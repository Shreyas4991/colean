import Mathlib

open Lean Meta Elab Deriving Command Lean.Parser.Term

/-!
# Derive handler for `Dist`

This file registers a `deriving` handler for the `Dist` typeclass so that
inductive types automatically receive a canonical ultrametric.
The implementation follows the same structure as `Lean.Elab.Deriving.Ord`
(`Lean/Elab/Deriving/Ord.lean`), which also generates a two-argument `match`
over an inductive type.

## The generated metric

For an inductive type `T`, `deriving instance Dist for T` produces a
`noncomputable` function `dist : T → T → ℝ` defined by:

| Pattern | Value |
|---------|-------|
| Same 0-ary constructor | `0` |
| Same constructor, all non-recursive fields equal, recursive fields `aᵢ bᵢ` | `2⁻¹ * (dist a₁ b₁ ⊔ dist a₂ b₂ ⊔ …)` |
| Same constructor, some non-recursive field differs | `1` |
| Different constructors | `1` |

This is the **Baire / profinite ultrametric**: two values are close iff they
agree on a deep common prefix of their tree structure.

### Examples

```
-- List α  (needs [DecidableEq α])
dist [] []             = 0
dist (x::xs) (y::ys)   = if x = y then 2⁻¹ * dist xs ys else 1
dist _ _               = 1

-- BinTree
dist .leaf .leaf                 = 0
dist (.node l₁ r₁) (.node l₂ r₂) = 2⁻¹ * (dist l₁ l₂ ⊔ dist r₁ r₂)
dist _ _                         = 1
```

## Generated instance signature

Non-recursive fields are compared with `=`, so `[DecidableEq α]` is required
for each type parameter `α` that appears in such a field.
Recursive fields are only compared via the metric itself; no `[Dist α]`
constraint on element types is needed or generated.

The resulting instance is `noncomputable` because `ℝ` arithmetic is.

## Implementation notes

- `matchAltExpr` (from `Lean.Parser.Term`) must be in scope for match-alternative
  quasiquotes; bare `matchAlt` is not quotable in user-space Lean 4.
- `mkImplicitBinders` returns `Array (TSyntax ``implicitBinder)` and
  `mkInstImplicitBinders` returns `Array Syntax`; both are cast to
  `bracketedBinder` via `.map (·.raw |> TSyntax.mk)` / `.map TSyntax.mk`.
- `Context` is aliased as `DCtx` to avoid ambiguity with `Meta.Context` and
  `Command.Context` introduced by the `open` chain.
- For indexed types the match includes the indices as leading discriminants so that
  Lean can refine constructor availability via dependent pattern matching.
- Cross-constructor cases emit **one alt per coexisting ordered pair** `(cᵢ, cⱼ)`
  (checked via `constructorsCanCoexist`) rather than a wildcard catch-all.
  This avoids redundant-alt errors for indexed types where some constructor pairs
  can never share an index (e.g. `IntVector.nil : IntVector 0` vs
  `IntVector.cons : IntVector (n+1)`).  No `set_option match.ignoreUnusedAlts` or
  `pop.pop` bookkeeping is needed.
- Fields whose free variable appears in the constructor's result type are index
  positions forced equal by dependent typing; the right-hand pattern uses
  `.(a)` (inaccessible) instead of a fresh binding — the same guard Ord uses
  via `occursOrInType`.
-/

namespace MetricCorec.Deriving.Dist

-- Disambiguate: the `Context` we want is the Deriving one.
private abbrev DCtx := Lean.Elab.Deriving.Context

/-- Return `true` iff constructors `c1` and `c2` can produce values of the *same*
    type instance, i.e. their result types are unifiable.  Used to decide whether
    cross-constructor match alternatives are needed for indexed inductives.

    Example: `IntVector.nil : IntVector 0` and `IntVector.cons : IntVector (n+1)`
    are NOT unifiable (0 ≠ n+1), so no cross-ctor alt is needed there.
    But `StrangeVector.nil : StrangeVector 0` and
    `StrangeVector.cons : StrangeVector n` ARE unifiable (n := 0). -/
private def constructorsCanCoexist (c1Name c2Name : Name) : MetaM Bool :=
  withoutModifyingState do
    let c1 ← getConstInfoCtor c1Name
    let c2 ← getConstInfoCtor c2Name
    let (_, _, type1) ← forallMetaTelescopeReducing c1.type
    let (_, _, type2) ← forallMetaTelescopeReducing c2.type
    isDefEq type1 type2

/-- Find the aux-function identifier for a field type in the mutual group. -/
private def auxFnForType (ctx : DCtx) (type : Expr) : Option Ident :=
  (ctx.typeInfos.findIdx? fun info => type.isAppOf info.name).map
    fun i => mkIdent ctx.auxFunNames[i]!

/-- Build the RHS for one same-constructor match arm.
    `recCalls`    : pre-built `dist a b` terms for recursive fields.
    `nonRecPairs` : `(a, b)` idents for non-recursive (equality-checked) fields. -/
private def buildDistRhs
    (recCalls    : Array Term)
    (nonRecPairs : Array (Ident × Ident)) : TermElabM Term := do
  let base : Term ← match recCalls.toList with
    | []        => `((0 : ℝ))
    | t :: rest =>
      let sup ← rest.foldlM (fun acc r => `($acc ⊔ $r)) t
      `((2 : ℝ)⁻¹ * $sup)
  match nonRecPairs.toList with
  | []           => return base
  | (a₀, b₀) :: rest =>
    let cond ← rest.foldlM
      (fun acc (a, b) => `($acc ∧ $a = $b))
      (← `($a₀ = $b₀))
    `(if $cond then $base else (1 : ℝ))

/-- Build `match idx…, x₁, x₂ with …` for one inductive in the mutual group.
    Index names (beyond numParams in `argNames`) are added as leading discriminants
    so that Lean can refine types via dependent pattern matching.

    Two strategies are used depending on whether the type is indexed:

    Structure of the generated match:

    1. **Same-constructor alt** for every constructor `c`:
       `| idx…, @c lhs_fields…, @c rhs_fields… => dist_formula`
       Fields that appear in the result type (index positions) use an inaccessible
       `.(a)` pattern on the right side (same guard as Ord's `occursOrInType`).

    2. **Cross-constructor alt** for every *ordered* pair `(c_i, c_j)` with `i ≠ j`
       for which `constructorsCanCoexist c_i c_j` holds (i.e. their result types can
       unify).  Both sides are fully wildcarded:
       `| idx…, @c_i _…, @c_j _… => 1`

       Using explicit constructor pairs rather than a wildcard catch-all means:
       - impossible cross-ctor combinations (different indices) are never listed →
         no redundant-alt errors.
       - no `set_option match.ignoreUnusedAlts` needed.
       - no pop.pop bookkeeping needed.

    Requires `open Lean.Parser.Term` for `matchAltExpr`. -/
private def mkDistMatch
    (ctx      : DCtx)
    (argNames : Array Name)   -- all param+index names from mkInductArgNames
    (x1 x2   : Name)
    (indVal   : InductiveVal) : TermElabM Term := do
  let numIndices := argNames.size - indVal.numParams
  let ctors := indVal.ctors.toArray
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]

  -- Helper: produce `_` patterns for the index positions
  let idxPats : TermElabM (Array Term) :=
    (Array.range numIndices).mapM fun _ => `(term| _)

  -- Helper: fully-wildcarded pattern for a constructor (for cross-ctor alts)
  let mkWildCtor (ctorName : Name) : TermElabM Term := do
    let info ← getConstInfoCtor ctorName
    let n    := indVal.numParams + info.numFields
    let ws   : Array Term ← (Array.range n).mapM fun _ => `(term| _)
    `(@$(mkIdent ctorName) $ws:term*)

  -- 1. Same-constructor alts
  for ctorName in ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let sameAlt ← forallTelescopeReducing ctorInfo.type fun xs resultType => do
      let resultType ← Core.betaReduce resultType
      let mut lhsArgs  : Array Term            := #[]
      let mut rhsArgs  : Array Term            := #[]
      let mut recCalls : Array Term            := #[]
      let mut nonRecs  : Array (Ident × Ident) := #[]
      for _ in [:indVal.numParams] do
        lhsArgs := lhsArgs.push (← `(_))
        rhsArgs := rhsArgs.push (← `(_))
      for i in [:ctorInfo.numFields] do
        let x    := xs[indVal.numParams + i]!
        let decl ← x.fvarId!.getDecl
        let a    := mkIdent (← mkFreshUserName `a)
        -- Index position: right side is forced equal to left by the type,
        -- so use an inaccessible pattern `.(a)` (mirrors Ord's occursOrInType guard).
        if resultType.containsFVar x.fvarId! then
          lhsArgs := lhsArgs.push a
          rhsArgs := rhsArgs.push (← `(term| .($a:ident)))
        else
          let b := mkIdent (← mkFreshUserName `b)
          lhsArgs := lhsArgs.push a
          rhsArgs := rhsArgs.push b
          match auxFnForType ctx decl.type with
          | some fn => recCalls := recCalls.push (← `($fn $a $b))
          | none    => nonRecs  := nonRecs.push (a, b)
      let lPat ← `(@$(mkIdent ctorName) $lhsArgs:term*)
      let rPat ← `(@$(mkIdent ctorName) $rhsArgs:term*)
      let rhs  ← buildDistRhs recCalls nonRecs
      let ip   ← idxPats
      let pats := ip ++ #[lPat, rPat]
      `(matchAltExpr| | $[$(pats):term],* => $rhs:term)
    alts := alts.push sameAlt

  -- 2. Cross-constructor alts: one per coexisting *ordered* pair (i, j), i ≠ j.
  --    Only pairs whose result types unify are listed; impossible pairs (different
  --    index levels) are silently skipped, preventing redundant-alt errors.
  for i in [:ctors.size] do
    for j in [:ctors.size] do
      if i != j && (← constructorsCanCoexist ctors[i]! ctors[j]!) then
        let w1   ← mkWildCtor ctors[i]!
        let w2   ← mkWildCtor ctors[j]!
        let ip   ← idxPats
        let pats := ip ++ #[w1, w2]
        alts := alts.push (← `(matchAltExpr| | $[$(pats):term],* => (1 : ℝ)))

  -- Discriminants: indices first, then x1 x2
  let idxDiscrs ← (Array.range numIndices).mapM fun i => mkDiscr argNames[indVal.numParams + i]!
  let valDiscrs ← #[x1, x2].mapM mkDiscr
  let discrs     := idxDiscrs ++ valDiscrs
  `(match $[$discrs],* with $alts:matchAlt*)

/-- Generate one `noncomputable def` for the auxiliary distance function. -/
def mkDistAuxFunction (ctx : DCtx) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal     := ctx.typeInfos[i]!
  let argNames   ← mkInductArgNames indVal
  let implBndrs  ← mkImplicitBinders argNames
  let decEqBndrs ← mkInstImplicitBinders ``DecidableEq indVal argNames
  let targetType ← mkInductiveApp indVal argNames
  let x1 ← mkFreshUserName `x
  let x2 ← mkFreshUserName `x
  let body ← mkDistMatch ctx argNames x1 x2 indVal
  `(command| noncomputable def $(mkIdent auxFunName):ident
      $(implBndrs.map (·.raw |> TSyntax.mk)):bracketedBinder*
      $(decEqBndrs.map TSyntax.mk):bracketedBinder*
      ($(mkIdent x1) : $targetType) ($(mkIdent x2) : $targetType)
      : ℝ := $body)

/-- Wrap all aux functions in `mutual … end`. -/
def mkDistMutualBlock (ctx : DCtx) : TermElabM Command := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkDistAuxFunction ctx i)
  `(mutual $auxDefs:command* end)

/-- Generate `noncomputable instance : Dist T` using the aux function. -/
def mkDistInstanceCmd (ctx : DCtx) (declName : Name) : TermElabM Command := do
  let i          := ctx.typeInfos.findIdx? (·.name == declName) |>.getD 0
  let indVal     := ctx.typeInfos[i]!
  let auxFunName := ctx.auxFunNames[i]!
  let argNames   ← mkInductArgNames indVal
  let implBndrs  ← mkImplicitBinders argNames
  let decEqBndrs ← mkInstImplicitBinders ``DecidableEq indVal argNames
  let indType    ← mkInductiveApp indVal argNames
  `(command| noncomputable instance $(mkIdent ctx.instName):ident
      $(implBndrs.map (·.raw |> TSyntax.mk)):bracketedBinder*
      $(decEqBndrs.map TSyntax.mk):bracketedBinder*
      : Dist $indType := ⟨$(mkIdent auxFunName)⟩)

private def mkDistInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext ``Dist "dist" declName
  return #[← mkDistMutualBlock ctx, ← mkDistInstanceCmd ctx declName]

def mkDistInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    for declName in declNames do
      let cmds ← liftTermElabM <| mkDistInstance declName
      cmds.forM elabCommand
    return true
  else
    return false

initialize
  registerDerivingHandler ``Dist mkDistInstanceHandler

end MetricCorec.Deriving.Dist
