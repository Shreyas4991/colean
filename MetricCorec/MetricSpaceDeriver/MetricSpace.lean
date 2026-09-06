import Mathlib

open Lean Meta Elab Deriving Command Lean.Parser.Term

/-!
# Derive handler for `MetricSpace`

Generates a Baire-style ultrametric on any non-mutual, non-indexed inductive type with
`DecidableEq` on its non-recursive fields. For each derived type `T` the handler adds:

| Declaration | Type |
|-------------|------|
| `T.dist` | `T → T → ℝ` (the Baire ultrametric) |
| `T.dist_self` | `∀ x, T.dist x x = 0` |
| `T.dist_comm` | `∀ x y, T.dist x y = T.dist y x` |
| `T.dist_nonneg` | `∀ x y, 0 ≤ T.dist x y` |
| `T.dist_le_one` | `∀ x y, T.dist x y ≤ 1` |
| `T.dist_ultra` | `∀ x y z, T.dist x z ≤ T.dist x y ⊔ T.dist y z` |
| `T.eq_of_dist_eq_zero` | `∀ {x y}, T.dist x y = 0 → x = y` |

A `MetricSpace T` and `BoundedSpace T` instance are then assembled from these lemmas.
`dist_triangle` is derived from `dist_ultra` via `max_le_add_of_nonneg`.

## Distance definition

For constructors with only recursive fields (e.g. `BinTree`):
  `dist (ctor a₁ … aₙ) (ctor b₁ … bₙ) = 2⁻¹ * (dist a₁ b₁ ⊔ … ⊔ dist aₙ bₙ)`

For constructors with non-recursive fields (e.g. `List.cons`):
  `dist (ctor h₁ t₁) (ctor h₂ t₂) = if h₁ = h₂ then 2⁻¹ * dist t₁ t₂ else 1`

Differing constructors always have distance 1.

## Limitations

- Mutual inductive types are rejected (fun_induction unavailable; `sorry` would be needed).
- Indexed inductive families are rejected (constructor result types diverge).
-/

namespace MetricCorec.Deriving.MetricSpace

private abbrev DCtx := Lean.Elab.Deriving.Context

-- ═══════════════════════════════════════════════════════════════════
-- §1  Dist generation  (verbatim copy from Dist.lean so this file is
--     self-contained and we retain full control over naming)
-- ═══════════════════════════════════════════════════════════════════

private def constructorsCanCoexist (c1Name c2Name : Name) : MetaM Bool :=
  withoutModifyingState do
    let c1 ← getConstInfoCtor c1Name
    let c2 ← getConstInfoCtor c2Name
    let (_, _, type1) ← forallMetaTelescopeReducing c1.type
    let (_, _, type2) ← forallMetaTelescopeReducing c2.type
    isDefEq type1 type2

private def auxFnForType (ctx : DCtx) (type : Expr) : Option Ident :=
  (ctx.typeInfos.findIdx? fun info => type.isAppOf info.name).map
    fun i => mkIdent ctx.auxFunNames[i]!

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

private def mkDistMatch
    (ctx      : DCtx)
    (argNames : Array Name)
    (x1 x2   : Name)
    (indVal   : InductiveVal) : TermElabM Term := do
  let numIndices := argNames.size - indVal.numParams
  let ctors := indVal.ctors.toArray
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let idxPats : TermElabM (Array Term) :=
    (Array.range numIndices).mapM fun _ => `(term| _)
  let mkWildCtor (ctorName : Name) : TermElabM Term := do
    let info ← getConstInfoCtor ctorName
    let n    := indVal.numParams + info.numFields
    let ws   : Array Term ← (Array.range n).mapM fun _ => `(term| _)
    `(@$(mkIdent ctorName) $ws:term*)
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
  for i in [:ctors.size] do
    for j in [:ctors.size] do
      if i != j && (← constructorsCanCoexist ctors[i]! ctors[j]!) then
        let w1   ← mkWildCtor ctors[i]!
        let w2   ← mkWildCtor ctors[j]!
        let ip   ← idxPats
        let pats := ip ++ #[w1, w2]
        alts := alts.push (← `(matchAltExpr| | $[$(pats):term],* => (1 : ℝ)))
  let idxDiscrs ← (Array.range numIndices).mapM fun i => mkDiscr argNames[indVal.numParams + i]!
  let valDiscrs ← #[x1, x2].mapM mkDiscr
  let discrs     := idxDiscrs ++ valDiscrs
  `(match $[$discrs],* with $alts:matchAlt*)

private def mkDistAuxFunction (ctx : DCtx) (i : Nat) : TermElabM Command := do
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

private def mkDistMutualBlock (ctx : DCtx) : TermElabM Command := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkDistAuxFunction ctx i)
  `(mutual $auxDefs:command* end)

private def mkDistInstanceCmd (ctx : DCtx) (declName : Name) : TermElabM Command := do
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

-- ═══════════════════════════════════════════════════════════════════
-- §2  Named lemma generation
--     One theorem per type in the mutual group.
-- ═══════════════════════════════════════════════════════════════════

/-- `T.dist_self : ∀ x, T.dist x x = 0` for every type in the group.
    Proof: `induction x <;> simp_all [distFns...]`
    Only called for simple (non-mutual, non-indexed) types; the handler rejects others. -/
private def mkDistSelfCmds (ctx : DCtx) : TermElabM (Array Command) := do
  let allDistFns : Array Term ← ctx.auxFunNames.mapM fun n => `($(mkIdent n))
  let mut thms : Array Command := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal     := ctx.typeInfos[i]!
    let distFun    := ctx.auxFunNames[i]!
    let argNames   ← mkInductArgNames indVal
    let implBndrs  ← mkImplicitBinders argNames
    let decEqBndrs ← mkInstImplicitBinders ``DecidableEq indVal argNames
    let indType    ← mkInductiveApp indVal argNames
    let thmName    := indVal.name ++ `dist_self
    thms := thms.push (← `(command| theorem $(mkIdent thmName):ident
        $(implBndrs.map (·.raw |> TSyntax.mk)):bracketedBinder*
        $(decEqBndrs.map TSyntax.mk):bracketedBinder*
        (x : $indType) : $(mkIdent distFun) x x = 0 := by
          induction x <;> simp_all [$[$allDistFns:term],*]))
  if thms.size == 1 then return thms
  return #[← `(mutual $thms:command* end)]

/-- `T.dist_comm : ∀ x y, T.dist x y = T.dist y x` for every type in the group.
    Proof: `induction x generalizing y <;> cases y <;> simp_all [distFns..., eq_comm]`
    Only called for simple (non-mutual, non-indexed) types; the handler rejects others. -/
private def mkDistCommCmds (ctx : DCtx) : TermElabM (Array Command) := do
  let allDistFns : Array Term ← ctx.auxFunNames.mapM fun n => `($(mkIdent n))
  let mut thms : Array Command := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal     := ctx.typeInfos[i]!
    let distFun    := ctx.auxFunNames[i]!
    let argNames   ← mkInductArgNames indVal
    let implBndrs  ← mkImplicitBinders argNames
    let decEqBndrs ← mkInstImplicitBinders ``DecidableEq indVal argNames
    let indType    ← mkInductiveApp indVal argNames
    let thmName    := indVal.name ++ `dist_comm
    thms := thms.push (← `(command| theorem $(mkIdent thmName):ident
        $(implBndrs.map (·.raw |> TSyntax.mk)):bracketedBinder*
        $(decEqBndrs.map TSyntax.mk):bracketedBinder*
        (x y : $indType) : $(mkIdent distFun) x y = $(mkIdent distFun) y x := by
          induction x generalizing y <;> cases y <;>
            simp_all [$[$allDistFns:term],*, eq_comm]))
  if thms.size == 1 then return thms
  return #[← `(mutual $thms:command* end)]

/-- `T.dist_nonneg : ∀ x y, 0 ≤ T.dist x y` for every type in the group.
    Proof: `fun_induction distFun x y <;> grind`
    Only called for simple (non-mutual, non-indexed) types; the handler rejects others. -/
private def mkDistNonnegCmds (ctx : DCtx) : TermElabM (Array Command) :=
  ctx.typeInfos.mapIdxM fun i indVal => do
    let distFun    := ctx.auxFunNames[i]!
    let argNames   ← mkInductArgNames indVal
    let implBndrs  ← mkImplicitBinders argNames
    let decEqBndrs ← mkInstImplicitBinders ``DecidableEq indVal argNames
    let indType    ← mkInductiveApp indVal argNames
    let thmName    := indVal.name ++ `dist_nonneg
    `(command| theorem $(mkIdent thmName):ident
        $(implBndrs.map (·.raw |> TSyntax.mk)):bracketedBinder*
        $(decEqBndrs.map TSyntax.mk):bracketedBinder*
        (x y : $indType) : (0 : ℝ) ≤ $(mkIdent distFun) x y := by
          fun_induction $(mkIdent distFun) x y <;> grind)

/-- `T.dist_le_one : ∀ x y, T.dist x y ≤ 1` for every type in the group.
    Proof: `fun_induction distFun x y <;> grind` — follows the match cases of the dist def. -/
private def mkDistLeOneCmds (ctx : DCtx) : TermElabM (Array Command) :=
  ctx.typeInfos.mapIdxM fun i indVal => do
    let distFun    := ctx.auxFunNames[i]!
    let argNames   ← mkInductArgNames indVal
    let implBndrs  ← mkImplicitBinders argNames
    let decEqBndrs ← mkInstImplicitBinders ``DecidableEq indVal argNames
    let indType    ← mkInductiveApp indVal argNames
    let thmName    := indVal.name ++ `dist_le_one
    let proof : TSyntax `tactic ←
      if ctx.typeInfos.size > 1 then `(tactic| sorry)
      else `(tactic| fun_induction $(mkIdent distFun) x y <;> grind)
    `(command| theorem $(mkIdent thmName):ident
        $(implBndrs.map (·.raw |> TSyntax.mk)):bracketedBinder*
        $(decEqBndrs.map TSyntax.mk):bracketedBinder*
        (x y : $indType) : $(mkIdent distFun) x y ≤ 1 := by
          $(proof):tactic)

-- ═══════════════════════════════════════════════════════════════════
-- §3  dist_ultra  (ultrametric triangle inequality)
-- ═══════════════════════════════════════════════════════════════════

/-- Key lemma: halving distributes over sup in the right way for ultrametric proofs. -/
lemma half_sup_le_sup_halves (x y z : ℝ) :
    2⁻¹ * x ≤ (2⁻¹ * y) ⊔ (2⁻¹ * z) ↔ x ≤ y ⊔ z := by simp

/-- `T.dist_ultra x y z : T.dist x z ≤ T.dist x y ⊔ T.dist y z`
    Exhaustive match over all n³ constructor triples.
    Cross-constructor arms: dist of differing ctors is 1, so le_max_{left,right} closes it.
    Same-constructor arms: split on non-recursive field equality, then recurse. -/
private def mkDistUltraCmds (ctx : DCtx) : TermElabM (Array Command) :=
  ctx.typeInfos.mapIdxM fun i indVal => do
    let distFun    := ctx.auxFunNames[i]!
    let argNames   ← mkInductArgNames indVal
    let implBndrs  ← mkImplicitBinders argNames
    let decEqBndrs ← mkInstImplicitBinders ``DecidableEq indVal argNames
    let indType    ← mkInductiveApp indVal argNames
    let thmName    := indVal.name ++ `dist_ultra
    let distLeOne  := mkIdent (indVal.name ++ `dist_le_one)
    let distNonneg := mkIdent (indVal.name ++ `dist_nonneg)
    let halfSup    := mkIdent ``MetricCorec.Deriving.MetricSpace.half_sup_le_sup_halves
    let ctors      := indVal.ctors.toArray

    -- Build @CtorName _... f1 f2 ... pattern; return (pat, [(name, isRecursive)])
    let mkCtorPat (ctorName : Name) (pre : String)
        : TermElabM (Term × Array (Name × Bool)) := do
      let ctorInfo ← getConstInfoCtor ctorName
      let fieldInfos ← forallTelescopeReducing ctorInfo.type fun xs resultType => do
        let resultType ← Core.betaReduce resultType
        (Array.range ctorInfo.numFields).mapM fun j => do
          let x := xs[indVal.numParams + j]!
          let decl ← x.fvarId!.getDecl
          let fname ← mkFreshUserName (Name.mkSimple (pre ++ toString (j + 1)))
          -- A field is recursive if its type is indexed (appears in the result type)
          -- OR if its type is one of the types being derived (regular structural recursion).
          let isRec := resultType.containsFVar x.fvarId! || (auxFnForType ctx decl.type).isSome
          return (fname, isRec)
      let mut args : Array Term := #[]
      for _ in [:indVal.numParams] do
        args := args.push (← `(term| _))
      for (fname, _) in fieldInfos do
        args := args.push (mkIdent fname)
      return (← `(@$(mkIdent ctorName) $args:term*), fieldInfos)

    -- Build conjunction a1 = b1 ∧ a2 = b2 ∧ ... from pairs
    let mkCond (pairs : Array (Name × Name)) : TermElabM Term := do
      match pairs.toList with
      | []              => `(True)
      | [(a, b)]        => `($(mkIdent a) = $(mkIdent b))
      | (a₀, b₀) :: rest =>
        rest.foldlM (fun acc (a, b) => `($acc ∧ $(mkIdent a) = $(mkIdent b)))
                    (← `($(mkIdent a₀) = $(mkIdent b₀)))

    let x1 ← mkFreshUserName `p1
    let x2 ← mkFreshUserName `p2
    let x3 ← mkFreshUserName `p3

    let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for c1Name in ctors do
      for c2Name in ctors do
        for c3Name in ctors do
          let (pat1, fi1) ← mkCtorPat c1Name "a"
          let (pat2, fi2) ← mkCtorPat c2Name "b"
          let (pat3, fi3) ← mkCtorPat c3Name "c"
          let pats := #[pat1, pat2, pat3]
          let rhs : Term ←
            if c1Name ≠ c2Name then
              -- dist p1 p2 = 1 definitionally, so max ≥ 1 ≥ dist p1 p3
              `(($distLeOne _ _).trans (le_max_left _ _))
            else if c2Name ≠ c3Name then
              -- dist p2 p3 = 1 definitionally
              `(($distLeOne _ _).trans (le_max_right _ _))
            else do
              -- Same constructor c1 = c2 = c3.
              -- Separate non-recursive fields (need if-splitting) from recursive ones.
              let mut nrPairs12 : Array (Name × Name) := #[]
              let mut nrPairs23 : Array (Name × Name) := #[]
              let mut recTriples : Array (Name × Name × Name) := #[]
              for j in [:fi1.size] do
                let (a, isRec) := fi1[j]!
                let (b, _)     := fi2[j]!
                let (c, _)     := fi3[j]!
                if isRec then
                  recTriples := recTriples.push (a, b, c)
                else
                  nrPairs12 := nrPairs12.push (a, b)
                  nrPairs23 := nrPairs23.push (b, c)
              -- Recursive calls for `order`
              let orderArgs ← recTriples.mapM fun (ra, rb, rc) =>
                `($(mkIdent thmName) $(mkIdent ra) $(mkIdent rb) $(mkIdent rc))
              let distFunT : Term ← `($(mkIdent distFun))
              let halfSupT : Term ← `($halfSup)
              if nrPairs12.isEmpty then
                if recTriples.isEmpty then
                  -- No fields at all: dist = 0
                  `(($distNonneg _ _).trans (le_max_left _ _))
                else
                  -- Only recursive fields: no if-then-else in dist
                  let simpArgs : Array Term := #[distFunT, halfSupT]
                  `(by simp only [$[$simpArgs:term],*]
                       order [$[$orderArgs:term],*])
              else
                -- Has non-recursive fields: split on whether they match.
                -- `if h12 : ¬ P` binds h12 : ¬ P in then-branch, h12 : ¬¬ P in else-branch.
                -- `of_not_not h12` extracts the equalities for simp to use.
                let h12Name ← mkFreshUserName `h12
                let h23Name ← mkFreshUserName `h23
                -- Use plain ident for `if h : P` syntax; the macro `if $h:ident : P` requires ident.
                let h12I := mkIdent h12Name
                let h23I := mkIdent h23Name
                let h12T : Term ← `($h12I)
                let h23T : Term ← `($h23I)
                let ofNN12T : Term ← `(of_not_not $(mkIdent h12Name))
                let ofNN23T : Term ← `(of_not_not $(mkIdent h23Name))
                let cond12 ← mkCond nrPairs12
                let cond23 ← mkCond nrPairs23
                let simp12  : Array Term := #[distFunT, h12T]
                let simp23  : Array Term := #[distFunT, h23T]
                let simpElse  : Array Term := #[distFunT, ofNN12T, ofNN23T]
                let simpElseH : Array Term := #[distFunT, ofNN12T, ofNN23T, halfSupT]
                let elseElse : Term ←
                  if recTriples.isEmpty then
                    `(by simp only [$[$simpElse:term],*, ↓reduceIte])
                  else
                    `(by simp only [$[$simpElseH:term],*, ↓reduceIte]
                         order [$[$orderArgs:term],*])
                `(if $h12I:ident : ¬ $cond12 then
                    ($distLeOne _ _).trans
                      (le_max_of_le_left (by simp only [$[$simp12:term],*, ↓reduceIte, le_refl]))
                  else if $h23I:ident : ¬ $cond23 then
                    ($distLeOne _ _).trans
                      (le_max_of_le_right (by simp only [$[$simp23:term],*, ↓reduceIte, le_refl]))
                  else $elseElse)
          alts := alts.push (← `(matchAltExpr| | $[$(pats):term],* => $rhs))
    let discrs ← #[x1, x2, x3].mapM mkDiscr
    let body ← `(match $[$discrs],* with $alts:matchAlt*)
    `(command| theorem $(mkIdent thmName):ident
        $(implBndrs.map (·.raw |> TSyntax.mk)):bracketedBinder*
        $(decEqBndrs.map TSyntax.mk):bracketedBinder*
        ($(mkIdent x1) $(mkIdent x2) $(mkIdent x3) : $indType) :
        $(mkIdent distFun) $(mkIdent x1) $(mkIdent x3) ≤
          $(mkIdent distFun) $(mkIdent x1) $(mkIdent x2) ⊔
          $(mkIdent distFun) $(mkIdent x2) $(mkIdent x3) := $body)

-- ═══════════════════════════════════════════════════════════════════
-- §5  MetricSpace instance
-- ═══════════════════════════════════════════════════════════════════

/-- `T.eq_of_dist_eq_zero : ∀ {x y : T}, T.dist x y = 0 → x = y` for every type in the group.
    Proof strategy mirrors BinTree.lean:
      `have := @dist_nonneg; fun_induction dist x y <;> grind`
    `@dist_nonneg` gives the universal nonneg fact without triggering implicit-arg inference.
    Mutual types use `sorry` (fun_induction is unavailable for mutual recursion). -/
private def mkDistEqOfDistEqZeroCmds (ctx : DCtx) : TermElabM (Array Command) :=
  ctx.typeInfos.mapIdxM fun i indVal => do
    let distFun    := ctx.auxFunNames[i]!
    let distNonneg := mkIdent (indVal.name ++ `dist_nonneg)
    let argNames   ← mkInductArgNames indVal
    let implBndrs  ← mkImplicitBinders argNames
    let decEqBndrs ← mkInstImplicitBinders ``DecidableEq indVal argNames
    let indType    ← mkInductiveApp indVal argNames
    let thmName    := indVal.name ++ `eq_of_dist_eq_zero
    if ctx.typeInfos.size > 1 then
      `(command| theorem $(mkIdent thmName):ident
          $(implBndrs.map (·.raw |> TSyntax.mk)):bracketedBinder*
          $(decEqBndrs.map TSyntax.mk):bracketedBinder*
          {x y : $indType} (_ : $(mkIdent distFun) x y = 0) : x = y := by sorry)
    else
      `(command| theorem $(mkIdent thmName):ident
          $(implBndrs.map (·.raw |> TSyntax.mk)):bracketedBinder*
          $(decEqBndrs.map TSyntax.mk):bracketedBinder*
          {x y : $indType} (_ : $(mkIdent distFun) x y = 0) : x = y := by
            have : ∀ (a b : $indType), (0 : ℝ) ≤ $(mkIdent distFun) a b := $distNonneg
            fun_induction $(mkIdent distFun) x y <;> grind)

/-- Generate the `MetricSpace T` instance using all named lemmas. -/
private def mkMetricSpaceInstanceCmd (ctx : DCtx) (declName : Name) : TermElabM Command := do
  let i          := ctx.typeInfos.findIdx? (·.name == declName) |>.getD 0
  let indVal     := ctx.typeInfos[i]!
  let distFun    := ctx.auxFunNames[i]!
  let distSelf   := mkIdent (indVal.name ++ `dist_self)
  let distComm   := mkIdent (indVal.name ++ `dist_comm)
  let distUltra  := mkIdent (indVal.name ++ `dist_ultra)
  let distNonneg := mkIdent (indVal.name ++ `dist_nonneg)
  let eqOfDist   := mkIdent (indVal.name ++ `eq_of_dist_eq_zero)
  let argNames   ← mkInductArgNames indVal
  let implBndrs  ← mkImplicitBinders argNames
  let decEqBndrs ← mkInstImplicitBinders ``DecidableEq indVal argNames
  let indType    ← mkInductiveApp indVal argNames
  `(command| noncomputable instance
      $(implBndrs.map (·.raw |> TSyntax.mk)):bracketedBinder*
      $(decEqBndrs.map TSyntax.mk):bracketedBinder*
      : MetricSpace $indType where
        dist               := $(mkIdent distFun)
        dist_self          := $distSelf
        dist_comm          := $distComm
        dist_triangle x y z :=
          ($distUltra x y z).trans (max_le_add_of_nonneg ($distNonneg x y) ($distNonneg y z))
        eq_of_dist_eq_zero := $eqOfDist)

/-- `BoundedSpace T` instance via `Metric.boundedSpace_iff`: the bound is 1 by `dist_le_one`. -/
private def mkBoundedSpaceInstanceCmd (ctx : DCtx) (declName : Name) : TermElabM Command := do
  let i          := ctx.typeInfos.findIdx? (·.name == declName) |>.getD 0
  let indVal     := ctx.typeInfos[i]!
  let distLeOne  := mkIdent (indVal.name ++ `dist_le_one)
  let argNames   ← mkInductArgNames indVal
  let implBndrs  ← mkImplicitBinders argNames
  let decEqBndrs ← mkInstImplicitBinders ``DecidableEq indVal argNames
  let indType    ← mkInductiveApp indVal argNames
  `(command| noncomputable instance
      $(implBndrs.map (·.raw |> TSyntax.mk)):bracketedBinder*
      $(decEqBndrs.map TSyntax.mk):bracketedBinder*
      : BoundedSpace $indType :=
        Metric.boundedSpace_iff.mpr ⟨1, $distLeOne⟩)

-- ═══════════════════════════════════════════════════════════════════
-- §6  Handler
-- ═══════════════════════════════════════════════════════════════════

def mkMetricSpaceInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    -- Early rejection: logError (not throwError) so the message reaches the user.
    -- throwError inside a deriving handler is caught/swallowed by the deriving machinery.
    let indVal ← liftCoreM <| getConstInfoInduct declNames[0]!
    -- Reject mutual groups (indVal.all contains the full mutual group).
    if indVal.all.length > 1 then
      logError "MetricSpace deriving: mutual inductive types are not supported"
      return false
    -- Reject indexed families.
    if indVal.numIndices > 0 then
      logError "MetricSpace deriving: indexed inductive families are not supported"
      return false
    -- Build ONE context for the whole group. Iterating `for declName in declNames` and calling
    -- `mkContext` per element would produce `_1`-suffixed aux names on the 2nd+ calls.
    let cmds ← liftTermElabM do
      let ctx           ← mkContext ``Dist "dist" declNames[0]!
      let distMutual    := ← mkDistMutualBlock ctx
      let distInstCmds  ← declNames.mapM (mkDistInstanceCmd ctx)
      let selfCmds      ← mkDistSelfCmds ctx
      let commCmds      ← mkDistCommCmds ctx
      let nonnegCmds    ← mkDistNonnegCmds ctx
      let leOneCmds     ← mkDistLeOneCmds ctx
      let ultraCmds     ← mkDistUltraCmds ctx
      let eqOfDistCmds  ← mkDistEqOfDistEqZeroCmds ctx
      let msCmds        ← declNames.mapM (mkMetricSpaceInstanceCmd ctx)
      let bsCmds        ← declNames.mapM (mkBoundedSpaceInstanceCmd ctx)
      return #[distMutual] ++ distInstCmds ++ selfCmds ++ commCmds ++
             nonnegCmds ++ leOneCmds ++ ultraCmds ++ eqOfDistCmds ++ msCmds ++ bsCmds
    cmds.forM elabCommand
    return true
  else
    return false

initialize
  registerDerivingHandler ``MetricSpace mkMetricSpaceInstanceHandler

end MetricCorec.Deriving.MetricSpace
