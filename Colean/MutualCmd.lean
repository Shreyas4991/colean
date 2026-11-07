import Colean.DataCmd

/-!
# Mutual blocks

```
mutual
codata Tree (α : Type u)
  | node (a : α) (children : Forest α)
codata Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end
```

A `mutual … end` block whose declarations are all `codata`, or all `data`, with the same
parameters, is one family: the block `Tree_Forest` (the names joined by `_`) is declared as a
single family over the inductive `Tree_Forest.Ix`, which has a constructor per type, `Tree` and
`Forest`, whose arguments are the indices of that type, and every declaration of the single
type case is generated for the block (`Tree_Forest.F`, `Tree_Forest.corec`, `Tree_Forest.bisim`,
`Tree_Forest.rec`, …). This is how Lean itself elaborates mutual fixpoints, and the generic
theory needs nothing new. The types need not agree on their indices, since each has its own
constructor of `Ix`; written in a block, they must agree on their universe. Then, per type:
`Tree α := Tree_Forest α .Tree`, and `Even n := Even_Odd (.Even n)` with an index, its constructors
`Tree.node` with their lemmas under `Tree`, `Tree.casesOn` with only the constructors of `Tree`,
registered as the `cases` eliminator, and aliases `Tree.corec`, `Tree.bisim` (or `Tree.fold`)
restricting the block-level declarations to the type. Dot notation `t.dtor` resolves to
`Tree_Forest.dtor` through the definition of `Tree`, and the lemmas are stated with the
block-level `dtor` and `ctor`. Corecursion and induction take a state or motive over the whole
block:
`S : Tree_Forest.Ix α → Type _` and `c : ∀ i, S i → Tree_Forest.F α S i` for `corec`, and
`induction t using Tree_Forest.rec` for `data`, as with Lean's mutual inductives, whose
`induction` tactic does not apply to mutual types either.

Constructor names shared by several types of the block are qualified in the block-level
inductives (`Even_succ`, `Odd_succ` in `Even_Odd.F`); the per-type declarations keep the plain
names.

A `mutual` block mixing `data` and `codata` is rejected: such a block is a nested fixpoint and
the nesting order is a choice, made by the order of a `mixed_mutual` block.

## Mixed blocks: `mixed_mutual`

```
mixed_mutual
codata Tree (α : Type u)
  | node (a : α) (children : Forest α)
data Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end
```

A block with both kinds is a nested fixpoint, and a cyclic system has several nested solutions
(`Tree` outside `Forest` is the finitely branching infinite trees, `Forest` outside `Tree` the
finite trees), so the block says the order: *the textual order is the nesting order, the first
declaration outermost*. A *run* is a maximal sequence of adjacent declarations of the same kind
and is one uniform block; runs `R₁ ⊃ R₂ ⊃ … ⊃ Rₖ` are elaborated from the innermost out:

* the innermost run `Rₖ` is declared with one extra parameter for the run `Rₖ₋₁` it mentions,
  the family `X` (a type `X : Type u_<Rₖ₋₁>` when `Rₖ₋₁` is a single type without indices, a
  family `X : J → Type u_<Rₖ₋₁>` over its index, `Blk.Ix` for a block, otherwise), every
  occurrence of a type of `Rₖ₋₁` replaced by `X` (at its packed index) and every occurrence of
  a type of `Rₖ` applied to `X`;
* a run `Rᵢ` is declared likewise with a parameter for `Rᵢ₋₁`, and every occurrence of a type
  `E` of `Rᵢ₊₁` becomes `E params (Rᵢ params X)` (or `E params (fun p => Rᵢ params X p.1 p.2…)`),
  a nested occurrence through `E` in its family parameter;
* the outermost run has no extra parameter; its types are closed.

So the user sees the parameterised inner types (`Forest α X`, with `Forest.nil : Forest α X`
for any `X`, `Forest.fold`, `Forest.rec`) and the closed outer ones (`Tree.node : α → Forest α
(Tree α) → Tree α`, `Tree.corec`, `Tree.bisim` with `Occ.Rel`/`IOcc.Rel` on the forests): the uniform contracts, composed. The universe of a family parameter is a `universe`
variable declared in scope (a hole would be solved differently across the generated
declarations). All declarations of the block must have the same parameters.

Any number of runs is allowed, in any order. A declaration may mention any run inside its own:
an occurrence of a type of a run further inside is applied to the chain of families down to
the declaration's own run (`Trace α (Menu α (Proc α))`), a nested occurrence through the
composite of the declared structures (`Occ.comp`). For now a declaration may mention, among
the runs outside its own, only the adjacent one: a reference further outside needs a structure
in several parameters (plan, section 5, step 2). A `mixed_mutual` block with a single
kind is accepted with a warning suggesting `mutual`.

The nesting through inner runs needs `PolyIso` instances for them, in their family parameter.
These are not generated yet, and cannot be given by hand inside a block, so a block in which an
outer run mentions an inner one stops at that declaration with the error for a missing instance.
-/

open Lean Elab Command Lean.Parser.Term

namespace Codata

/-- `mixed_mutual … end`: a block of `codata` and `data` declarations, nested in the order
written, the first declaration outermost. -/
syntax (name := mixedMutualCmd) "mixed_mutual" (ppLine (codataCmd <|> dataCmd))+
  ppDedent(ppLine "end") : command

/-- One declaration of a block: whether it is `codata`, its name, parameters, sort and
constructors. -/
structure Decl where
  isCo : Bool
  T : Ident
  ps : Array (TSyntax ``bracketedBinder)
  sort : Option Term
  ctors : Array (TSyntax ``codataCtor)
  deriving Inhabited

private def readDecl (stx : Syntax) : CommandElabM Decl := do
  match stx with
  | `(codata $T:ident $ps:bracketedBinder* $[: $s]? $cs:codataCtor*) =>
    return { isCo := true, T, ps, sort := s, ctors := cs }
  | `(data $T:ident $ps:bracketedBinder* $[: $s]? $cs:codataCtor*) =>
    return { isCo := false, T, ps, sort := s, ctors := cs }
  | _ => throwUnsupportedSyntax

/-- Does the declaration `id` (relative to the current namespace) exist? -/
private def declExists (id : Ident) : CommandElabM Bool := do
  return (← getEnv).contains ((← getCurrNamespace) ++ id.getId)

/-- The block name of several declarations. -/
private def blockName (decls : Array Decl) : Ident :=
  mkIdent (Name.mkSimple ("_".intercalate (decls.map (·.T.getId.toString)).toList))

/-- The index of a block: a constructor per type, with the indices of that type as arguments. It
takes the parameters `ps`, on which the indices may depend. -/
private def genIx (Ix : Ident) (ps : Array (TSyntax ``bracketedBinder)) (decls : Array Decl) :
    CommandElabM Unit := do
  let pExp ← ps.mapM fun b => do
    let (ids, ty, _) ← readBinder b
    `(bracketedBinder| ($ids* : $ty))
  let ctors ← decls.mapM fun d => do
    let bs ← (← readIdx d.sort).mapM fun (x, ty) => `(bracketedBinder| ($x:ident : $ty))
    `(Parser.Command.ctor| | $(mkIdent (Name.mkSimple d.T.getId.getString!)):ident $bs:bracketedBinder*)
  elabCommand (← `(inductive $Ix:ident $pExp:bracketedBinder* where $[$ctors:ctor]*))

/-- Elaborate a uniform group (all `codata` or all `data`), as a single declaration or as a
block. The index of the block may have been declared already, on the first `nPs` parameters. -/
private def elabGroup (isCo : Bool) (decls : Array Decl) (nPs : Option Nat := none) :
    CommandElabM Unit := do
  let (T, ps) := (decls[0]!.T, decls[0]!.ps)
  let ctx ← if decls.size == 1 then
      mkCtx isCo T ps #[(T, decls[0]!.sort, decls[0]!.ctors)] none
    else do
      let blk := blockName decls
      let Ix := mkIdent (blk.getId ++ `Ix)
      unless ← declExists Ix do genIx Ix ps decls
      let nAll ← ps.foldlM (fun n b => do return n + (← readBinder b).1.size) 0
      mkCtx isCo blk ps (decls.map fun d => (d.T, d.sort, d.ctors)) (some (Ix, nPs.getD nAll))
  if isCo then codataPipeline ctx else dataPipeline ctx

/-- A substitution of the occurrences of some types: their names, and the replacement of an
occurrence of the `m`-th one at the index arguments `idx`. -/
abbrev Subst := Array Name × (Nat → Array Term → CommandElabM Term)

/-- Replace every occurrence `T params idx…` of a type of one of the substitutions in `stx` by
its replacement; replacements are not traversed again. -/
private partial def substOccs (params : Array Ident) (subs : Array Subst) (stx : Syntax) :
    CommandElabM Syntax := do
  for (tNames, f) in subs do
    if let some (m, idx) := recIdx tNames params ⟨stx⟩ then return (← f m idx).raw
  match stx with
  | .node info k args => return .node info k (← args.mapM (substOccs params subs))
  | _ => return stx

/-- The sort at the end of a declared sort `I₁ → … → Type u`. -/
private partial def resultSort : Term → CommandElabM Term
  | `($_:bracketedBinder → $cod) => resultSort cod
  | `($_ → $cod) => resultSort cod
  | t => pure t

/-- The checks shared by `mutual` and `mixed_mutual`: the same parameters everywhere, and, within
the declarations `decls` that form one uniform block, the same universe where it is written.
Indices may differ. -/
private def checkUniform (d₀ : Decl) (decls : Array Decl) (sameUniverse : Bool) :
    CommandElabM Unit := do
  for d in decls do
    unless d.ps.size == d₀.ps.size && (d.ps.zip d₀.ps).all (fun (a, b) => a.raw.structEq b.raw) do
      throwErrorAt d.T "the types of a mutual block must have the same parameters as `{d₀.T}`"
    if let (true, some a, some b) := (sameUniverse, d.sort, d₀.sort) then
      unless (← resultSort a).raw.structEq (← resultSort b).raw do
        throwErrorAt d.T "the types of a mutual block must be in the same universe as `{d₀.T}`"

/-! ### Runs of a `mixed_mutual` block -/

/-- A run: adjacent declarations of the same kind, one uniform block. -/
private structure Run where
  isCo : Bool
  decls : Array Decl
  deriving Inhabited

private def Run.names (r : Run) : Array Name := r.decls.map (·.T.getId)

/-- The block name of the run: the type itself for a single declaration. -/
private def Run.blk (r : Run) : Ident := if r.decls.size == 1 then r.decls[0]!.T else blockName r.decls

private def Run.Ix (r : Run) : Ident := mkIdent (r.blk.getId ++ `Ix)

/-- The runs of a block, in order. -/
private def runsOf (decls : Array Decl) : Array Run := Id.run do
  let mut runs : Array Run := #[]
  for d in decls do
    if let some last := runs.back? then
      if last.isCo == d.isCo then
        runs := runs.pop.push { last with decls := last.decls.push d }
        continue
    runs := runs.push { isCo := d.isCo, decls := #[d] }
  return runs

/-- Does a constructor of the run `r` mention a type of the run `r'`? -/
private def mentions (r r' : Run) : Bool :=
  let names := r'.names
  r.decls.any fun d => d.ctors.any fun c => mentionsAny c.raw names

/-- The user's index telescope of a run. -/
private def Run.uidx (r : Run) : CommandElabM (Array (Ident × Term)) :=
  match r.decls[0]!.sort with
  | none => pure #[]
  | some s => readSort s

/-- The number of components of the run's index: one for a block, the user's indices otherwise. -/
private def Run.kIdx (r : Run) : CommandElabM Nat := do
  if r.decls.size ≥ 2 then return 1
  return (← r.uidx).size

/-- The packed index type of the run on the parameters `pTerms`: `Blk.Ix params` for a block,
`none` for a single type without indices (whose family is a type). -/
private def Run.J (r : Run) (pTerms : Array Term) : CommandElabM (Option Term) := do
  if r.decls.size ≥ 2 then return some (← mkAppT r.Ix pTerms)
  let tele ← r.uidx
  if tele.isEmpty then return none
  some <$> mkIxTerm tele

/-- The packed index of an occurrence of the `k`-th type of the run at the user's indices
`idx`: `@Blk.Ix.Tₖ params idx…` for a block, or `⟨idx…⟩`. -/
private def Run.packIdx (r : Run) (pTerms : Array Term) (k : Nat) (idx : Array Term) :
    CommandElabM Term := do
  if r.decls.size ≥ 2 then
    let c := mkIdent (r.Ix.getId ++ Name.mkSimple r.decls[k]!.T.getId.getString!)
    return Syntax.mkApp (← `(@$c:ident)) (pTerms ++ idx)
  if idx.size == 1 then pure idx[0]! else `(⟨$[$idx],*⟩)

/-- The family of the run, applied to the parameters `pTerms` (its own family parameter
included): the type itself, or `fun p => Blk params p.1 p.2…` on its packed index. -/
private def Run.fam (r : Run) (pTerms : Array Term) : CommandElabM Term := do
  let kC ← r.kIdx
  if kC == 0 then return ← `($(r.blk) $pTerms*)
  let p ← freshId "p"
  let mut projs : Array Term := #[]
  let mut cur : Term := idT p
  for _ in [0:kC - 1] do
    projs := projs.push (← `(PSigma.fst $cur))
    cur ← `(PSigma.snd $cur)
  projs := projs.push cur
  `(fun $p:ident => $(r.blk) $pTerms* $projs*)

/-- The family of the run `r''` as seen from the run `r` inside which it is being nested
(`r ≤ r''`): the run's block applied to the parameters and, when it mentions the run before it,
to that run's family, down to the family `selfFam` of the run `r` itself. -/
private partial def famOf (runs : Array Run) (pTerms : Array Term) (r : Nat) (selfFam : Term)
    (r'' : Nat) : CommandElabM Term := do
  if r'' == r then return selfFam
  let inner := runs[r'']!
  let args ← if mentions inner runs[r'' - 1]! then do
      let fam ← famOf runs pTerms r selfFam (r'' - 1)
      pure (pTerms.push fam)
    else pure pTerms
  inner.fam args

/-- Elaborate the runs of a `mixed_mutual` block, from the innermost out. -/
private def elabRuns (stx : Syntax) (runs : Array Run) : CommandElabM Unit := do
  let k := runs.size
  let ps₀ := runs[0]!.decls[0]!.ps
  let params ← ps₀.mapM fun b => do
    let (ids, _, _) ← readBinder b
    return ids
  let pids : Array Ident := params.foldl (· ++ ·) #[]
  let pTerms := pids.map idT
  -- Names the family parameter must avoid: the parameters, the types and the binders.
  let mut used : Array Name := pids.map (·.getId)
  for r in runs do
    for d in r.decls do
      used := used.push d.T.getId
      for c in d.ctors do
        let `(codataCtor| | $_:ident $bs:bracketedBinder* $[: $_]?) := c | continue
        for b in bs do
          let (ids, _, _) ← readBinder b
          used := used ++ ids.map (·.getId)
  let hygX ← `(X)
  let X : Ident := if used.contains `X then ⟨hygX.raw⟩ else mkIdent `X
  -- The indices of all blocks first: the family parameter of a run mentions the index of the
  -- run outside it.
  for r in runs do
    if r.decls.size ≥ 2 then
      unless ← declExists r.Ix do genIx r.Ix ps₀ r.decls
  for r' in [0:k] do
    let r := k - 1 - r'
    let run := runs[r]!
    -- The run outside, if mentioned: the family parameter.
    let outer? : Option Run := if r > 0 && mentions run runs[r - 1]! then some runs[r - 1]! else none
    let mut ps := ps₀
    let mut pTermsX := pTerms
    let mut subs : Array Subst := #[]
    if let some outer := outer? then
      let uX := mkIdent (Name.mkSimple ("u_" ++ outer.blk.getId.toString))
      unless (← getScope).levelNames.contains uX.getId do
        elabCommand (← `(universe $uX:ident))
      let XTy ← match ← outer.J pTerms with
        | none => `(Type $uX:ident)
        | some J => `($J → Type $uX:ident)
      ps := ps.push ⟨(← `(bracketedBinderF| ($X:ident : $XTy))).raw⟩
      pTermsX := pTerms.push (idT X)
      let outerJ ← outer.J pTerms
      subs := subs.push (outer.names, fun j idx => do
        if outerJ.isNone then pure (idT X) else `($X $(← outer.packIdx pTerms j idx)))
      subs := subs.push (run.names, fun j idx => `($(run.decls[j]!.T) $pTerms* $X $idx*))
    -- The runs inside that are mentioned: a run whose types are parameterised by the family of
    -- the run before it takes the chain of families down to this run's own, a nested
    -- occurrence through the composite of the declared containers.
    let selfFam ← run.fam pTermsX
    for r' in [r + 1:k] do
      let inner := runs[r']!
      if mentions run inner && mentions inner runs[r' - 1]! then
        let fam ← famOf runs pTerms r selfFam (r' - 1)
        subs := subs.push (inner.names, fun j idx => `($(inner.decls[j]!.T) $pTerms* $fam $idx*))
    let decls' ← run.decls.mapM fun d => do
      let ctors ← d.ctors.mapM fun c => return ⟨← substOccs pids subs c.raw⟩
      return { d with ctors, ps }
    withRef stx <| elabGroup run.isCo decls' (some pids.size)

/-- The declarations of a `mixed_mutual` block, in order. -/
private partial def collectDecls (stx : Syntax) : Array Syntax :=
  if stx.isOfKind ``codataCmd || stx.isOfKind ``dataCmd then #[stx]
  else match stx with
    | .node _ _ args => args.foldl (fun acc a => acc ++ collectDecls a) #[]
    | _ => #[]

@[command_elab mixedMutualCmd] def elabMixedMutual : CommandElab := fun stx => do
  let decls ← (collectDecls stx).mapM readDecl
  let runs := runsOf decls
  checkUniform decls[0]! decls false
  for r in runs do checkUniform r.decls[0]! r.decls true
  if runs.size == 1 then
    logWarningAt stx[0] m!"all declarations of this `mixed_mutual` block are `{if runs[0]!.isCo then "codata" else "data"}`; \
      use `mutual`"
    if decls.size == 1 then elabCommand (collectDecls stx)[0]!
    else elabGroup runs[0]!.isCo decls
    return
  -- Until structures in several parameters: a run may mention, among the runs outside it, only
  -- the adjacent one.
  for r in [0:runs.size] do
    for r' in [0:r] do
      if r' + 1 < r && mentions runs[r]! runs[r']! then
        let d := runs[r]!.decls.find? fun d => d.ctors.any fun c => mentionsAny c.raw runs[r']!.names
        throwErrorAt (d.map (·.T.raw)).get! m!"in a `mixed_mutual` block, a declaration may mention, among the runs outside its own, only the adjacent one \
          (`{d.get!.T}` mentions `{runs[r']!.decls[0]!.T}`, two or more runs outside): a reference to a run further outside \
          needs an occurrence structure in several parameters, which is not supported yet"
  elabRuns stx runs

@[command_elab Lean.Parser.Command.mutual] def elabMutualCodata : CommandElab := fun stx => do
  let cmds := stx[1].getArgs
  let ours (c : Syntax) : Bool := c.isOfKind ``codataCmd || c.isOfKind ``dataCmd
  unless cmds.all ours do
    if cmds.any ours then
      throwError "a mutual block must consist of `codata` and `data` declarations only"
    throwUnsupportedSyntax
  let decls ← cmds.mapM readDecl
  if decls.size == 1 then
    elabCommand cmds[0]!
    return
  let cs := decls.filter (·.isCo)
  let ds := decls.filter (!·.isCo)
  unless cs.isEmpty || ds.isEmpty do
    throwError "a `mutual` block may not mix `data` and `codata` declarations: the block is a nested \
      fixpoint and the nesting order is a choice; use `mixed_mutual … end`, which nests the \
      declarations in the order written, the first outermost"
  checkUniform decls[0]! decls true
  elabGroup decls[0]!.isCo decls

end Codata
