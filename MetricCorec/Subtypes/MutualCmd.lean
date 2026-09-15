import MetricCorec.Subtypes.DataCmd

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
parameters and the same indices, is one family over an enumeration of its types: the block
`Tree_Forest` (the names joined by `_`) is declared as a single indexed family whose first index
is `Tree_Forest.Which`, with constructors `Tree` and `Forest`, and every declaration of the single
type case is generated for the block (`Tree_Forest.F`, `Tree_Forest.corec`, `Tree_Forest.bisim`,
`Tree_Forest.rec`, …). This is how Lean itself elaborates mutual fixpoints, and the generic
theory needs nothing new. Then, per type: `Tree α := Tree_Forest α .Tree`, its constructors
`Tree.node` with their lemmas under `Tree`, `Tree.casesOn` with only the constructors of `Tree`,
registered as the `cases` eliminator, and aliases `Tree.corec`, `Tree.bisim` (or `Tree.fold`)
restricting the block-level declarations to the type. Dot notation `t.dtor` resolves to
`Tree_Forest.dtor` through the definition of `Tree`, and the lemmas are stated with the
block-level `dtor` and `ctor`. Corecursion and induction take a state or motive over the whole
block:
`S : Tree_Forest.Which → Type _` and `c : ∀ m, S m → Tree_Forest.F α S m` for `corec`, and
`induction t using Tree_Forest.rec` for `data`, as with Lean's mutual inductives, whose
`induction` tactic does not apply to mutual types either.

Constructor names shared by several types of the block are qualified in the block-level
inductives (`Even_succ`, `Odd_succ` in `Even_Odd.F`); the per-type declarations keep the plain
names.

## Mixed blocks

```
mutual
data Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
codata Tree (α : Type u)
  | node (a : α) (children : Forest α)
end
```

A block with both `data` and `codata` declarations is a nested fixpoint: the inductive types
are the least fixpoint *inside* the greatest one, so that they are finite structures between
coinductive steps (`Forest α` is a finite list of trees, `Tree α` an infinitely deep, finitely
branching tree). It is elaborated as such: the `data` declarations form a block with one extra
parameter, the coinductive family `X` (a type `X : Type u` for a single coinductive type without
indices, a family `X : J → Type u` over the coinductive block's packed index otherwise), every
occurrence of a coinductive type replaced by `X` (at its packed index); then the `codata`
declarations form a block in which every occurrence of an inductive type `Forest α` is
`Forest α (Tree α)` (or `Forest α (fun p => Tree_Stream α p.1 p.2)`), a nested occurrence
through the container that `Forest` is in its parameter (`Param.lean`). So the user sees
`Forest α X` with `Forest.nil : Forest α X` for any `X`, `Tree.node : α → Forest α (Tree α) →
Tree α`, and `Tree.F α X` with a field `children : Forest α X`: the functor of the mixed block.
`Forest.fold`, `Forest.rec` and `Forest.casesOn` are the ones of the parameterised type,
`Tree.corec`, `Tree.bisim` (with `IContainer.Rel`/`Container.Rel` on the forest) the ones of
the coinductive block. The other nesting order (coinductive inside inductive) is a different
type; it is obtained by declaring the coinductive types first, with explicit parameters, and
nesting through them. For other `mutual` blocks the elaborator defers to Lean's.
-/

open Lean Elab Command Lean.Parser.Term

namespace Codata

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

/-- The block name of several declarations, and its enumeration `Which`. -/
private def blockName (decls : Array Decl) : Ident :=
  mkIdent (Name.mkSimple ("_".intercalate (decls.map (·.T.getId.toString)).toList))

/-- The enumeration of the types of a block. -/
private def genWhich (which : Ident) (decls : Array Decl) : CommandElabM Unit := do
  let wCtors ← decls.mapM fun d =>
    `(Parser.Command.ctor| | $(mkIdent (Name.mkSimple d.T.getId.getString!)):ident)
  elabCommand (← `(inductive $which:ident where $[$wCtors:ctor]*))

/-- Elaborate a uniform group (all `codata` or all `data`), as a single declaration or as a
block; `Which` may have been declared already. -/
private def elabGroup (isCo : Bool) (decls : Array Decl) : CommandElabM Unit := do
  let (T, ps, sort) := (decls[0]!.T, decls[0]!.ps, decls[0]!.sort)
  let ctx ← if decls.size == 1 then
      mkCtx isCo T ps sort #[(T, decls[0]!.ctors)] none
    else do
      let blk := blockName decls
      let which := mkIdent (blk.getId ++ `Which)
      unless ← declExists which do genWhich which decls
      mkCtx isCo blk ps sort (decls.map fun d => (d.T, d.ctors)) (some which)
  if isCo then codataPipeline ctx else dataPipeline ctx

/-- Replace every occurrence `T params idx…` of one of the types `tNames` in `stx` by
`f m idx`. -/
private partial def substOccs (tNames : Array Name) (params : Array Ident)
    (f : Nat → Array Term → CommandElabM Term) (stx : Syntax) : CommandElabM Syntax := do
  if let some (m, idx) := recIdx tNames params ⟨stx⟩ then return (← f m idx).raw
  match stx with
  | .node info k args => return .node info k (← args.mapM (substOccs tNames params f))
  | _ => return stx

/-- A mixed block: the `data` declarations, parameterised by the coinductive family, then the
`codata` declarations nesting through them. -/
private def elabMixed (ds cs : Array Decl) : CommandElabM Unit := do
  let ps₀ := ds[0]!.ps
  let sort := ds[0]!.sort
  let params ← ps₀.mapM fun b => do
    let (ids, _, _) ← readBinder b
    return ids
  let pids : Array Ident := params.foldl (· ++ ·) #[]
  let pTerms := pids.map idT
  let uidx ← match sort with
    | none => pure #[]
    | some s => readSort s
  let nC := cs.size
  let kC := (if nC ≥ 2 then 1 else 0) + uidx.size
  let cBlk := if nC == 1 then cs[0]!.T else blockName cs
  let whichC := mkIdent (cBlk.getId ++ `Which)
  if nC ≥ 2 then genWhich whichC cs
  -- The coinductive family's index type: nothing for a single type without indices.
  let mId ← freshId "m"
  let tele := (if nC ≥ 2 then #[(mId, idT whichC)] else #[]) ++ uidx
  let J : Option Term ← if kC == 0 then pure none else some <$> mkIxTerm tele
  -- The parameter, named `X` unless the declarations use the name.
  let used : Array Name := pids.map (·.getId) ++ (ds ++ cs).map (·.T.getId)
  let hygX ← `(X)
  let X : Ident := if used.contains `X then ⟨hygX.raw⟩ else mkIdent `X
  -- Its universe: a variable of the current scope (a hole would be solved differently across
  -- the generated declarations).
  let uX := mkIdent (Name.mkSimple ("u_" ++ cBlk.getId.toString))
  unless (← getScope).levelNames.contains uX.getId do
    elabCommand (← `(universe $uX:ident))
  let XTy ← match J with
    | none => `(Type $uX:ident)
    | some J => `($J → Type $uX:ident)
  let dNames := ds.map (·.T.getId)
  let cNames := cs.map (·.T.getId)
  -- The packed index of an occurrence of the `k`-th coinductive type at `idx`.
  let packC (k : Nat) (idx : Array Term) : CommandElabM Term := do
    let args := (if nC ≥ 2 then
        #[idT (mkIdent (whichC.getId ++ Name.mkSimple cs[k]!.T.getId.getString!))]
      else #[]) ++ idx
    if args.size == 1 then pure args[0]! else `(⟨$[$args],*⟩)
  -- The `data` group: coinductive types become the parameter, inductive types take it.
  let ds' ← ds.mapM fun d => do
    let ctors ← d.ctors.mapM fun c => do
      let c ← substOccs cNames pids (fun k idx => do
        if kC == 0 then pure (idT X) else `($X $(← packC k idx))) c.raw
      let c ← substOccs dNames pids (fun j idx => `($(ds[j]!.T) $pTerms* $X $idx*)) c
      return ⟨c⟩
    return { d with ctors, ps := ps₀.push ⟨(← `(bracketedBinderF| ($X:ident : $XTy))).raw⟩ }
  elabGroup false ds'
  -- The `codata` group: inductive types are applied to the coinductive family.
  let fam ← match J with
    | none => `($(cs[0]!.T) $pTerms*)
    | some _ => do
      let p ← freshId "p"
      let mut projs : Array Term := #[]
      let mut cur : Term := idT p
      for _ in [0:kC - 1] do
        projs := projs.push (← `(PSigma.fst $cur))
        cur ← `(PSigma.snd $cur)
      projs := projs.push cur
      `(fun $p:ident => $cBlk $pTerms* $projs*)
  let cs' ← cs.mapM fun d => do
    let ctors ← d.ctors.mapM fun c => do
      let c ← substOccs dNames pids (fun j idx => `($(ds[j]!.T) $pTerms* $fam $idx*)) c.raw
      return ⟨c⟩
    return { d with ctors }
  elabGroup true cs'

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
  let d₀ := decls[0]!
  for d in decls[1:] do
    unless d.ps.size == d₀.ps.size && (d.ps.zip d₀.ps).all (fun (a, b) => a.raw.structEq b.raw) do
      throwErrorAt d.T "the types of a mutual block must have the same parameters as `{d₀.T}`"
    let sameSort := match d.sort, d₀.sort with
      | none, none => true
      | some a, some b => a.raw.structEq b.raw
      | _, _ => false
    unless sameSort do
      throwErrorAt d.T "the types of a mutual block must have the same indices as `{d₀.T}`"
  let cs := decls.filter (·.isCo)
  let ds := decls.filter (!·.isCo)
  if ds.isEmpty then elabGroup true cs
  else if cs.isEmpty then elabGroup false ds
  else elabMixed ds cs

end Codata
