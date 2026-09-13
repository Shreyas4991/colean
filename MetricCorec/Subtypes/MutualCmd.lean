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
names. Mixed blocks are rejected: a block with both `data` and `codata` has no canonical meaning
(see `Sketch/MixedFail.lean`); the inductive type is nested in the coinductive one instead. For
other `mutual` blocks the elaborator defers to Lean's.
-/

open Lean Elab Command Lean.Parser.Term

namespace Codata

/-- One declaration of a block: its name, parameters, sort and constructors. -/
private def readDecl (stx : Syntax) :
    CommandElabM (Ident × Array (TSyntax ``bracketedBinder) × Option Term ×
      Array (TSyntax ``codataCtor)) := do
  match stx with
  | `(codata $T:ident $ps:bracketedBinder* $[: $s]? $cs:codataCtor*) => return (T, ps, s, cs)
  | `(data $T:ident $ps:bracketedBinder* $[: $s]? $cs:codataCtor*) => return (T, ps, s, cs)
  | _ => throwUnsupportedSyntax

@[command_elab Lean.Parser.Command.mutual] def elabMutualCodata : CommandElab := fun stx => do
  let cmds := stx[1].getArgs
  let isCo := cmds.all (·.isOfKind ``codataCmd)
  let isData := cmds.all (·.isOfKind ``dataCmd)
  unless isCo || isData do
    if cmds.any fun c => c.isOfKind ``codataCmd || c.isOfKind ``dataCmd then
      throwError "a mutual block must consist of `codata` declarations only, or of `data` \
        declarations only: a mixed block has no canonical meaning; nest the inductive type in \
        the coinductive one instead"
    throwUnsupportedSyntax
  let decls ← cmds.mapM readDecl
  if decls.size == 1 then
    elabCommand cmds[0]!
    return
  let (T₀, ps₀, s₀, _) := decls[0]!
  for (T, ps, s, _) in decls[1:] do
    unless ps.size == ps₀.size && (ps.zip ps₀).all (fun (a, b) => a.raw.structEq b.raw) do
      throwErrorAt T "the types of a mutual block must have the same parameters as `{T₀}`"
    let sameSort := match s, s₀ with
      | none, none => true
      | some a, some b => a.raw.structEq b.raw
      | _, _ => false
    unless sameSort do
      throwErrorAt T "the types of a mutual block must have the same indices as `{T₀}`"
  let blk := mkIdent (Name.mkSimple ("_".intercalate (decls.map (·.1.getId.toString)).toList))
  let which := mkIdent (blk.getId ++ `Which)
  let wCtors ← decls.mapM fun (T, _, _, _) =>
    `(Parser.Command.ctor| | $(mkIdent (Name.mkSimple T.getId.getString!)):ident)
  elabCommand (← `(inductive $which:ident where $[$wCtors:ctor]*))
  let ctx ← mkCtx isCo blk ps₀ s₀ (decls.map fun (T, _, _, cs) => (T, cs)) (some which)
  if isCo then codataPipeline ctx else dataPipeline ctx

end Codata
