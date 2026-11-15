import Lean

/-!
# Generators on `Expr`: the display of a block's packing and of its layers' constructors

*Spec.* `Blk.Colean.St params S₁ … Sₖ i` (`Gen/Surface.lean`) packs a family per type of a block
into one on the block's index `Blk.Ix` by cases. At a constructor `Blk.Ix.Tⱼ params idx` it is
`Sⱼ idx` by definition, and it is shown so: the field of a constructor of the layer per type at the
types, `Tree_Forest.Colean.St (Tree α) (Forest α) .Forest` after `match t.dtor with | .node a cs`,
is shown `Forest α`. The packings carry the attribute `colean_pack`, and a delaborator shows an
application of one at a constructor as the family it packs there, applied to the constructor's
fields, each delaborated at its own position, so that hovers still show the term they are part of; a
family that is a `fun` (`fun _ => Nat`), applied to fields, is shown as its body at them (`Nat`), a
term that is not a part of the application.

The constructor `Tₘ.F.c` of the layer per type (`Gen/Surface.lean`) is the block functor's
constructor `Blk.F.c` (or `Blk.F.Tₘ_c`, when another type of the block has a constructor `c`) at the
packed family, a reducible definition that patterns unfold. The block functor's constructors are
recorded with it (`layerCtorExt`), and an application of one at a packing `Blk.Colean.St params
S₁ … Sₖ` is shown as one of `Tₘ.F.c`, with the same explicit arguments, each at its own position:
`Forest.F.cons t f` for `Tree_Forest.F.cons t f` after `match f.dtor with`.
-/

open Lean Meta PrettyPrinter Delaborator SubExpr

namespace Codata.Gen

/-- The packings `Blk.Colean.St` of the blocks (`Gen/Surface.lean`), shown at a constructor of
`Blk.Ix` as the family they pack there (`delabPack`). -/
initialize packAttr : TagAttribute ←
  registerTagAttribute `colean_pack
    "the packing of a family per type of a block by cases on the block's index (internal)"

/-- `Blk.Colean.St params S₁ … Sₖ (.Tⱼ params idx)`, applied to all its arguments, shown as
`Sⱼ idx`. The families `S₁ … Sₖ` and the index are the explicit binders of `Blk.Colean.St`, after
the parameters. -/
@[delab app]
def delabPack : Delab := do
  let e ← getExpr
  let .const n _ := e.getAppFn | failure
  unless packAttr.hasTag (← getEnv) n do failure
  let ci ← getConstInfo n
  let bis ← forallTelescope ci.type fun xs _ => xs.mapM (·.fvarId!.getBinderInfo)
  unless e.getAppNumArgs == bis.size do failure
  let k := (bis.toList.reverse.takeWhile (·.isExplicit)).length - 1
  let np := bis.size - k - 1
  let i := e.appArg!
  let .const c _ := i.getAppFn | failure
  let some (.ctorInfo cv) := (← getEnv).find? c | failure
  unless i.getAppNumArgs == cv.numParams + cv.numFields && cv.cidx < k do failure
  let S := e.getArg! (np + cv.cidx)
  -- A `fun` applied to the fields: its body at them, as an expression of its own.
  if cv.numFields > 0 && S.isLambda then
    let e' := S.beta (i.getAppArgs.extract cv.numParams i.getAppNumArgs)
    return ← withTheReader SubExpr (fun s => { s with expr := e' }) delab
  let f ← withNaryArg (np + cv.cidx) delab
  let args ← (List.range cv.numFields).toArray.mapM fun a =>
    withNaryArg (bis.size - 1) (withNaryArg (cv.numParams + a) delab)
  return Syntax.mkApp f args

/-- The constructors of the block functors with a constructor of a layer per type for them
(`Gen/Surface.lean`): `Blk.F.c` (or `Blk.F.Tₘ_c`) to `Tₘ.F.c` and the position of the family among
the arguments of `Blk.F.c`, after the parameters; for the closed types of a run inside a
`mixed_mutual` block, the closed constructor to the closed one of the layer. -/
initialize layerCtorExt : MapDeclarationExtension (Name × Nat) ← mkMapDeclarationExtension

/-- `Blk.F.c params (Blk.Colean.St params S₁ … Sₖ) args`, applied to all its arguments, shown as
`Tₘ.F.c args`, with the explicit arguments of `Blk.F.c`, which are those of `Tₘ.F.c`. Not with
`pp.explicit` or `pp.universes`, which would show the arguments or the universes of `Blk.F.c`. -/
@[delab app]
def delabLayerCtor : Delab := do
  let e ← getExpr
  let .const n _ := e.getAppFn | failure
  let env ← getEnv
  let some (alias, xi) := layerCtorExt.find? env n | failure
  if (← getPPOption getPPExplicit) || (← getPPOption getPPUniverses) then failure
  let bis ← forallTelescope (← getConstInfo n).type fun xs _ => xs.mapM (·.fvarId!.getBinderInfo)
  unless e.getAppNumArgs == bis.size && xi < bis.size do failure
  let X := e.getArg! xi
  let .const st _ := X.getAppFn | failure
  unless packAttr.hasTag env st do failure
  let stArity ← forallTelescope (← getConstInfo st).type fun xs _ => pure xs.size
  unless X.getAppNumArgs + 1 == stArity do failure
  let f ← withNaryFn <| withTheReader SubExpr (fun s => { s with expr := .const alias [] })
    delabConst
  let args ← ((List.range bis.size).filter fun a => xi < a && bis[a]!.isExplicit).toArray.mapM
    fun a => withNaryArg a delab
  return Syntax.mkApp f args

end Codata.Gen
