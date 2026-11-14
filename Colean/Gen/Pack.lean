import Lean

/-!
# Generators on `Expr`: the display of the packing of a block's families

*Spec.* `Blk.St params S₁ … Sₖ i` (`Gen/Surface.lean`) packs a family per type of a block into
one on the block's index `Blk.Ix` by cases. At a constructor `Blk.Ix.Tⱼ params idx` it is
`Sⱼ idx` by definition, and it is shown so: the field of a constructor of the layer per type at
the types, `Tree_Forest.St (Tree α) (Forest α) .Forest` after `match t.dtor with | .node a cs`,
is shown `Forest α`. The packings carry the attribute `colean_pack`, and a delaborator shows an
application of one at a constructor as the family it packs there, applied to the constructor's
fields, each delaborated at its own position, so that hovers still show the term they are part
of; a family that is a `fun` (`fun _ => Nat`), applied to fields, is shown as its body at them
(`Nat`), a term that is not a part of the application.
-/

open Lean Meta PrettyPrinter Delaborator SubExpr

namespace Codata.Gen

/-- The packings `Blk.St` of the blocks (`Gen/Surface.lean`), shown at a constructor of `Blk.Ix`
as the family they pack there (`delabPack`). -/
initialize packAttr : TagAttribute ←
  registerTagAttribute `colean_pack
    "the packing of a family per type of a block by cases on the block's index (internal)"

/-- `Blk.St params S₁ … Sₖ (.Tⱼ params idx)`, applied to all its arguments, shown as `Sⱼ idx`. The
families `S₁ … Sₖ` and the index are the explicit binders of `Blk.St`, after the parameters. -/
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

end Codata.Gen
