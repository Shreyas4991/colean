import Colean.Cmd.Analysis

/-!
# The command, step 1: the functor

*Spec.* Input: the context. Output: the inductive `T.F`, its action on functions `T.F.map`
with the computation rules `T.F.map_cᵢ` (`rfl`), and the two functor laws `T.F.map_id`,
`T.F.map_comp`. The laws are the first of the two places where the command proves something by
tactic (`cases` and `rfl`, with the `Occ` laws for nested arguments).
-/

open Lean Elab Command Lean.Parser.Term

namespace Codata

open Ctx

def genFunctor (ctx : Ctx) : CommandElabM Unit := do
  let pExp := ctx.pExp
  let pImp := ctx.pImp
  let xTy ← ctx.famTy
  let ib ← ctx.ixB
  let holes ← ctx.holes
  let jArgs := ctx.jArgs
  let X ← `(X)
  let Y ← `(Y)
  let fTy ← ctx.famFn X Y
  let FX ← ctx.atI (← `($(ctx.Fp) X))
  let FY ← ctx.atI (← `($(ctx.Fp) Y))
  let fCtors ← ctx.ctors.mapM fun c => do
    let bs ← fBinders c
    if ctx.idxed then
      let res ← appT (← `($(ctx.Fp) X)) c.idx
      `(Parser.Command.ctor| | $(c.fname):ident $[$bs]* : $res)
    else
      `(Parser.Command.ctor| | $(c.fname):ident $[$bs]*)
  if ctx.idxed then
    elabCommand (← `(inductive $(ctx.F):ident $[$pExp]* (X : $xTy) : $xTy where
      $[$fCtors:ctor]*))
  else
    elabCommand (← `(inductive $(ctx.F):ident $[$pExp]* (X : $xTy) where
      $[$fCtors:ctor]*))
  -- `F.map`, and its computation on constructors.
  let mapAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.mapM fun c => do
    ctx.alt c #[← ctx.fPat c] (← ctx.fApp c Y (← ctx.mappedArgs c true))
  let discrsA := ctx.discrs (← `(a))
  elabCommand (← `(def $(ctx.Fmap):ident $[$pImp]* {X Y : $xTy} (f : $fTy) $[$ib]*
      (a : $FX) : $FY := match $[$discrsA:term],* with $mapAlts:matchAlt*))
  for c in ctx.ctors do
    let bs ← fBinders c
    let lhs ← ctx.fApp c X (c.allIds.map idT)
    let rhs ← ctx.fApp c Y (← ctx.mappedArgs c false)
    let FXc ← appT (← `($(ctx.Fp) X)) c.idx
    elabCommand (← `(@[simp] theorem $(ctx.nF ("map_" ++ c.fname.getId.toString)):ident
        $[$pImp]* {X Y : $xTy} (f : $fTy) $[$bs]* :
        $(ctx.Fmap) f ($lhs : $FXc) = $rhs := rfl))
  -- The functor laws.
  let idFn ← if ctx.idxed then `(fun $[$holes]* x => x) else `(id)
  elabCommand (← `(theorem $(ctx.Fmap_id):ident $[$pImp]* {X : $xTy} $[$ib]* (a : $FX) :
      $(ctx.Fmap) $idFn a = a := by
    cases a
    all_goals first | rfl | simp only [$(ctx.Fmap):ident, id_eq, Codata.Occ.map_id, Codata.Occ.map_id', Codata.IOcc.map_id, Codata.IOcc.map_id']))
  let gTy ← ctx.famFn Y (← `(Z))
  let jIds := ctx.jIds
  let gf ← if ctx.idxed then `(fun $[$jIds:ident]* x => g $jArgs* (f $jArgs* x)) else `(g ∘ f)
  elabCommand (← `(theorem $(ctx.Fmap_comp):ident $[$pImp]* {X Y Z : $xTy} (g : $gTy)
      (f : $fTy) $[$ib]* (a : $FX) : $(ctx.Fmap) $gf a = $(ctx.Fmap) g ($(ctx.Fmap) f a) := by
    cases a
    all_goals first | rfl | simp only [$(ctx.Fmap):ident, Codata.Occ.map_map, Codata.IOcc.map_map, Function.comp_def]))

end Codata
