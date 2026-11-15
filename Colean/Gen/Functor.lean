import Colean.Gen.Ctx

/-!
# Generators on `Expr`, step 1: the functor

*Spec.* Input: the context. Output: the inductive `T.F (params) (X : ∀ j, Type _) : ∀ j, Type _`
(the constructors with every occurrence `T params idx` replaced by `X idx`), its action on
functions `T.F.fmap`, defined by `casesOn`, the computation rules `T.F.fmap_cᵢ` (simp lemmas,
proved by `rfl`), and the functor laws `T.F.fmap_id`, `T.F.fmap_comp`, proved by `cases` and
`rfl`, or `simp only` with the computation rules and the laws of `Model/Occ.lean` for a
constructor with nested arguments.
-/

open Lean Meta Elab Term

namespace Codata.Gen

namespace Ctx

variable (ctx : Ctx)

/-- `T.F params X idx`, at universe `w` of `X`. -/
def fAt (w : Level) (X : Expr) (idx : Array Expr) : MetaM Expr := do
  ctx.genAt ctx.F [w] (#[X] ++ idx)

/-- `@T.F.fmap params X Y f idx a`, at the universes `wX`, `wY` of `X`, `Y`. -/
def mapAt (wX wY : Level) (X Y f : Expr) (idx : Array Expr) (a : Expr) : MetaM Expr := do
  ctx.genAt ctx.Fmap [wX, wY] (#[X, Y, f] ++ idx ++ #[a])

/-- The arguments of `F.cᵢ` after `map f`, for the arguments `ys` (at `X`) of the constructor
`c`: data unchanged, `f idx y` for a plain recursive argument, `fun zs => f idx (y zs)` under a
telescope, `Occ.map o o' f y` (`IOcc.map`) for a nested one. -/
def mappedArgs (c : Ctor) (ys : Array Expr) (wX wY : Level) (f : Expr) :
    TermElabM (Array Expr) := do
  let σ (e : Expr) := e.replaceFVars c.fvars ys
  -- On the packed index, `f` uncurried.
  let fP ← if ctx.k ≤ 1 then pure f else
    withLocalDeclD `p ctx.J fun p => do mkLambdaFVars #[p] (mkAppN f (← ctx.projs p))
  (c.args.zip ys).mapM fun (a, y) => do
    match a.kind with
    | .data => pure y
    | .plain idx => pure (mkAppN f (idx.map σ |>.push y))
    | .fn n => openFn n (← inferType y) fun zs idx =>
      mkLambdaFVars zs (mkAppN f (idx.push (mkAppN y zs)))
    | .nest o =>
      let oX := ctx.nestAt o wX σ
      let oY := ctx.nestAt o wY σ
      if ctx.idxed then mkAppM ``Codata.IOcc.map #[oX, oY, fP, y]
      else mkAppM ``Codata.Occ.map #[oX, oY, f, y]

/-- `T.F`. -/
def genF : TermElabM Unit := do
  let [w] := ctx.freshLevels 1 | unreachable!
  let w := ctx.holeLevel (.param w)
  withLocalDeclD `X (← ctx.famType w) fun X => do
  let rep (idx : Array Expr) := mkAppN X idx
  let lvls ← ctx.ctors.foldlM (init := #[]) fun acc c => ctx.withArgsAt c rep w fun ys _ => do
    return acc ++ (← ys.mapM fun y => do getLevel (← inferType y))
  -- The contract takes `F` at the universe of the type, at least that of the index: without a
  -- recursive argument, `F` is put there (`A : Type → Type 1 | mk (n : Nat) : A Nat`).
  let r := resultLevel lvls
  let r := if ctx.fixedLvl?.isSome || w.occurs r || r.geq ctx.Jlvl then r
    else (mkLevelMax' r ctx.Jlvl).normalize
  let Fty ← mkForallFVars (ctx.params.push X)
    (← ctx.withJs fun js => mkForallFVars js (mkSort r.succ))
  -- The constructors, with a local variable for `F` until its universes are known.
  withLocalDeclD `F Fty fun Fv => do
  let ctorTys ← ctx.ctors.mapM fun c => ctx.withArgsAt c rep w fun ys σ => do
    withBinderInfo (ctx.params.push X) .implicit do
      mkForallFVars (ctx.params.push X ++ ys) (mkAppN Fv (ctx.params ++ #[X] ++ c.idx.map σ))
  let us ← ctx.levelParamsOf (ctx.freshLevels 1) (ctorTys.push Fty)
  let Fc := Lean.mkConst ctx.F (us.map mkLevelParam)
  addInductive us (ctx.params.size + 1) [{
    name := ctx.F, type := Fty
    ctors := (ctx.ctors.zip ctorTys).toList.map fun (c, t) =>
      { name := ctx.fCtor c, type := t.replaceFVar Fv Fc } }] ctx.ref

/-- `T.F.fmap` by `casesOn`, and its computation rules `T.F.fmap_cᵢ`. -/
def genMap : TermElabM Unit := do
  let fresh := ctx.freshLevels 2
  let [wX, wY] := fresh | unreachable!
  let (wX, wY) := (ctx.holeLevel (.param wX), ctx.holeLevel (.param wY))
  withLocalDecl `X .implicit (← ctx.famType wX) fun X => do
  withLocalDecl `Y .implicit (← ctx.famType wY) fun Y => do
  withLocalDeclD `f (← ctx.famFn X Y) fun f => do
  withLocalDeclD `a (← ctx.fAt wX X ctx.idx) fun a => do
  -- By cases on `a`; the arguments of `F` that became parameters (`fixedIndices`) are the first
  -- arguments of every constructor.
  let np := ctx.params.size + 1
  let FX ← ctx.fAt wX X ctx.idx
  let value ← mkCasesOnApp ctx.F (← ctx.levelsWith ctx.F [wX]) FX.getAppArgs a
    (← getLevel (← ctx.fAt wY Y ctx.idx))
    (fun is _ => do
      let ps := FX.getAppArgs.extract np (FX.getAppArgs.size - is.size)
      ctx.fAt wY Y (ps ++ is))
    (fun cname xs => do
      let some c := ctx.ctors.find? (ctx.fCtor · == cname)
        | throwError "internal error: unexpected constructor {cname}"
      let ys := FX.getAppArgs.extract np (np + c.args.size - xs.size) ++ xs
      let args ← ctx.mappedArgs c ys wX wY f
      ctx.genAt (ctx.fCtor c) [wY] (#[Y] ++ args))
  let xs := ctx.params ++ #[X, Y, f] ++ ctx.idx ++ #[a]
  let (type, value) ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    return (← mkForallFVars xs (← ctx.fAt wY Y ctx.idx), ← mkLambdaFVars xs value)
  addDef ctx.Fmap (← ctx.levelParamsOf fresh #[type, value]) type value ctx.ref
  -- The computation rules.
  for c in ctx.ctors do
    ctx.withArgsAt c (mkAppN X) wX fun ys σ => do
    let lhs ← ctx.mapAt wX wY X Y f (c.idx.map σ)
      (mkAppN (← ctx.constWith (ctx.fCtor c) [wX]) (ctx.params ++ #[X] ++ ys))
    let rhs := mkAppN (← ctx.constWith (ctx.fCtor c) [wY])
      (ctx.params ++ #[Y] ++ (← ctx.mappedArgs c ys wX wY f))
    let xs := ctx.params ++ #[X, Y, f] ++ ys
    let (type, value) ← withBinderInfo ctx.params .implicit do
      return (← mkForallFVars xs (← mkEq lhs rhs), ← mkLambdaFVars xs (← mkEqRefl lhs))
    let name := ctx.FmapCtor c
    addThm name (← ctx.levelParamsOf fresh #[type]) type value ctx.ref
    addSimp name

/-- The proof of a functor law: `cases` on the last hypothesis, then `rfl`, or `simp only` with
`lemmas` for a constructor with nested arguments. -/
def lawTactic (lemmas : Array Name) (g : MVarId) : TermElabM Unit := do
  let (hs, g) ← g.intros
  for sg in ← g.cases hs.back! do
    let some c := ctx.ctors.find? (ctx.fCtor · == sg.ctorName)
      | throwError "internal error: unexpected case {sg.ctorName}"
    if c.hasNest then simpOnly sg.mvarId lemmas else sg.mvarId.refl

/-- `T.F.fmap_id` and `T.F.fmap_comp`. -/
def genLaws : TermElabM Unit := do
  let mapCs := ctx.ctors.map ctx.FmapCtor
  -- `fmap_id`
  do
    let fresh := ctx.freshLevels 1
    let [wX] := fresh | unreachable!
    let wX := ctx.holeLevel (.param wX)
    withLocalDecl `X .implicit (← ctx.famType wX) fun X => do
    withLocalDeclD `a (← ctx.fAt wX X ctx.idx) fun a => do
    let idF ← if ctx.idxed then
        ctx.withJs fun js => withLocalDeclD `x (mkAppN X js) fun x => mkLambdaFVars (js.push x) x
      else mkAppOptM ``id #[X]
    let xs := ctx.params ++ #[X] ++ ctx.idx ++ #[a]
    let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
      mkForallFVars xs (← mkEq (← ctx.mapAt wX wX X X idF ctx.idx a) a)
    let value ← prove type <| ctx.lawTactic <| mapCs ++
      #[``id_eq, ``Codata.Occ.map_id, ``Codata.Occ.map_id', ``Codata.IOcc.map_id,
        ``Codata.IOcc.map_id']
    addThm ctx.Fmap_id (← ctx.levelParamsOf fresh #[type]) type value ctx.ref
  -- `fmap_comp`
  let fresh := ctx.freshLevels 3
  let [wX, wY, wZ] := fresh | unreachable!
  let (wX, wY, wZ) :=
    (ctx.holeLevel (.param wX), ctx.holeLevel (.param wY), ctx.holeLevel (.param wZ))
  withLocalDecl `X .implicit (← ctx.famType wX) fun X => do
  withLocalDecl `Y .implicit (← ctx.famType wY) fun Y => do
  withLocalDecl `Z .implicit (← ctx.famType wZ) fun Z => do
  withLocalDeclD `g (← ctx.famFn Y Z) fun g => do
  withLocalDeclD `f (← ctx.famFn X Y) fun f => do
  withLocalDeclD `a (← ctx.fAt wX X ctx.idx) fun a => do
  let gf ← if ctx.idxed then
      ctx.withJs fun js => withLocalDeclD `x (mkAppN X js) fun x =>
        mkLambdaFVars (js.push x) (mkAppN g (js.push (mkAppN f (js.push x))))
    else mkAppM ``Function.comp #[g, f]
  let lhs ← ctx.mapAt wX wZ X Z gf ctx.idx a
  let rhs ← ctx.mapAt wY wZ Y Z g ctx.idx (← ctx.mapAt wX wY X Y f ctx.idx a)
  let xs := ctx.params ++ #[X, Y, Z, g, f] ++ ctx.idx ++ #[a]
  let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    mkForallFVars xs (← mkEq lhs rhs)
  let value ← prove type <| ctx.lawTactic <| mapCs ++
    #[``Codata.Occ.map_map, ``Codata.IOcc.map_map, ``Function.comp_def]
  addThm ctx.Fmap_comp (← ctx.levelParamsOf fresh #[type]) type value ctx.ref

/-- Step 1. -/
def genFunctor : TermElabM Unit := do
  ctx.genF
  ctx.genMap
  ctx.genLaws

end Ctx

end Codata.Gen
