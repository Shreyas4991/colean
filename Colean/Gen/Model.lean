import Colean.Gen.Rel

/-!
# Generators on `Expr`, step 2: the model and the contract

*Spec.* Input: the context, `T.F` (step 1), the signature and the isomorphism. Output:

* `T := Cotype (T.sig params)` (`Intype` for `data`), curried in the indices;
* for `codata`: `T.dtor`, `T.corec` (with a state in any universe), `T.dtor_corec` (simp),
  `T.bisim` (for `T.F.Rel`), and `T.contract : Codata.Contract T F`;
* for `data`: `T.ctor`, `T.fold` (into a family in any universe), `T.fold_ctor` (simp), and
  `T.contract : Data.Contract T F`.

No proofs: every theorem instantiates a transport theorem of `Model/Cotype.lean`,
`Model/Intype.lean` or `Framework.lean` through the isomorphism. The theory states everything
for families on one index type, the packed index; the user-facing declarations are curried, and
the instantiations convert with lambdas (`curryN`, `uncurryN`, `packFam`), so that each statement
is definitionally the theory's.
-/

open Lean Meta Elab Term

namespace Codata.Gen

/-- `fun (x : ty) => body x`, with binder info `bi`. -/
def lam (n : Name) (ty : Expr) (body : Expr → TermElabM Expr) (bi := BinderInfo.default) :
    TermElabM Expr :=
  withLocalDecl n bi ty fun x => do mkLambdaFVars #[x] (← body x)

namespace Ctx

variable (ctx : Ctx)

/-! ### Terms -/

/-- `fun {p : Ix} => body p`, on the packed index. -/
def lamP (body : Expr → TermElabM Expr) : TermElabM Expr := do
  lam `p (← ctx.ixp) body .implicit

/-- `T params`, the curried family. -/
def tFam : MetaM Expr := return mkAppN (← ctx.constWith ctx.name []) ctx.params

/-- `T params idx`. -/
def tAt (idx : Array Expr) : MetaM Expr := return mkAppN (← ctx.tFam) idx

/-- `T.F params X`, for a curried family `X` at universe `w`. -/
def fFam (w : Level) (X : Expr) : MetaM Expr :=
  return mkAppN (← ctx.constWith ctx.F [w]) (ctx.params.push X)

/-- `Ix → Type w`. -/
def famP (w : Level) : MetaM Expr := do mkArrow (← ctx.ixp) (mkSort w.succ)

/-- The functor of the contract, on families on the packed index:
`fun X p => T.F params (curry X) p.1 p.2`, or `T.F params`. -/
def fPk (L : Level) : TermElabM Expr := do
  if ctx.k == 1 then return mkAppN (← ctx.constWith ctx.F [L]) ctx.params
  lam `X (← ctx.famP L) fun X => do
    lam `p (← ctx.ixp) fun p => do
      return mkAppN (← ctx.fFam L (← ctx.curryFam X)) (← ctx.projs p)

/-- `@T.F.map params X Y f idx a` on the packed index `p`, for curried families `X`, `Y` and `f`
on the packed index. -/
def mapP (wX wY : Level) (X Y f p a : Expr) : TermElabM Expr := do
  ctx.mapAt wX wY X Y (← ctx.curryN f 1) (← ctx.projs p) a

/-! ### The type -/

/-- `T := Cotype (T.sig params)` (or `Intype`), curried. -/
def genType : TermElabM Unit := do
  let L ← ctx.tLvl
  let fam ← ctx.modelFam
  let value ← match ctx.k with
    | 0 => mkLambdaFVars ctx.params (mkApp fam (Lean.mkConst ``Unit.unit))
    | 1 => mkLambdaFVars ctx.params fam
    | _ => mkLambdaFVars (ctx.params ++ ctx.idx) (mkApp fam (← ctx.packI))
  let type ← mkForallFVars (ctx.params ++ ctx.idx) (mkSort L.succ)
  unless ctx.isBlock do addRangesUser ctx.name ctx.ref ctx.types[0]!.nameRef
  addDef ctx.name (← ctx.levelParamsOf [] #[type, value]) type value ctx.ref

/-! ### The coinductive contract -/

/-- `T.dtor`, `T.corec`, `T.dtor_corec`, `T.bisim`. -/
def genContract : TermElabM Unit := do
  let L ← ctx.tLvl
  let σ ← ctx.sigE
  let fam ← ctx.modelFam
  let pI ← ctx.packI
  let T ← ctx.tFam
  -- `dtor`
  withLocalDeclD `t (← ctx.tAt ctx.idx) fun t => do
    let dtorC := mkApp3 (← ctx.sigConst ``Codata.Signature.dtorC) σ pI t
    let value ← ctx.ofCAt L fam ctx.idx dtorC
    let xs := ctx.params ++ ctx.idx |>.push t
    let (type, value) ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
      return (← mkForallFVars xs (← ctx.fAt L T ctx.idx), ← mkLambdaFVars xs value)
    addDef ctx.dtor (← ctx.levelParamsOf [] #[type, value]) type value ctx.ref
  -- `corec` and `dtor_corec`, for a state `S` in any universe.
  let fresh := ctx.motiveLevels
  let wS := ctx.holeLevel (.param fresh[0]!)
  withLocalDecl (← ctx.userName `S) .implicit (← ctx.famType wS) fun S => do
  let FS ← ctx.fFam wS S
  withLocalDeclD `c (← ctx.famFn S FS) fun c => do
  withLocalDeclD `s (mkAppN S ctx.idx) fun s => do
  let Sp ← ctx.packFam S
  let coalg ← lam `p (← ctx.ixp) fun p => do
    let ps ← ctx.projs p
    lam `s (mkApp Sp p).headBeta fun s => do ctx.toCAt wS Sp ps (mkAppN c (ps.push s))
  let corecC := mkAppN (← ctx.sigConst ``Codata.Signature.corecC [wS]) #[σ, Sp, coalg, pI, s]
  let xs := ctx.params ++ #[S, c] ++ ctx.idx ++ #[s]
  let (type, value) ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    return (← mkForallFVars xs (← ctx.tAt ctx.idx), ← mkLambdaFVars xs corecC)
  addDef ctx.corec (← ctx.elimLevelParamsOf fresh #[type, value]) type value ctx.ref
  let corecAt (idx : Array Expr) (s : Expr) : MetaM Expr := do
    ctx.genAt ctx.corec [wS] (#[S, c] ++ idx ++ #[s])
  let dtorAt (idx : Array Expr) (t : Expr) : MetaM Expr := do
    ctx.genAt ctx.dtor [] (idx ++ #[t])
  let corecFn ← if ctx.k == 0 then
      pure (mkAppN (← ctx.constWith ctx.corec [wS]) (ctx.params ++ #[S, c]))
    else ctx.withJs fun js => do withLocalDeclD `s (mkAppN S js) fun s => do
      mkLambdaFVars (js.push s) (← corecAt js s)
  let lhs ← dtorAt ctx.idx (← corecAt ctx.idx s)
  let rhs ← ctx.mapAt wS L S T corecFn ctx.idx (mkAppN c (ctx.idx.push s))
  let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    mkForallFVars xs (← mkEq lhs rhs)
  -- The instance of `dtor_corec_of`.
  let FSp ← ctx.packFam FS
  let FTp ← ctx.packFam (← ctx.fFam L T)
  let toC ← ctx.lamP fun p => do lam `a (mkApp FSp p).headBeta fun a => do
    ctx.toCAt wS Sp (← ctx.projs p) a
  let ofCS ← ctx.lamP fun p => do lam `z (← ctx.objAt wS Sp p) fun z => do
    ctx.ofCAt wS Sp (← ctx.projs p) z
  let ofCT ← ctx.lamP fun p => do lam `z (← ctx.objAt L fam p) fun z => do
    ctx.ofCAt L fam (← ctx.projs p) z
  let fTy ← withLocalDeclD `j (← ctx.ixp) fun j => do
    mkForallFVars #[j] (← mkArrow (mkApp Sp j).headBeta (mkApp fam j))
  let map ← lam `f fTy fun f => do ctx.lamP fun p => do
    lam `a (mkApp FSp p).headBeta fun a => do ctx.mapP wS L S T f p a
  let ofC_toC ← ctx.lamP fun p => do lam `a (mkApp FSp p).headBeta fun a => do
    ctx.genAt ctx.ofC_toC [wS] (#[Sp] ++ (← ctx.projs p) ++ #[a])
  let ofC_map ← lam `f fTy fun f => do ctx.lamP fun p => do
    lam `z (← ctx.objAt wS Sp p) fun z => do
      ctx.genAt ctx.ofC_map [wS, L] (#[Sp, fam, f] ++ (← ctx.projs p) ++ #[z])
  let value ← mkAppOptM ``Codata.Signature.dtor_corec_of
    (#[σ, Sp, FSp, FTp, toC, ofCS, ofCT, map, ofC_toC, ofC_map, ← ctx.uncurryN c 1, pI, s].map some)
  let value ← mkLambdaFVars xs value
  addThm ctx.dtor_corec (← ctx.elimLevelParamsOf fresh #[type]) type value ctx.ref
  addSimp ctx.dtor_corec
  -- `bisim`
  withLocalDeclD `R (← ctx.famRel T T) fun R => do
  let HTy ← withLocalDeclD `x (← ctx.tAt ctx.idx) fun x => do
    withLocalDeclD `y (← ctx.tAt ctx.idx) fun y => do
      let rel ← ctx.relAt L L T T R ctx.idx (← dtorAt ctx.idx x) (← dtorAt ctx.idx y)
      mkForallFVars (ctx.idx ++ #[x, y]) (← mkArrow (mkAppN R (ctx.idx ++ #[x, y])) rel)
  withLocalDeclD `H HTy fun H => do
  withLocalDecl `x .implicit (← ctx.tAt ctx.idx) fun x => do
  withLocalDecl `y .implicit (← ctx.tAt ctx.idx) fun y => do
  withLocalDeclD `h (mkAppN R (ctx.idx ++ #[x, y])) fun h => do
  let xs := ctx.params ++ #[R, H] ++ ctx.idx ++ #[x, y, h]
  let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    mkForallFVars xs (← mkEq x y)
  let RTy ← withLocalDeclD `j (← ctx.ixp) fun j => do
    mkForallFVars #[j] (← mkArrow (mkApp fam j) (← mkArrow (mkApp fam j) (mkSort .zero)))
  let rel ← lam `R RTy fun R => do ctx.lamP fun p => do
    lam `a (mkApp FTp p).headBeta fun a => do lam `b (mkApp FTp p).headBeta fun b => do
      ctx.relAt L L T T (← ctx.curryN R 0) (← ctx.projs p) a b
  let rel_ofC ← lam `R RTy fun R => do ctx.lamP fun p => do
    lam `z (← ctx.objAt L fam p) fun z => do lam `z' (← ctx.objAt L fam p) fun z' => do
    let ps ← ctx.projs p
    lam `h (← ctx.relAt L L T T (← ctx.curryN R 0) ps (← ctx.ofCAt L fam ps z)
        (← ctx.ofCAt L fam ps z')) fun h => do
      ctx.genAt ctx.rel_ofC [L, L] (#[fam, fam, R] ++ ps ++ #[z, z', h])
  let value ← mkAppOptM ``Codata.Signature.bisim_of
    (#[σ, FTp, ofCT, rel, rel_ofC, ← ctx.packFam R, ← ctx.uncurryN H 3, pI, x, y, h].map some)
  addThm ctx.bisim (← ctx.levelParamsOf [] #[type]) type (← mkLambdaFVars xs value) ctx.ref

/-! ### The contract, packaged -/

/-- The fields shared by the two contracts, at the universe `L` of the type: `map`, `map_id`,
`map_comp`, for families on the packed index. -/
def mapFields (L : Level) : TermElabM (Expr × Expr × Expr) := do
  let famL ← ctx.famP L
  let fPk ← ctx.fPk L
  let fTy (X Y : Expr) : TermElabM Expr := do withLocalDeclD `j (← ctx.ixp) fun j => do
    mkForallFVars #[j] (← mkArrow (mkApp X j) (mkApp Y j))
  let map ← lam `X famL (bi := .implicit) fun X => do
    lam `Y famL (bi := .implicit) fun Y => do
    lam `f (← fTy X Y) fun f => do ctx.lamP fun p => do
    lam `a (mkApp2 fPk X p).headBeta fun a => do
      ctx.mapP L L (← ctx.curryFam X) (← ctx.curryFam Y) f p a
  let map_id ← lam `X famL (bi := .implicit) fun X => do ctx.lamP fun p => do
    lam `a (mkApp2 fPk X p).headBeta fun a => do
      ctx.genAt ctx.Fmap_id [L] (#[← ctx.curryFam X] ++ (← ctx.projs p) ++ #[a])
  let map_comp ← lam `X famL (bi := .implicit) fun X => do
    lam `Y famL (bi := .implicit) fun Y => do
    lam `Z famL (bi := .implicit) fun Z => do
    lam `g (← fTy Y Z) fun g => do lam `f (← fTy X Y) fun f => do ctx.lamP fun p => do
    lam `a (mkApp2 fPk X p).headBeta fun a => do
      ctx.genAt ctx.Fmap_comp [L, L, L] (#[← ctx.curryFam X, ← ctx.curryFam Y, ← ctx.curryFam Z,
          ← ctx.curryN g 1, ← ctx.curryN f 1] ++ (← ctx.projs p) ++ #[a])
  return (map, map_id, map_comp)

/-- `T.contract : Codata.Contract T F`, the model packaged for the framework. Its `bisim` is for
the canonical lifting, from `T.bisim` for `T.F.Rel`, which contains it by `T.F.rel_map`. -/
def genContractDef : TermElabM Unit := do
  let L ← ctx.tLvl
  let famL ← ctx.famP L
  let fPk ← ctx.fPk L
  let tPk ← ctx.packFam (← ctx.tFam)
  let (map, map_id, map_comp) ← ctx.mapFields L
  let dtor ← ctx.lamP fun p => do lam `t (mkApp tPk p).headBeta fun t => do
    ctx.genAt ctx.dtor [] ((← ctx.projs p) ++ #[t])
  let cTy (S : Expr) : TermElabM Expr := do withLocalDeclD `i (← ctx.ixp) fun i => do
    mkForallFVars #[i] (← mkArrow (mkApp S i) (mkApp2 fPk S i).headBeta)
  let corecLike (n : Name) : TermElabM Expr :=
    lam `S famL (bi := .implicit) fun S => do lam `c (← cTy S) fun c => do
    ctx.lamP fun p => do lam `s (mkApp S p) fun s => do
      ctx.genAt n [L] (#[← ctx.curryFam S, ← ctx.curryN c 1] ++ (← ctx.projs p) ++ #[s])
  let corec ← corecLike ctx.corec
  let dtor_corec ← corecLike ctx.dtor_corec
  -- `bisim`, through `bisim_canonical_of`.
  let RTy (X Y : Expr) : TermElabM Expr := do withLocalDeclD `j (← ctx.ixp) fun j => do
    mkForallFVars #[j] (← mkArrow (mkApp X j) (← mkArrow (mkApp Y j) (mkSort .zero)))
  let fTy (X Y : Expr) : TermElabM Expr := do withLocalDeclD `j (← ctx.ixp) fun j => do
    mkForallFVars #[j] (← mkArrow (mkApp X j) (mkApp Y j))
  let rel ← lam `X famL (bi := .implicit) fun X => do
    lam `Y famL (bi := .implicit) fun Y => do
    lam `R (← RTy X Y) fun R => do ctx.lamP fun p => do
    lam `a (mkApp2 fPk X p).headBeta fun a => do lam `b (mkApp2 fPk Y p).headBeta fun b => do
      ctx.relAt L L (← ctx.curryFam X) (← ctx.curryFam Y) (← ctx.curryN R 0) (← ctx.projs p) a b
  let rel_map ← lam `X famL (bi := .implicit) fun X => do
    lam `Y famL (bi := .implicit) fun Y => do
    lam `Z famL (bi := .implicit) fun Z => do
    lam `R (← RTy Y Z) fun R => do lam `f (← fTy X Y) fun f => do
    lam `g (← fTy X Z) fun g => do ctx.lamP fun p => do
    lam `a (mkApp2 fPk X p).headBeta fun a => do
    let hTy ← withLocalDeclD `j (← ctx.ixp) fun j => withLocalDeclD `x (mkApp X j) fun x => do
      mkForallFVars #[j, x] (mkAppN R #[j, mkApp2 f j x, mkApp2 g j x])
    lam `h hTy fun h => do
      ctx.genAt ctx.Frel_map [L, L, L] (#[← ctx.curryFam X, ← ctx.curryFam Y, ← ctx.curryFam Z,
          ← ctx.curryN R 0, ← ctx.curryN f 1, ← ctx.curryN g 1] ++ (← ctx.projs p) ++
          #[a, ← ctx.curryN h 1])
  let bisimT ← lam `R (← RTy tPk tPk) fun R => do
    let HTy ← withLocalDeclD `i (← ctx.ixp) fun i => do
      withLocalDeclD `x (mkApp tPk i).headBeta fun x => do
      withLocalDeclD `y (mkApp tPk i).headBeta fun y => do
        mkForallFVars #[i, x, y] (← mkArrow (mkAppN R #[i, x, y])
          (mkAppN rel #[tPk, tPk, R, i, mkApp2 dtor i x, mkApp2 dtor i y]).headBeta)
    lam `H HTy fun H => do ctx.lamP fun p => do
    lam `x (mkApp tPk p).headBeta (bi := .implicit) fun x => do
    lam `y (mkApp tPk p).headBeta (bi := .implicit) fun y => do
    lam `h (mkAppN R #[p, x, y]) fun h => do
      ctx.genAt ctx.bisim []
        (#[← ctx.curryN R 0, ← ctx.curryN H 3] ++ (← ctx.projs p) ++ #[x, y, h])
  let bisim ← mkAppOptM ``Codata.bisim_canonical_of
    (#[← ctx.ixp, tPk, fPk, map, rel, rel_map, dtor, bisimT].map some)
  let value ← mkAppOptM ``Codata.Contract.mk
    (#[← ctx.ixp, tPk, fPk, map, map_id, map_comp, dtor, corec, dtor_corec, bisim].map some)
  let type ← inferType value
  let (type, value) ← withBinderInfo ctx.params .implicit do
    return (← mkForallFVars ctx.params type, ← mkLambdaFVars ctx.params value)
  addDef ctx.contract (← ctx.levelParamsOf [] #[type, value]) type value ctx.ref

/-! ### The inductive contract -/

/-- `T.ctor`, `T.fold`, `T.fold_ctor`. -/
def genDataContract : TermElabM Unit := do
  let L ← ctx.tLvl
  let σ ← ctx.sigE
  let fam ← ctx.modelFam
  let pI ← ctx.packI
  let T ← ctx.tFam
  -- `ctor`
  withLocalDeclD `y (← ctx.fAt L T ctx.idx) fun y => do
    let value := mkApp3 (← ctx.sigConst ``Codata.Signature.ctorI) σ pI
      (← ctx.toCAt L fam ctx.idx y)
    let xs := ctx.params ++ ctx.idx |>.push y
    let (type, value) ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
      return (← mkForallFVars xs (← ctx.tAt ctx.idx), ← mkLambdaFVars xs value)
    addDef ctx.ctor (← ctx.levelParamsOf [] #[type, value]) type value ctx.ref
  -- `fold` and `fold_ctor`, into a family `S` in any universe.
  let fresh := ctx.motiveLevels
  let wS := ctx.holeLevel (.param fresh[0]!)
  withLocalDecl (← ctx.userName `S) .implicit (← ctx.famType wS) fun S => do
  let FS ← ctx.fFam wS S
  withLocalDeclD `a (← ctx.famFn FS S) fun a => do
  withLocalDeclD `t (← ctx.tAt ctx.idx) fun t => do
  let Sp ← ctx.packFam S
  let alg ← lam `p (← ctx.ixp) fun p => do
    let ps ← ctx.projs p
    lam `z (← ctx.objAt wS Sp p) fun z => do
      return mkAppN a (ps.push (← ctx.ofCAt wS Sp ps z))
  let foldI := mkAppN (← ctx.sigConst ``Codata.Signature.foldI [wS]) #[σ, Sp, alg, pI, t]
  let xs := ctx.params ++ #[S, a] ++ ctx.idx ++ #[t]
  let (type, value) ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    return (← mkForallFVars xs (mkAppN S ctx.idx), ← mkLambdaFVars xs foldI)
  addDef ctx.fold (← ctx.elimLevelParamsOf fresh #[type, value]) type value ctx.ref
  let foldAt (idx : Array Expr) (t : Expr) : MetaM Expr := do
    ctx.genAt ctx.fold [wS] (#[S, a] ++ idx ++ #[t])
  let foldFn ← if ctx.k == 0 then
      pure (mkAppN (← ctx.constWith ctx.fold [wS]) (ctx.params ++ #[S, a]))
    else ctx.withJs fun js => do withLocalDeclD `t (← ctx.tAt js) fun t => do
      mkLambdaFVars (js.push t) (← foldAt js t)
  withLocalDeclD `y (← ctx.fAt L T ctx.idx) fun y => do
  let ctorY := mkAppN (← ctx.constWith ctx.ctor []) (ctx.params ++ ctx.idx ++ #[y])
  let lhs ← foldAt ctx.idx ctorY
  let rhs := mkAppN a (ctx.idx.push (← ctx.mapAt L wS T S foldFn ctx.idx y))
  let xs := ctx.params ++ #[S, a] ++ ctx.idx ++ #[y]
  let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    mkForallFVars xs (← mkEq lhs rhs)
  -- The instance of `fold_ctor_of`.
  let FSp ← ctx.packFam FS
  let FTp ← ctx.packFam (← ctx.fFam L T)
  let toCT ← ctx.lamP fun p => do lam `y (mkApp FTp p).headBeta fun y => do
    ctx.toCAt L fam (← ctx.projs p) y
  let ofCT ← ctx.lamP fun p => do lam `z (← ctx.objAt L fam p) fun z => do
    ctx.ofCAt L fam (← ctx.projs p) z
  let ofCS ← ctx.lamP fun p => do lam `z (← ctx.objAt wS Sp p) fun z => do
    ctx.ofCAt wS Sp (← ctx.projs p) z
  let fTy ← withLocalDeclD `j (← ctx.ixp) fun j => do
    mkForallFVars #[j] (← mkArrow (mkApp fam j) (mkApp Sp j).headBeta)
  let map ← lam `f fTy fun f => do ctx.lamP fun p => do
    lam `a (mkApp FTp p).headBeta fun a => do ctx.mapP L wS T S f p a
  let ofC_toC ← ctx.lamP fun p => do lam `y (mkApp FTp p).headBeta fun y => do
    ctx.genAt ctx.ofC_toC [L] (#[fam] ++ (← ctx.projs p) ++ #[y])
  let ofC_map ← lam `f fTy fun f => do ctx.lamP fun p => do
    lam `z (← ctx.objAt L fam p) fun z => do
      ctx.genAt ctx.ofC_map [L, wS] (#[fam, Sp, f] ++ (← ctx.projs p) ++ #[z])
  let value ← mkAppOptM ``Codata.Signature.fold_ctor_of
    (#[σ, Sp, FSp, FTp, toCT, ofCT, ofCS, map, ofC_toC, ofC_map, ← ctx.uncurryN a 1, pI,
      y].map some)
  addThm ctx.fold_ctor (← ctx.elimLevelParamsOf fresh #[type]) type (← mkLambdaFVars xs value) ctx.ref
  addSimp ctx.fold_ctor

/-- `T.contract : Data.Contract T F`, the model packaged for the framework; its `induction` is
`Signature.induction_of` at the packed index. -/
def genDataContractDef : TermElabM Unit := do
  let L ← ctx.tLvl
  let σ ← ctx.sigE
  let fam ← ctx.modelFam
  let famL ← ctx.famP L
  let fPk ← ctx.fPk L
  let tPk ← ctx.packFam (← ctx.tFam)
  let (map, map_id, map_comp) ← ctx.mapFields L
  let ctor ← ctx.lamP fun p => do lam `y (mkApp2 fPk tPk p).headBeta fun y => do
    ctx.genAt ctx.ctor [] ((← ctx.projs p) ++ #[y])
  let aTy (S : Expr) : TermElabM Expr := do withLocalDeclD `i (← ctx.ixp) fun i => do
    mkForallFVars #[i] (← mkArrow (mkApp2 fPk S i).headBeta (mkApp S i))
  let foldLike (n : Name) (arg : Expr → TermElabM Expr) : TermElabM Expr :=
    lam `S famL (bi := .implicit) fun S => do lam `a (← aTy S) fun a => do
    ctx.lamP fun p => do lam `t (← arg p) fun t => do
      ctx.genAt n [L] (#[← ctx.curryFam S, ← ctx.curryN a 1] ++ (← ctx.projs p) ++ #[t])
  let fold ← foldLike ctx.fold fun p => return (mkApp tPk p).headBeta
  let fold_ctor ← foldLike ctx.fold_ctor fun p => return (mkApp2 fPk tPk p).headBeta
  -- `induction`, from `induction_of`.
  let toCT ← ctx.lamP fun p => do lam `y (mkApp2 fPk fam p).headBeta fun y => do
    ctx.toCAt L fam (← ctx.projs p) y
  let ofC ← lam `X famL (bi := .implicit) fun X => do ctx.lamP fun p => do
    lam `z (← ctx.objAt L X p) fun z => do ctx.ofCAt L X (← ctx.projs p) z
  let toC_ofC ← ctx.lamP fun p => do lam `z (← ctx.objAt L fam p) fun z => do
    ctx.genAt ctx.toC_ofC [L] (#[fam] ++ (← ctx.projs p) ++ #[z])
  let ofC_toC ← ctx.lamP fun p => do lam `y (mkApp2 fPk fam p).headBeta fun y => do
    ctx.genAt ctx.ofC_toC [L] (#[fam] ++ (← ctx.projs p) ++ #[y])
  let fTy (X Y : Expr) : TermElabM Expr := do withLocalDeclD `j (← ctx.ixp) fun j => do
    mkForallFVars #[j] (← mkArrow (mkApp X j) (mkApp Y j))
  let ofC_map ← lam `X famL (bi := .implicit) fun X => do
    lam `Y famL (bi := .implicit) fun Y => do lam `f (← fTy X Y) fun f => do
    ctx.lamP fun p => do lam `z (← ctx.objAt L X p) fun z => do
      ctx.genAt ctx.ofC_map [L, L] (#[X, Y, f] ++ (← ctx.projs p) ++ #[z])
  let induction ← mkAppOptM ``Codata.Signature.induction_of
    (#[σ, fPk, map, toCT, ofC, toC_ofC, ofC_toC, ofC_map].map some)
  let value ← mkAppOptM ``Data.Contract.mk
    (#[← ctx.ixp, tPk, fPk, map, map_id, map_comp, ctor, fold, fold_ctor, induction].map some)
  let type ← inferType value
  let (type, value) ← withBinderInfo ctx.params .implicit do
    return (← mkForallFVars ctx.params type, ← mkLambdaFVars ctx.params value)
  addDef ctx.contract (← ctx.levelParamsOf [] #[type, value]) type value ctx.ref

/-- Step 2, after the signature and the isomorphism: the type and the contract. -/
def genModel : TermElabM Unit := do
  ctx.genType
  if ctx.co then
    ctx.genContract
    ctx.genContractDef
  else
    ctx.genDataContract
    ctx.genDataContractDef

end Ctx

end Codata.Gen
