import Colean.Gen.Model

/-!
# Generators on `Expr`, step 3: instantiating the framework

*Spec.* Input: `T.contract` and the names in the context. Output: the declarations derived from
the contract alone, by instantiating `Framework.lean`: `T.ctor`, `T.dtor_ctor`, `T.ctor_dtor`, `T.ctor_injective`,
`T.corec_eq`, `T.corec_unique` for codata; `T.dtor`, `T.dtor_ctor`, `T.ctor_dtor`,
`T.ctor_injective`, `T.fold_eq`, `T.fold_unique` for data. Nothing here looks at the
constructors, and there are no proofs. `corec_eq`, `corec_unique`, `fold_eq` and `fold_unique`
are for a state or family in any universe, so they instantiate the `_of` theorems with the
contract's pieces rather than the contract itself (which fixes one universe). In a block these
are the block's, over `Blk.Ix`; the same per type, with a family per type of the block, are step
4's (`Gen/Surface.lean`), from these.
-/

open Lean Meta Elab Term

namespace Codata.Gen

namespace Ctx

variable (ctx : Ctx)

/-- The contract `T.contract params` and its implicit arguments `Ix`, `T`, `F` (packed). -/
def contractArgs : TermElabM (Array Expr) := do
  let L ← ctx.tLvl
  return #[← ctx.ixp, ← ctx.packFam (← ctx.tFam), ← ctx.fPk L,
    mkAppN (← ctx.constWith ctx.contract []) ctx.params]

/-- A field lemma of the contract at the packed index: `@K.n Ix T F contract ⟨idx⟩ args…`. -/
def contractAt (n : Name) (args : Array Expr) : TermElabM Expr := do
  mkAppOptM n ((← ctx.contractArgs).map some ++ #[some (← ctx.packI)] ++ args.map some)

/-- A definition or lemma `T.n {params} {idx} (x : ty) : stmt x := value x` over one argument
(or none). -/
def addOver (n : Name) (thm : Bool) (arg? : Option (Name × Expr))
    (stmt : Array Expr → TermElabM Expr) (value : Array Expr → TermElabM Expr) :
    TermElabM Unit := do
  let go (xs : Array Expr) : TermElabM Unit := do
    let all := ctx.params ++ ctx.idx ++ xs
    let (type, value) ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
      return (← mkForallFVars all (← stmt xs), ← mkLambdaFVars all (← value xs))
    let us ← ctx.levelParamsOf [] #[type, value]
    if thm then addThm n us type value ctx.ref else addDef n us type value ctx.ref
  match arg? with
  | some (x, ty) => withLocalDeclD x ty fun x => go #[x]
  | none => go #[]

/-- `@T.n params idx args…` for a generated constant `n` without universes of its own. -/
def appAt (n : Name) (idx args : Array Expr) : MetaM Expr := do
  ctx.genAt n [] (idx ++ args)

/-- Lambek's lemma from the contract (`K` its namespace, `Codata.Contract` or `Data.Contract`):
`ctor` (codata) or `dtor` (data), `dtor_ctor`, `ctor_dtor`, `ctor_injective`. -/
def genLambek (K : Name) : TermElabM Unit := do
  let L ← ctx.tLvl
  let T ← ctx.tFam
  let FT ← ctx.fAt L T ctx.idx
  let TI ← ctx.tAt ctx.idx
  if ctx.co then
    ctx.addOver ctx.ctor false none (fun _ => mkArrow FT TI) fun _ =>
      ctx.contractAt (K ++ `ctor) #[]
  else
    ctx.addOver ctx.dtor false (some (`t, TI)) (fun _ => pure FT) fun xs =>
      ctx.contractAt (K ++ `dtor) xs
  let ctorAt (y : Expr) := ctx.appAt ctx.ctor ctx.idx #[y]
  let dtorAt (t : Expr) := ctx.appAt ctx.dtor ctx.idx #[t]
  ctx.addOver ctx.dtor_ctor true (some (`y, FT))
    (fun xs => do mkEq (← dtorAt (← ctorAt xs[0]!)) xs[0]!)
    fun xs => ctx.contractAt (K ++ `dtor_ctor) xs
  addSimp ctx.dtor_ctor
  ctx.addOver ctx.ctor_dtor true (some (`t, TI))
    (fun xs => do mkEq (← ctorAt (← dtorAt xs[0]!)) xs[0]!)
    fun xs => ctx.contractAt (K ++ `ctor_dtor) xs
  ctx.addOver ctx.ctor_injective true none
    (fun _ => do mkAppM ``Function.Injective #[← ctx.appAt ctx.ctor ctx.idx #[]])
    fun _ => ctx.contractAt (K ++ `ctor_injective) #[]

/-- Function types on the packed index: `∀ j, X j → Y j`. -/
def fnP (X Y : Expr) : TermElabM Expr := do
  withLocalDeclD `j (← ctx.ixp) fun j => do
    mkForallFVars #[j] (← mkArrow (mkApp X j).headBeta (mkApp Y j).headBeta)

/-- `corec_eq`, `corec_unique`, for a state in any universe. -/
def genCorecLemmas : TermElabM Unit := do
  let L ← ctx.tLvl
  let T ← ctx.tFam
  let tPk ← ctx.packFam T
  let fresh := ctx.motiveLevels
  let wS := ctx.holeLevel (.param fresh[0]!)
  withLocalDecl (← ctx.userName `S) .implicit (← ctx.famType wS) fun S => do
  let FS ← ctx.fFam wS S
  withLocalDeclD `c (← ctx.famFn S FS) fun c => do
  withLocalDeclD `s (mkAppN S ctx.idx) fun s => do
  let Sp ← ctx.packFam S
  let FSp ← ctx.packFam FS
  let FTp ← ctx.packFam (← ctx.fFam L T)
  let corecAt (idx : Array Expr) (c s : Expr) : MetaM Expr := do
    ctx.genAt ctx.corec [wS] (#[S, c] ++ idx ++ #[s])
  let corecFn ← if ctx.k == 0 then
      pure (mkAppN (← ctx.constWith ctx.corec [wS]) (ctx.params ++ #[S, c]))
    else ctx.withJs fun js => do withLocalDeclD `s (mkAppN S js) fun s => do
      mkLambdaFVars (js.push s) (← corecAt js c s)
  -- The contract's pieces at the packed index, for the state `S`.
  let dtor ← ctx.lamP fun p => do lam `t (mkApp tPk p).headBeta fun t => do
    ctx.appAt ctx.dtor (← ctx.projs p) #[t]
  let cTy ← withLocalDeclD `i (← ctx.ixp) fun i => do
    mkForallFVars #[i] (← mkArrow (mkApp Sp i).headBeta (mkApp FSp i).headBeta)
  let corec ← lam `c cTy fun c => do ctx.lamP fun p => do lam `s (mkApp Sp p).headBeta fun s => do
    corecAt (← ctx.projs p) (← ctx.curryN c 1) s
  let map ← lam `f (← ctx.fnP Sp tPk) fun f => do ctx.lamP fun p => do
    lam `a (mkApp FSp p).headBeta fun a => do ctx.mapP wS L S T f p a
  let dtor_corec ← lam `c cTy fun c => do ctx.lamP fun p => do
    lam `s (mkApp Sp p).headBeta fun s => do
    ctx.genAt ctx.dtor_corec [wS] (#[S, ← ctx.curryN c 1] ++ (← ctx.projs p) ++ #[s])
  -- `corec_eq`
  do
    let lhs ← corecAt ctx.idx c s
    let rhs ← ctx.appAt ctx.ctor ctx.idx
      #[← ctx.mapAt wS L S T corecFn ctx.idx (mkAppN c (ctx.idx.push s))]
    let xs := ctx.params ++ #[S, c] ++ ctx.idx ++ #[s]
    let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do mkForallFVars xs (← mkEq lhs rhs)
    let ctor ← ctx.lamP fun p => do lam `y (mkApp FTp p).headBeta fun y => do
      ctx.appAt ctx.ctor (← ctx.projs p) #[y]
    let ctor_dtor ← ctx.lamP fun p => do lam `t (mkApp tPk p).headBeta fun t => do
      ctx.appAt ctx.ctor_dtor (← ctx.projs p) #[t]
    let value ← mkAppOptM ``Codata.corec_eq_of (#[← ctx.ixp, tPk, Sp, FSp, FTp, dtor, ctor, corec,
      map, dtor_corec, ctor_dtor, ← ctx.uncurryN c 1, ← ctx.packI, s].map some)
    addThm ctx.corec_eq (← ctx.elimLevelParamsOf fresh #[type]) type (← mkLambdaFVars xs value)
      ctx.ref
  -- `corec_unique`
  withLocalDeclD `h (← ctx.famFn S T) fun h => do
  let hhTy ← withLocalDeclD `s (mkAppN S ctx.idx) fun s => do
    mkForallFVars (ctx.idx.push s)
      (← mkEq (← ctx.appAt ctx.dtor ctx.idx #[mkAppN h (ctx.idx.push s)])
      (← ctx.mapAt wS L S T h ctx.idx (mkAppN c (ctx.idx.push s))))
  withLocalDeclD `hh hhTy fun hh => do
  let xs := ctx.params ++ #[S, c, h, hh] ++ ctx.idx ++ #[s]
  let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    mkForallFVars xs (← mkEq (mkAppN h (ctx.idx.push s)) (← corecAt ctx.idx c s))
  let RTy ← withLocalDeclD `j (← ctx.ixp) fun j => do
    let Tj := (mkApp tPk j).headBeta
    mkForallFVars #[j] (← mkArrow Tj (← mkArrow Tj (mkSort .zero)))
  let rel ← lam `R RTy fun R => do ctx.lamP fun p => do
    lam `a (mkApp FTp p).headBeta fun a => do lam `b (mkApp FTp p).headBeta fun b => do
      ctx.relAt L L T T (← ctx.curryN R 0) (← ctx.projs p) a b
  -- `bisim` at the packed index, from `T.bisim` with its curried arguments.
  let bisim ← lam `R RTy fun R => do
    let HTy ← withLocalDeclD `i (← ctx.ixp) fun i => do
      withLocalDeclD `x (mkApp tPk i).headBeta fun x => do
      withLocalDeclD `y (mkApp tPk i).headBeta fun y => do
        mkForallFVars #[i, x, y] (← mkArrow (mkAppN R #[i, x, y])
          (mkAppN rel #[R, i, mkApp2 dtor i x, mkApp2 dtor i y]).headBeta)
    lam `H HTy fun H => do ctx.lamP fun p => do
    lam `x (mkApp tPk p).headBeta (bi := .implicit) fun x => do
    lam `y (mkApp tPk p).headBeta (bi := .implicit) fun y => do
    lam `h (mkAppN R #[p, x, y]) fun h => do
      ctx.genAt ctx.bisim []
        (#[← ctx.curryN R 0, ← ctx.curryN H 3] ++ (← ctx.projs p) ++ #[x, y, h])
  let rel_map ← lam `R RTy fun R => do lam `f (← ctx.fnP Sp tPk) fun f => do
    lam `g (← ctx.fnP Sp tPk) fun g => do ctx.lamP fun p => do
    lam `a (mkApp FSp p).headBeta fun a => do
    let hTy ← withLocalDeclD `j (← ctx.ixp) fun j => do
      withLocalDeclD `x (mkApp Sp j).headBeta fun x => do
        mkForallFVars #[j, x] (mkAppN R #[j, mkApp2 f j x, mkApp2 g j x])
    lam `h hTy fun h => do
      ctx.genAt ctx.Frel_map [wS, L, L]
        (#[S, T, T, ← ctx.curryN R 0, ← ctx.curryN f 1, ← ctx.curryN g 1] ++
          (← ctx.projs p) ++ #[a, ← ctx.curryN h 1])
  let value ← mkAppOptM ``Codata.corec_unique_of (#[← ctx.ixp, tPk, Sp, FSp, FTp, dtor, corec, map,
    rel, bisim, dtor_corec, rel_map, ← ctx.uncurryN c 1, ← ctx.uncurryN h 1,
    ← ctx.uncurryN hh 1, ← ctx.packI, s].map some)
  addThm ctx.corec_unique (← ctx.elimLevelParamsOf fresh #[type]) type (← mkLambdaFVars xs value)
    ctx.ref

/-- `fold_eq`, `fold_unique`, for a family in any universe. -/
def genFoldLemmas : TermElabM Unit := do
  let L ← ctx.tLvl
  let T ← ctx.tFam
  let tPk ← ctx.packFam T
  let fPk ← ctx.fPk L
  let fresh := ctx.motiveLevels
  let wS := ctx.holeLevel (.param fresh[0]!)
  withLocalDecl (← ctx.userName `S) .implicit (← ctx.famType wS) fun S => do
  let FS ← ctx.fFam wS S
  withLocalDeclD `a (← ctx.famFn FS S) fun a => do
  withLocalDeclD `t (← ctx.tAt ctx.idx) fun t => do
  let Sp ← ctx.packFam S
  let FSp ← ctx.packFam FS
  let FTp ← ctx.packFam (← ctx.fFam L T)
  let foldAt (idx : Array Expr) (a t : Expr) : MetaM Expr := do
    ctx.genAt ctx.fold [wS] (#[S, a] ++ idx ++ #[t])
  let foldFn ← if ctx.k == 0 then
      pure (mkAppN (← ctx.constWith ctx.fold [wS]) (ctx.params ++ #[S, a]))
    else ctx.withJs fun js => do withLocalDeclD `t (← ctx.tAt js) fun t => do
      mkLambdaFVars (js.push t) (← foldAt js a t)
  let aTy ← withLocalDeclD `i (← ctx.ixp) fun i => do
    mkForallFVars #[i] (← mkArrow (mkApp FSp i).headBeta (mkApp Sp i).headBeta)
  let fold ← lam `a aTy fun a => do ctx.lamP fun p => do lam `t (mkApp tPk p).headBeta fun t => do
    foldAt (← ctx.projs p) (← ctx.curryN a 1) t
  let fold_ctor ← lam `a aTy fun a => do ctx.lamP fun p => do
    lam `y (mkApp FTp p).headBeta fun y => do
      ctx.genAt ctx.fold_ctor [wS] (#[S, ← ctx.curryN a 1] ++ (← ctx.projs p) ++ #[y])
  let ctor ← ctx.lamP fun p => do lam `y (mkApp FTp p).headBeta fun y => do
    ctx.appAt ctx.ctor (← ctx.projs p) #[y]
  -- `fold_eq`
  do
    let rhs := mkAppN a (ctx.idx.push
      (← ctx.mapAt L wS T S foldFn ctx.idx (← ctx.appAt ctx.dtor ctx.idx #[t])))
    let xs := ctx.params ++ #[S, a] ++ ctx.idx ++ #[t]
    let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
      mkForallFVars xs (← mkEq (← foldAt ctx.idx a t) rhs)
    let dtor ← ctx.lamP fun p => do lam `t (mkApp tPk p).headBeta fun t => do
      ctx.appAt ctx.dtor (← ctx.projs p) #[t]
    let map ← lam `f (← ctx.fnP tPk Sp) fun f => do ctx.lamP fun p => do
      lam `a (mkApp FTp p).headBeta fun a => do ctx.mapP L wS T S f p a
    let ctor_dtor ← ctx.lamP fun p => do lam `t (mkApp tPk p).headBeta fun t => do
      ctx.appAt ctx.ctor_dtor (← ctx.projs p) #[t]
    let value ← mkAppOptM ``Data.fold_eq_of (#[← ctx.ixp, tPk, Sp, FSp, FTp, dtor, ctor, fold, map,
      fold_ctor, ctor_dtor, ← ctx.uncurryN a 1, ← ctx.packI, t].map some)
    addThm ctx.fold_eq (← ctx.elimLevelParamsOf fresh #[type]) type (← mkLambdaFVars xs value) ctx.ref
  -- `fold_unique`
  withLocalDeclD `h (← ctx.famFn T S) fun h => do
  let hhTy ← withLocalDeclD `y (← ctx.fAt L T ctx.idx) fun y => do
    mkForallFVars (ctx.idx.push y)
      (← mkEq (mkAppN h (ctx.idx.push (← ctx.appAt ctx.ctor ctx.idx #[y])))
      (mkAppN a (ctx.idx.push (← ctx.mapAt L wS T S h ctx.idx y))))
  withLocalDeclD `hh hhTy fun hh => do
  let xs := ctx.params ++ #[S, a, h, hh] ++ ctx.idx ++ #[t]
  let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    mkForallFVars xs (← mkEq (mkAppN h (ctx.idx.push t)) (← foldAt ctx.idx a t))
  let (map, _, _) ← ctx.mapFields L
  let famL ← ctx.famP L
  let induction ← mkAppOptM ``Data.Contract.induction ((← ctx.contractArgs).map some)
  let mapS ← lam `X famL (bi := .implicit) fun X => do lam `f (← ctx.fnP X Sp) fun f => do
    ctx.lamP fun p => do lam `a (mkApp2 fPk X p).headBeta fun a => do
      ctx.mapP L wS (← ctx.curryFam X) S f p a
  let mapS_map ← lam `X famL (bi := .implicit) fun X => do lam `g (← ctx.fnP tPk Sp) fun g => do
    lam `f (← ctx.fnP X tPk) fun f => do ctx.lamP fun p => do
    lam `z (mkApp2 fPk X p).headBeta fun z => do
      ctx.genAt ctx.Fmap_comp [L, L, wS]
        (#[← ctx.curryFam X, T, S, ← ctx.curryN g 1, ← ctx.curryN f 1] ++
          (← ctx.projs p) ++ #[z])
  let value ← mkAppOptM ``Data.fold_unique_of (#[← ctx.ixp, tPk, Sp, FSp, fPk, map, ctor,
    induction, fold, mapS, fold_ctor, mapS_map, ← ctx.uncurryN a 1, ← ctx.uncurryN h 1,
    ← ctx.uncurryN hh 1, ← ctx.packI, t].map some)
  addThm ctx.fold_unique (← ctx.elimLevelParamsOf fresh #[type]) type (← mkLambdaFVars xs value) ctx.ref

/-- Step 3. -/
def genFramework : TermElabM Unit := do
  if ctx.co then
    ctx.genLambek ``Codata.Contract
    ctx.genCorecLemmas
  else
    ctx.genLambek ``Data.Contract
    ctx.genFoldLemmas

end Ctx

end Codata.Gen
