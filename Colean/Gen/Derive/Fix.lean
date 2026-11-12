import Colean.Gen.Derive.Layer

/-!
# Generators on `Expr`, step 5: the fixpoint and the instances

`T.Poly.fix`, from the contract by the theorems of `Model/Poly.lean`, and the instances
`PolyIso`, `PolyMap` of the types, with their eta forms.
-/

open Lean Meta Elab Term

namespace Codata.Gen

namespace Ctx

variable (ctx : Ctx)

/-! ### The fixpoint and the instances -/

/-- With indices, `T.Poly.fix (X) : IPolyFix P tree X (fun i => T (H X) (ι i))`: `icoFix`
(`iinFix`), whose `corec` (`fold`) on states over the index of the presentation is the type's on
the states `Along ι St` (`Over ι St`) over its own index, and the bisimulation (induction)
principle from the contract along `ι` (`ico_bisim`, `iin_ind`). The proof arguments are `rw` on
goal metavariables, as without indices. -/
def genIPolyFix (P : Poly) : TermElabM Unit := do
  let L ← ctx.tLvl
  let pX (X : Expr) := ctx.polyParams P P.Hs X
  -- The layers maps composed by the states (`Along`, `Over`) are the expected ones by unfolding:
  -- `rfl` after the rewriting.
  let rwTac (steps : Array (Bool × Name)) := rwSteps steps (close := true)
  let σE ← ctx.polySig P
  let Pc ← ctx.polyP P
  withLocalDeclD `X (mkSort P.lx.succ) fun X => do
  -- The type at the premises, curried, and as a family over the index of the presentation.
  let T := mkAppN (← ctx.constWith ctx.name []) (pX X)
  let TI ← ctx.polyLayFam P P.Hs X T
  let I' := P.subX P.Hs X (← ctx.ixp)
  let ιf ← lam `j P.I fun j => ctx.polyIota P P.Hs X j
  let idxAt (i : Expr) : MetaM (Array Expr) := do ctx.projs (← ctx.polyIota P P.Hs X i)
  let yL (w : Level) := [(P.fresh[2]!, w)]
  let toL (Y i a : Expr) (w : Level) := ctx.polyAt P "toL" (yL w) #[X, Y, i, a]
  let ofL (Y i z : Expr) (w : Level) := ctx.polyAt P "ofL" (yL w) #[X, Y, i, z]
  let dtorAt (i t : Expr) : MetaM Expr := do
    return mkAppN (← ctx.constWith ctx.dtor []) (pX X ++ (← idxAt i) |>.push t)
  let dL ← lam `i P.I (bi := .implicit) fun i => do
    lam `a (mkApp TI i).headBeta fun a => do toL T i (← dtorAt i a) L
  let K := mkAppN (← ctx.constWith ctx.contract []) (pX X)
  -- The layer on families over `I'`, the contract's, curried for `T.F`.
  let curry (Y : Expr) : TermElabM Expr := do return P.subX P.Hs X (← ctx.curryFam Y)
  let ofLz (ty : Expr) : TermElabM Expr := lamOf ty fun xs => do
    ofL (← curry xs[0]!) xs[1]! xs[2]! (← famLevel xs[0]!)
  let toLz (ty : Expr) : TermElabM Expr := lamOf ty fun xs => do
    toL (← curry xs[0]!) xs[1]! xs[2]! (← famLevel xs[0]!)
  let ofL_toL (Y i a : Expr) : TermElabM Expr := do
    ctx.polyAt P "ofL_toL" (yL (← famLevel Y)) #[X, Y, i, a]
  let ofL_map (ty : Expr) : TermElabM Expr := lamOf ty fun xs => do
    ctx.polyAt P "ofL_map" [(P.fresh[2]!, ← famLevel xs[0]!), (P.fresh[3]!, ← famLevel xs[1]!)]
      #[X, ← curry xs[0]!, ← curry xs[1]!, P.subX P.Hs X (← ctx.curryN xs[2]! 1), xs[3]!, xs[4]!]
  -- `T.F (H X) Y` over `I'`, for the states.
  let FOn (Y : Expr) (w : Level) : TermElabM Expr := lam `j I' fun j => do
    return mkAppN (← ctx.polyF P X Y w) (← ctx.projs j)
  let value ← withUnfolding do
    if ctx.co then
      let f ← mkAppOptM ``Codata.icoFix #[σE, Pc, X, TI, dL]
      let f ← fillArg f fun ty => lamOf ty fun xs => do
        let (St, c, i, s) := (xs[0]!, xs[1]!, xs[2]!, xs[3]!)
        let lSt ← famLevel St
        let Al ← mkAppOptM ``Codata.Along #[σE, I', ιf, St]
        let AlC ← curry Al
        let ofL' ← lam `i P.I (bi := .implicit) fun i => do
          lam `z (← ctx.polyILay P X AlC i) fun z => ofL AlC i z lSt
        let co ← mkAppOptM ``Codata.Along.coalg
          #[σE, Pc, X, I', ιf, St, ← FOn AlC lSt, ofL', c]
        let mk ← mkAppOptM ``Codata.Along.mk #[σE, I', ιf, St, i, s]
        return mkAppN (← ctx.constWith ctx.corec [lSt])
          (pX X ++ #[AlC, P.subX P.Hs X (← ctx.curryN co 1)] ++ (← idxAt i) |>.push mk)
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.dtor_corec), (false, ``Codata.Along.coalg_mk),
          (true, ctx.polyName "ofL_map"), (false, ctx.polyName "toL_ofL")])
      let bis ← mkAppFirst ``Codata.ico_bisim #[σE, Pc, X] 6
      let bis ← fillArg bis fun _ => pure K
      let bis ← fillArg bis fun _ => pure ιf
      let bis ← fillArg bis fun _ => pure dL
      let bis ← fillArg bis ofLz
      let bis ← fillArg bis fun ty => lamOf ty fun xs => do
        ofL_toL T xs[0]! (← dtorAt xs[0]! xs[1]!)
      let bis ← fillArg bis ofL_map
      fillArg f fun _ => pure bis
    else
      let ctorL ← lam `i P.I (bi := .implicit) fun i => do
        lam `z (← ctx.polyILay P X T i) fun z => do
          return mkAppN (← ctx.constWith ctx.ctor []) (pX X ++ (← idxAt i) |>.push
            (← ofL T i z L))
      let f ← mkAppOptM ``Codata.iinFix #[σE, Pc, X, TI, ctorL, dL]
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.dtor_ctor), (false, ctx.polyName "toL_ofL")])
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.polyName "ofL_toL"), (false, ctx.ctor_dtor)])
      let f ← fillArg f fun ty => lamOf ty fun xs => do
        let (St, a, i, t) := (xs[0]!, xs[1]!, xs[2]!, xs[3]!)
        let lSt ← famLevel St
        let Ov ← mkAppOptM ``Codata.Over #[σE, I', ιf, St]
        let OvC ← curry Ov
        let toL' ← lam `i P.I (bi := .implicit) fun i => do
          lam `y (← ctx.polyFI P X OvC i lSt) fun y => toL OvC i y lSt
        let alg ← mkAppOptM ``Codata.Over.alg #[σE, Pc, X, I', ιf, St, ← FOn OvC lSt, toL', a]
        let folded := mkAppN (← ctx.constWith ctx.fold [lSt])
          (pX X ++ #[OvC, P.subX P.Hs X (← ctx.curryN alg 1)] ++ (← idxAt i) |>.push t)
        return mkApp2 folded i (← mkEqRefl (← ctx.polyIota P P.Hs X i))
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.fold_ctor), (false, ``Codata.Over.alg_apply),
          (true, ctx.polyName "ofL_map"), (false, ctx.polyName "toL_ofL")])
      let ind ← mkAppFirst ``Codata.iin_ind #[σE, Pc, X] 6
      let ind ← fillArg ind fun _ => pure K
      let ind ← fillArg ind fun _ => pure ιf
      let ind ← fillArg ind toLz
      let ind ← fillArg ind ofLz
      let ind ← fillArg ind fun ty => lamOf ty fun xs => do
        ofL_toL (← curry xs[0]!) xs[1]! xs[2]!
      let ind ← fillArg ind ofL_map
      fillArg f fun _ => pure ind
  let value ← instantiateMVars value
  ctx.addPolyDef P "fix" (P.premises.push X) (← inferType value) value

/-- `T.Poly.fix (X) : PolyFix P tree X (T (H X))`, from the public declarations of the type:
`coFix` (`inFix` for `data`), its proof arguments by `rw` on goal metavariables, and the
bisimulation (induction) principle from the contract (`co_bisim`, `in_ind`). -/
def genPolyFix (P : Poly) : TermElabM Unit := do
  if ctx.idxed then return ← ctx.genIPolyFix P
  let L ← ctx.tLvl
  let pX (X : Expr) := ctx.polyParams P P.Hs X
  let rwTac (steps : Array (Bool × Name)) := rwSteps steps
  withLocalDeclD `X (mkSort P.lx.succ) fun X => do
  let TX := mkAppN (← ctx.constWith ctx.name []) (pX X)
  let yL (w : Level) := [(P.fresh[2]!, w)]
  let toL (Y a : Expr) (w : Level) := ctx.polyAt P "toL" (yL w) #[X, Y, a]
  let ofL (Y z : Expr) (w : Level) := ctx.polyAt P "ofL" (yL w) #[X, Y, z]
  let dtorAt (t : Expr) : MetaM Expr := return mkAppN (← ctx.constWith ctx.dtor []) (pX X |>.push t)
  let dL ← lam `a TX fun a => do toL TX (← dtorAt a) L
  let K := mkAppN (← ctx.constWith ctx.contract []) (pX X)
  let ofLz (ty : Expr) : TermElabM Expr := lamOf ty fun xs => do
    ofL xs[0]! xs[1]! (← typeLevel xs[0]!)
  let ofL_toL (Y a : Expr) : TermElabM Expr := do
    ctx.polyAt P "ofL_toL" (yL (← typeLevel Y)) #[X, Y, a]
  let ofL_map (ty : Expr) : TermElabM Expr := lamOf ty fun xs => do
    ctx.polyAt P "ofL_map" [(P.fresh[2]!, ← typeLevel xs[0]!), (P.fresh[3]!, ← typeLevel xs[1]!)]
      (#[X] ++ xs)
  let value ← withUnfolding do
    if ctx.co then
      let f ← mkAppOptM ``Codata.coFix #[none, none, none, none, none, dL]
      let f ← fillArg f fun ty => lamOf ty fun xs => do
        let (St, c, s) := (xs[0]!, xs[1]!, xs[2]!)
        let lSt ← typeLevel St
        let c' ← lam `st St fun st => ofL St (mkApp c st) lSt
        return mkAppN (← ctx.constWith ctx.corec [lSt]) (pX X ++ #[St, c', s])
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.dtor_corec), (true, ctx.polyName "ofL_map"),
          (false, ctx.polyName "toL_ofL")])
      let bis ← fillArg (← mkAppMVars ``Codata.co_bisim 6) fun _ => pure K
      let bis ← fillArg bis fun _ => pure dL
      let bis ← fillArg bis ofLz
      let bis ← fillArg bis fun ty => lamOf ty fun xs => do ofL_toL TX (← dtorAt xs[0]!)
      let bis ← fillArg bis ofL_map
      fillArg f fun _ => pure bis
    else
      let ctorL ← lam `z (← ctx.polyLay P X TX) fun z => do
        return mkAppN (← ctx.constWith ctx.ctor []) (pX X |>.push (← ofL TX z L))
      let f ← mkAppOptM ``Codata.inFix #[none, none, none, none, none, ctorL, dL]
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.dtor_ctor), (false, ctx.polyName "toL_ofL")])
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.polyName "ofL_toL"), (false, ctx.ctor_dtor)])
      let f ← fillArg f fun ty => lamOf ty fun xs => do
        let (St, a, t) := (xs[0]!, xs[1]!, xs[2]!)
        let lSt ← typeLevel St
        let a' ← lam `y (← ctx.polyF P X St lSt) fun y => do return mkApp a (← toL St y lSt)
        return mkAppN (← ctx.constWith ctx.fold [lSt]) (pX X ++ #[St, a', t])
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.fold_ctor), (true, ctx.polyName "ofL_map"),
          (false, ctx.polyName "toL_ofL")])
      let ind ← fillArg (← mkAppMVars ``Codata.in_ind 6) fun _ => pure K
      let ind ← fillArg ind fun ty => lamOf ty fun xs => do toL xs[0]! xs[1]! (← typeLevel xs[0]!)
      let ind ← fillArg ind ofLz
      let ind ← fillArg ind fun ty => lamOf ty fun xs => ofL_toL xs[0]! xs[1]!
      let ind ← fillArg ind ofL_map
      fillArg f fun _ => pure ind
  let value ← instantiateMVars value
  ctx.addPolyDef P "fix" (P.premises.push X) (← inferType value) value

/-- `T.Poly.fix` at the premises `Hs` (with their instances `insts`) and `X`, at the universes
`σ`. -/
def polyFixAt (P : Poly) (σ : List (Name × Level)) (Hs insts : Array Expr) (X : Expr) :
    MetaM Expr := do
  return mkAppN (← polyConst (ctx.polyName "fix") σ) (P.consts ++ Hs ++ P.SR ++ insts |>.push X)

/-- Add the instance `n` of type `type` with value `value`, closed over `xs`. -/
def addPolyInstance (P : Poly) (n : Name) (xs : Array Expr) (type value : Expr) :
    TermElabM Unit := do
  let (type, value) ← withBinderInfo (P.consts ++ P.Hs ++ P.Hs' ++ P.SR) .implicit do
    return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  addDef n (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref
  registerInstance n .global (eval_prio default)

/-- When the last parameter is the last hole, the instances `T.Poly.instPolyIsoEta`,
`T.Poly.instPolyMapEta` for `T a₁ … aₙ₋₁` itself, a type `T` without indices: `fun X => T a X` is
`T a`, the instances at the identity in the last parameter, the other holes constant. -/
def genPolyEta (P : Poly) (T : Name) : TermElabM Unit := do
  let isoN := T ++ `Poly ++ `instPolyIso
  let mapN := T ++ `Poly ++ `instPolyMap
  let some last := ctx.params.back? | return
  unless P.holes.back? == some last do return
  let others := P.holes.pop
  let lastLvl ← typeLevel last
  let lastTy ← inferType last
  let idH ← lam `X lastTy fun X => pure X
  let etaHs ← others.mapM fun a => lam `X lastTy fun _ => pure a
  let etaSR ← others.mapM fun a => do
    return #[a, ← lam `x a fun _ => pure (Lean.mkConst ``Empty)]
  let etaSR := etaSR.flatten ++
    #[Lean.mkConst ``Unit, ← lam `x (Lean.mkConst ``Unit) fun _ => pure (Lean.mkConst ``Unit)]
  let etaHs := etaHs.push idH
  let synth (Hs : Array Expr) : TermElabM (Array Expr) :=
    (Array.range Hs.size).mapM fun i => do
      synthInstance (← mkAppM ``Codata.PolyIso #[Hs[i]!, etaSR[2 * i]!, etaSR[2 * i + 1]!])
  let insts ← synth etaHs
  -- The universes of the instances at these premises.
  let levelsOf (es : Array Expr) : MetaM (List (Name × Level)) := do
    let mut σ := [(P.fresh[0]!, lastLvl)]
    for i in [0:P.holes.size] do
      σ := σ ++ [(P.fresh[5 + 2 * i]!, ← typeLevel es[2 * i]!), (P.fresh[6 + 2 * i]!, Level.zero)]
    return σ
  let σ ← levelsOf etaSR
  let isoE := mkAppN (← polyConst isoN σ) (P.consts ++ etaHs ++ etaSR ++ insts)
  -- The functors `fun X => T a X` of the types, eta-reduced.
  let etaType (ty : Expr) : Expr :=
    mkAppN ty.getAppFn (ty.getAppArgs.modify 0 Expr.eta |>.modify 1 Expr.eta)
  ctx.addPolyInstance P (T ++ `Poly ++ `instPolyIsoEta) (P.consts ++ others)
    (etaType (← whnfR (← inferType isoE))) isoE
  -- Across universes only when the universe of the last parameter is its own: a level in one
  -- universe parameter (`u`, `u + 1`, `max u 1`) that no other parameter's type mentions.
  let own? ← match (collectLevelParams {} (mkSort lastLvl)).params.toList with
    | [u] => do
      let shared ← others.anyM fun a => do
        return (collectLevelParams {} (← inferType a)).params.contains u
      pure (if !P.primes.any (·.1 == u) || shared then none else some u)
    | _ => pure none
  -- The primed universes of `instPolyMap`: that of the last parameter, if it is its own, the
  -- others unprimed (the other holes are fixed).
  let lastLvl' := match own? with
    | some u => lastLvl.instantiateParams [u] [P.lvl 4]
    | none => lastLvl
  let σu := P.primes.filterMap fun (v, v') => match v' with
    | .param n => some (n, if own? == some v then P.lvl 4 else .param v)
    | _ => none
  let idH' ← lam `X (mkSort lastLvl'.succ) fun X => pure X
  let etaHs' := (← others.mapM fun a => lam `X (mkSort lastLvl'.succ) fun _ => pure a).push idH'
  let insts' ← synth etaHs'
  -- The premises' maps: of the identity and of constants.
  let maps ← (Array.range etaHs.size).mapM fun i => do
    synthInstance (← mkAppOptM ``Codata.PolyMap (#[etaHs[i]!, etaHs'[i]!, etaSR[2 * i]!,
      etaSR[2 * i + 1]!, insts[i]!, insts'[i]!].map some))
  let σm := σ ++ [(P.fresh[1]!, lastLvl')] ++ σu
  let mapE := mkAppN (← polyConst mapN σm)
    (P.consts ++ etaHs ++ etaHs' ++ etaSR ++ insts ++ insts' ++ maps)
  let mapTy ← whnfR (← inferType mapE)
  ctx.addPolyInstance P (T ++ `Poly ++ `instPolyMapEta) (P.consts ++ others)
    (etaType mapTy) mapE

/-- For each type `Tₘ` (the type, the family, or the types of a block) at its indices `idx`, which
are arguments of the instances: `Tₘ.Poly.instPolyIso` for `fun X => Tₘ (H X) idx`, at the trees of
shapes (with indices at its index `i` of the presentation, `⟨idx⟩` or `Blk.Poly.Ix.Tₘ idx`), and
`Tₘ.Poly.instPolyMap`; when the last parameter is the last hole, for a type without indices, the
instances `Tₘ.Poly.instPolyIsoEta`, `Tₘ.Poly.instPolyMapEta` for `Tₘ a₁ … aₙ₋₁` itself
(`genPolyEta`). -/
def genPolyInstances (P : Poly) : TermElabM Unit := do
  let fam := if ctx.co then ``Codata.Signature.Cotype else ``Codata.Signature.Intype
  for m in [0:ctx.types.size] do
    let t := ctx.types[m]!
    -- The trees of shapes and their paths; with indices at the index `i` of the type.
    let (W, path, i?) ← if ctx.idxed then do
        let σE ← ctx.polySig P
        let tree ← mkAppM (if ctx.co then ``Codata.coITree else ``Codata.inITree) #[σE]
        let i ← ctx.polyIdx P (ctx.wrap m t.idx)
        pure (← mkAppM fam #[σE, i], ← mkAppOptM ``Codata.IPath #[σE, ← ctx.polyP P, none, tree, i],
          some i)
      else do
        let B ← ctx.polyB P
        let tree ← mkAppM (if ctx.co then ``Codata.coTree else ``Codata.inTree) #[B]
        pure (← mkAppM fam #[← mkAppOptM ``Codata.shapeSig #[none, B], mkConst ``Unit.unit],
          ← mkAppM ``Codata.Path #[← ctx.polyP P, tree], none)
    -- The functor `fun X => Tₘ (H X) idx`, and at the primed universes `fun X => Tₘ (H' X) idx`.
    let Tc ← ctx.constWith t.name []
    let funT ← lam `X (mkSort P.lx.succ) fun X =>
      return mkAppN Tc (ctx.polyParams P P.Hs X ++ t.idx)
    let funT' ← lam `X (mkSort P.lx'.succ) fun X =>
      return mkAppN (P.prime Tc) (ctx.polyParams P P.Hs' X ++ t.idx)
    let isoN := t.name ++ `Poly ++ `instPolyIso
    let mapN := t.name ++ `Poly ++ `instPolyMap
    -- `PolyIso`
    do
      let equiv ← lam `X (mkSort P.lx.succ) (bi := .implicit) fun X => do
        let M ← ctx.polyFixAt P [] P.Hs P.insts X
        match i? with
        | some i => mkAppOptM ``Codata.IPolyFix.equiv #[none, none, none, none, none, none, M, i]
        | none => mkAppM ``Codata.PolyFix.equiv #[M]
      let value ← mkAppOptM ``Codata.PolyIso.mk #[funT, W, path, equiv]
      ctx.addPolyInstance P isoN (P.premises ++ t.idx) (← mkAppM ``Codata.PolyIso #[funT, W, path])
        value
    -- `PolyMap`
    do
      let iso := mkAppN (← polyConst isoN) (P.premises ++ t.idx)
      let σ' := (P.fresh[0]!, P.lx') :: P.primes
      let iso' := mkAppN (← polyConst isoN σ') (P.consts ++ P.Hs' ++ P.SR ++ P.insts' ++ t.idx)
      let mp ← mkAppOptM ``Codata.PolyMap.mk #[funT, funT', W, path, iso, iso']
      -- `PolyFix.map M M' f x` (`n`), with indices `IPolyFix.map` at `i` (`n'`); `equiv_map`.
      let along (n n' : Name) (xs : Array Expr) : TermElabM Expr := do
        let M ← ctx.polyFixAt P [] P.Hs P.insts xs[0]!
        let M' ← ctx.polyFixAt P σ' P.Hs' P.insts' xs[1]!
        match i? with
        | some i =>
          mkAppOptM n' #[none, none, none, none, none, none, M, none, none, M', xs[2]!, i, xs[3]!]
        | none => mkAppM n #[M, M', xs[2]!, xs[3]!]
      let mp ← fillArg mp fun ty => lamOf ty (along ``Codata.PolyFix.map ``Codata.IPolyFix.map)
      let mp ← withUnfolding <| fillArg mp fun ty =>
        lamOf ty (along ``Codata.PolyFix.equiv_map ``Codata.IPolyFix.equiv_map)
      let xs := P.consts ++ P.Hs ++ P.Hs' ++ P.SR ++ P.insts ++ P.insts' ++ P.maps ++ t.idx
      ctx.addPolyInstance P mapN xs (← inferType mp) (← instantiateMVars mp)
    if t.idx.isEmpty then ctx.genPolyEta P t.name

end Ctx

end Codata.Gen
