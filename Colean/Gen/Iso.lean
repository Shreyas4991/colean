import Colean.Gen.Signature

/-!
# Generators on `Expr`, step 2: the isomorphism

*Spec.* Input: the context, `T.F` and the signature. Output: the isomorphism between `F` and the
signature's layers, for a family `X` on the packed index:

* `T.toC : T.F params X' idx → (T.sig params).Obj X ⟨idx⟩` and `T.ofC` back, where `X'` is `X`
  curried (`curryFam`);
* their laws `T.ofC_toC`, `T.toC_ofC`, `T.ofC_map`, and for `codata` `T.rel_ofC` (stated with
  `T.F.Rel`, `Gen/Rel.lean`).

`toC` is by cases on `F`; the children of a layer are by cases on the position (`casesPos`), at
its shape `Shape.c d` and the constructor's index, in general position: the position is
eliminated at variables, and the equation of the shapes is solved before those of the indices,
which then hold by definition. So a result index need not be a pattern (`T (n * 2)`), where
`MVarId.cases` would have to invert it. The laws eliminate positions the same way. The
layers of the nested arguments are bound by a lambda, `(fun z => ⟨Shape.c d z.1, …⟩) (toC o x)`,
so that the children are parametric in them and `toC_ofC` can rewrite them. `ofC` is by cases on
the shape. The laws are proved on goal metavariables: by cases, then `rfl`; for nested arguments
the goal is first unfolded (`whnf`), then rewritten with the laws of `Model/Occ.lean` (for
`ofC_map` with the unfolding of Lean before 4.34, `withUnfolding`: a child's type
`X (sig.idx b)` is the index of the structure only after unfolding).
-/

open Lean Meta Elab Term

namespace Codata.Gen

/-! ### Case analysis on positions -/

/-- A proof of the equation `eq` (`x = x'` or `x ≍ x'`): `rfl` if its sides are definitionally
equal, else one of the hypotheses `hs` with these sides. -/
def eqProof (eq : Expr) (hs : Array Expr) : MetaM Expr := do
  let sides (e : Expr) : Option (Expr × Expr × Bool) :=
    match e.heq?, e.eq? with
    | some (_, x, _, x'), _ => some (x, x', true)
    | _, some (_, x, x') => some (x, x', false)
    | _, _ => none
  let some (x, x', heq) := sides eq
    | throwError "internal error: expected an equation, got{indentExpr eq}"
  if ← isDefEq x x' then return ← if heq then mkHEqRefl x else mkEqRefl x
  for h in hs do
    let some (a, a', hheq) := sides (← whnfR (← inferType h)) | continue
    if ← isDefEq x a <&&> isDefEq x' a' then
      return ← if heq == hheq then pure h else if heq then mkHEqOfEq h else mkEqOfHEq h
  throwError "internal error: no proof of{indentExpr eq}"

/-- `MVarId.cases` on a position `b : T.B params idx s` whose shape `s` is a constructor
application, in general position: `b` is eliminated at variables (`generalizeIndices`), and in
each case the equation of the shapes is solved first, by the heterogeneous `noConfusion` of
`T.Shape`, which closes the cases of other shapes and gives the equations of the shapes'
arguments; once these are substituted, the equations of the indices hold by definition. So the
indices need not be patterns: `cases`, which solves them first, fails on `n' * 2 = n * 2` for a
constructor of `T (n * 2)`. -/
def casesPos (g : MVarId) (b : FVarId) : MetaM (Array CasesSubgoal) := g.withContext do
  let ty ← whnf (← b.getType)
  let .const I _ := ty.getAppFn
    | throwError "internal error: expected a position, got{indentExpr ty}"
  -- Without indices besides the shape, there is nothing to solve before it.
  if (← getConstInfoInduct I).numIndices ≤ 1 then return ← g.cases b
  if (← constructorApp'? ty.appArg!).isNone then return ← g.cases b
  let gi ← generalizeIndices g b
  let ctors := (← getConstInfoInduct I).ctors.toArray
  let sgs ← gi.mvarId.induction gi.fvarId (mkCasesOnName I)
  (sgs.zip ctors).filterMapM fun (sg, ctor) => sg.mvarId.withContext do
    -- The equations of the indices, then of the shapes, then of the positions.
    let (hs, g) ← sg.mvarId.introNP (gi.numEqs - 1)
    g.withContext do
    let hs := hs.map mkFVar
    let P ← g.getType
    let hsTy ← inferType hs.back!
    let (s₀, s') ← match hsTy.heq?, hsTy.eq? with
      | some (_, s₀, _, s'), _ => pure (s₀, s')
      | _, some (_, s₀, s') => pure (s₀, s')
      | _, _ => throwError "internal error: expected an equation of shapes, got{indentExpr hsTy}"
    let sTy ← whnf (← inferType s₀)
    let .const S us := sTy.getAppFn
      | throwError "internal error: expected a shape, got{indentExpr sTy}"
    let info ← getConstInfoInduct S
    -- `S.noConfusion`, with the equations of the parameters and indices, then of the shapes.
    let mut nc := mkAppN (.const (S ++ `noConfusion) ((← getLevel P) :: us))
      (#[P] ++ sTy.getAppArgs ++ #[s₀] ++ (← whnf (← inferType s')).getAppArgs ++ #[s'])
    for _ in [0:info.numParams + info.numIndices + 1] do
      nc := mkApp nc (← eqProof (← whnfForall (← inferType nc)).bindingDomain! hs)
    let some (c₀, _) ← constructorApp'? s₀ | throwError "internal error: expected a constructor"
    let some (c', _) ← constructorApp'? s' | throwError "internal error: expected a constructor"
    if c₀.name != c'.name then
      g.assign nc
      return none
    let .forallE _ K _ _ ← whnf (← inferType nc)
      | throwError "internal error: unexpected `noConfusion`{indentExpr nc}"
    let k ← mkFreshExprSyntheticOpaqueMVar K (← g.getTag)
    g.assign (mkApp nc k)
    let g ← k.mvarId!.tryClearMany (hs.map (·.fvarId!))
    -- The equations of the shapes' arguments, then of the positions.
    let nEqs := K.getNumHeadForalls - P.getNumHeadForalls + 1
    let some (g, subst) ← Cases.unifyEqs? nEqs g sg.subst ctor | return none
    return some { mvarId := g, subst, fields := sg.fields.map subst.apply, ctorName := ctor }

namespace Ctx

variable (ctx : Ctx)

/-! ### Terms -/

/-- The occurrences of a nested argument at a family `X` on the packed index: `X ()` without
indices, `X` with. -/
def holeFam (X : Expr) : Expr := if ctx.idxed then X else mkApp X (mkConst ``Unit.unit)

/-- `Occ.n o args…` (`IOcc.n` with indices), with the occurrences at `hole`. -/
def occFn (n : Name) (o hole : Expr) (args : Array Expr) : MetaM Expr := do
  if ctx.idxed then
    mkAppOptM (`Codata.IOcc ++ n) (#[none, none, none, none, none, some o, some hole] ++
      args.map some)
  else mkAppOptM (`Codata.Occ ++ n) (#[none, none, none, some o, some hole] ++ args.map some)

/-- `Occ.ofC o ⟨sh, fun q => snd q⟩` (`IOcc.ofC` with indices). -/
def mkOfC (o hole sh : Expr) (snd : Expr → TermElabM Expr) : TermElabM Expr := do
  let f ← ctx.occFn `ofC o hole #[]
  let D ← whnf (← whnf (← inferType f)).bindingDomain!
  unless D.isAppOfArity ``Sigma 2 do
    throwError "internal error: expected a layer, got{indentExpr D}"
  let α := D.appFn!.appArg!
  let β := D.appArg!
  let sndTy ← whnf (mkApp β sh).headBeta
  let fn ← withLocalDeclD `q sndTy.bindingDomain!.headBeta fun q => do
    mkLambdaFVars #[q] (← snd q)
  return mkApp f (mkApp4 (.const ``Sigma.mk D.getAppFn.constLevels!) α β sh fn)

/-- `(b : T.B params idx s) → X (T.idx b)`, the type of the children of a layer (`X ()` without
indices). -/
def childTy (X : Expr) (idx : Array Expr) (s : Expr) : TermElabM Expr := do
  withLocalDeclD `b (← ctx.bAt idx s) fun b => do
    let i ← if ctx.idxed then ctx.idxAt idx s b else pure (mkConst ``Unit.unit)
    mkForallFVars #[b] (mkApp X i)

/-- `@T.toC params X idx a`, for `X` at universe `w`. -/
def toCAt (w : Level) (X : Expr) (idx : Array Expr) (a : Expr) : MetaM Expr := do
  ctx.genAt ctx.toC [w] (#[X] ++ idx ++ #[a])

/-- `@T.ofC params X idx z`, for `X` at universe `w`. -/
def ofCAt (w : Level) (X : Expr) (idx : Array Expr) (z : Expr) : MetaM Expr := do
  ctx.genAt ctx.ofC [w] (#[X] ++ idx ++ #[z])

/-- The index arguments of an inductive `I` from those `mkCasesOnApp` gives its motive, `is`
after its parameters: the indices it took as parameters come from `args`, after `nParams`. -/
def fullIdx (I : Name) (nParams : Nat) (args is : Array Expr) : MetaM (Array Expr) := do
  let info ← getConstInfoInduct I
  return args.extract nParams info.numParams ++ is

/-! ### `toC` -/

/-- The children of the layer of `F.c` with arguments `ys` and nested layers `zs`, at index `idx`
and shape `s`: by cases on the position (`casesPos`). -/
def toCChild (c : Ctor) (X : Expr) (ys zs idx : Array Expr) (s : Expr) : TermElabM Expr := do
  let g ← mkFreshExprSyntheticOpaqueMVar (← ctx.childTy X idx s)
  let (b, g') ← g.mvarId!.intro1
  for sg in ← casesPos g' b do
    let some k := c.args.findIdx? fun a => !a.kind.isData && sg.ctorName == some (ctx.bCtor c a)
      | throwError "internal error: unexpected position {sg.ctorName}"
    let a := c.args[k]!
    let v ← match a.kind with
      | .nest _ =>
        let some m := c.nests.findIdx? (·.1.fvar == a.fvar) | unreachable!
        pure (mkApp (← mkAppM ``Sigma.snd #[sg.subst.apply zs[m]!]) sg.fields.back!)
      | .fn n => pure (mkAppN (sg.subst.apply ys[k]!) (sg.fields.extract (sg.fields.size - n)))
      | _ => pure (sg.subst.apply ys[k]!)
    sg.mvarId.withContext do
      unless ← isDefEq (← sg.mvarId.getType) (← inferType v) do
        throwError "internal error: ill-typed child{indentExpr v}"
      sg.mvarId.assign v
  instantiateMVars g

/-- The layer of `F.c` with arguments `ys` at the family `X` (universe `w`):
`(fun z… => ⟨Shape.c data z.1…, children⟩) (toC o x)…`. -/
def layer (c : Ctor) (w : Level) (X : Expr) (ys : Array Expr) : TermElabM Expr := do
  let σ (e : Expr) := e.replaceFVars c.fvars ys
  let hole := ctx.holeFam X
  let toCs ← c.nests.mapM fun (a, n) => do
    let some k := c.args.findIdx? (·.fvar == a.fvar) | unreachable!
    ctx.occFn `toC (ctx.nestAt n w σ) hole #[ys[k]!]
  let rec go (i : Nat) (zs : Array Expr) : TermElabM Expr := do
    if h : i < toCs.size then
      withLocalDeclD (c.nests[i]!.1.name.appendBefore "z_") (← inferType toCs[i]) fun z =>
        go (i + 1) (zs.push z)
    else
      let data := (c.args.zip ys).filterMap fun (a, y) => if a.kind.isData then some y else none
      let shape ← ctx.shapeCtorApp c (data ++ (← zs.mapM fun z => mkAppM ``Sigma.fst #[z]))
      let idx := c.idx.map σ
      let child ← ctx.toCChild c X ys zs idx shape
      let obj := mkApp5 (← ctx.sigConst ``Codata.Signature.Obj.mk [w]) (← ctx.sigE) X
        (← ctx.pack idx) shape child
      mkLambdaFVars zs obj
  return mkAppN (← go 0 #[]) toCs

/-- Run `k` on the family `X : Ix → Type w` (implicit), with `w` the added universe. -/
def withFamX (n : Name) (w : Level) (k : Expr → TermElabM α) : TermElabM α := do
  withLocalDecl n .implicit (← mkArrow (← ctx.ixp) (mkSort w.succ)) k

/-- `T.toC`. -/
def genToC : TermElabM Unit := do
  let fresh := ctx.freshLevels 1
  let w := ctx.holeLevel (.param fresh[0]!)
  ctx.withFamX `X w fun X => do
  let X' ← ctx.curryFam X
  let FX ← ctx.fAt w X' ctx.idx
  withLocalDeclD `a FX fun a => do
  let np := ctx.params.size + 1
  let value ← mkCasesOnApp ctx.F (← ctx.levelsWith ctx.F [w]) FX.getAppArgs a
    (← getLevel (← ctx.objAt w X (← ctx.packI)))
    (fun is _ => do ctx.objAt w X (← ctx.pack (← fullIdx ctx.F np FX.getAppArgs is)))
    (fun cname xs => do
      let some c := ctx.ctors.find? (ctx.fCtor · == cname)
        | throwError "internal error: unexpected constructor {cname}"
      ctx.layer c w X (← ctorArgsOf ctx.F np FX.getAppArgs xs c.args.size))
  let xs := ctx.params ++ #[X] ++ ctx.idx ++ #[a]
  let (type, value) ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    return (← mkForallFVars xs (← ctx.objAt w X (← ctx.packI)), ← mkLambdaFVars xs value)
  addDef ctx.toC (← ctx.levelParamsOf fresh #[type, value]) type value ctx.ref

/-! ### `ofC` -/

/-- `F.c params X' args…` from the shape arguments `sargs` (data, then the shapes of the nested
arguments) and the children `ch` of a layer. -/
def ofCBody (c : Ctor) (w : Level) (X ch : Expr) (sargs : Array Expr) : TermElabM Expr := do
  let nd := c.dataArgs.size
  let data := sargs.extract 0 nd
  let shs := sargs.extract nd sargs.size
  let σ (e : Expr) := e.replaceFVars (c.dataArgs.map (·.fvar)) data
  let mut fn := mkAppN (← ctx.constWith (ctx.fCtor c) [w]) (ctx.params.push (← ctx.curryFam X))
  let mut ty ← inferType fn
  let mut di := 0
  for a in c.args do
    ty ← whnf ty
    let v ← match a.kind with
      | .data => pure data[di]!
      | .plain _ => pure (mkApp ch (← ctx.bCtorApp c a sargs))
      | .fn n => withTele n ty.bindingDomain! fun ys _ => do
        mkLambdaFVars ys (mkApp ch (← ctx.bCtorApp c a (sargs ++ ys)))
      | .nest n =>
        let some m := c.nests.findIdx? (·.1.fvar == a.fvar) | unreachable!
        ctx.mkOfC (ctx.nestAt n w σ) (ctx.holeFam X) shs[m]! fun q => do
          return mkApp ch (← ctx.bCtorApp c a (sargs.push q))
    if a.kind.isData then di := di + 1
    fn := mkApp fn v
    ty := ty.bindingBody!.instantiate1 v
  return fn

/-- `T.ofC`, by cases on the shape. -/
def genOfC : TermElabM Unit := do
  let fresh := ctx.freshLevels 1
  let w := ctx.holeLevel (.param fresh[0]!)
  ctx.withFamX `X w fun X => do
  let X' ← ctx.curryFam X
  let pI ← ctx.packI
  withLocalDeclD `z (← ctx.objAt w X pI) fun z => do
  let σE ← ctx.sigE
  let shape := mkApp4 (← ctx.sigConst ``Codata.Signature.Obj.shape [w]) σE X pI z
  let child := mkApp4 (← ctx.sigConst ``Codata.Signature.Obj.child [w]) σE X pI z
  let args := ctx.params ++ ctx.idx
  let motive (idx : Array Expr) (s : Expr) : TermElabM Expr := do
    mkArrow (← ctx.childTy X idx s) (← ctx.fAt w X' idx)
  let value ← mkCasesOnApp ctx.Shape (← ctx.levelsWith ctx.Shape []) args shape
    (← getLevel (← motive ctx.idx shape))
    (fun is s => do motive (← fullIdx ctx.Shape ctx.params.size args is) s)
    (fun cname xs => do
      let some c := ctx.ctors.find? (ctx.shapeCtor · == cname)
        | throwError "internal error: unexpected constructor {cname}"
      let sargs ← ctorArgsOf ctx.Shape ctx.params.size args xs (c.dataArgs.size + c.nests.size)
      let data := sargs.extract 0 c.dataArgs.size
      let idx := c.idx.map (·.replaceFVars (c.dataArgs.map (·.fvar)) data)
      withLocalDeclD `ch (← ctx.childTy X idx (← ctx.shapeCtorApp c sargs)) fun ch => do
        mkLambdaFVars #[ch] (← ctx.ofCBody c w X ch sargs))
  let value := mkApp value child
  let xs := ctx.params ++ #[X] ++ ctx.idx ++ #[z]
  let (type, value) ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    return (← mkForallFVars xs (← ctx.fAt w X' ctx.idx), ← mkLambdaFVars xs value)
  addDef ctx.ofC (← ctx.levelParamsOf fresh #[type, value]) type value ctx.ref

/-! ### The laws -/

/-- In a proof, after the introduction of the statement's binders `hs` (parameters first): `e`
with the parameters of the analysis replaced by those of the proof. -/
def inProof (hs : Array Expr) (e : Expr) : Expr :=
  e.replaceFVars ctx.params (hs.extract 0 ctx.params.size)

/-- After `cases` on a layer `z : σ.Obj X ⟨idx⟩` (one goal, its fields the shape and the
children): `cases` on the shape, its type stated as `T.Shape params idx` first so that its
indices are the index variables. `k` gets each constructor's goal, with the substitution. -/
def casesLayer (hs : Array Expr) (g : MVarId) (z : Expr) (idx : Array Expr)
    (k : Ctor → CasesSubgoal → TermElabM Unit) : TermElabM FVarSubst := do
  let #[sg] ← g.cases z.fvarId! | throwError "internal error: cases on a layer"
  let s := sg.fields[0]!
  let g ← sg.mvarId.withContext do
    sg.mvarId.replaceLocalDeclDefEq s.fvarId!
      (ctx.inProof hs (← ctx.shapeAt (idx.map sg.subst.apply)))
  for sg' in ← g.cases s.fvarId! do
    let some c := ctx.ctors.find? fun c => sg'.ctorName == some (ctx.shapeCtor c)
      | throwError "internal error: unexpected shape {sg'.ctorName}"
    k c sg'
  return sg.subst

/-- Close `g : A = Obj.mk s c` where `A` reduces to `Obj.mk s' c'`: by `funext`, cases on the
position (`casesPos`), and `rfl`. The position's type is stated as `T.B params idx s` first. -/
def finishLayer (hs : Array Expr) (g : MVarId) : TermElabM Unit := g.withContext do
  let some (_, _, rhs) := (← instantiateMVars (← g.getType)).eq?
    | throwError "internal error: expected an equation"
  let rhs ← whnf rhs
  let s := rhs.appFn!.appArg!
  let sargs := s.getAppArgs.extract ctx.params.size s.getAppArgs.size
  let some c := ctx.ctors.find? (s.getAppFn.isConstOf <| ctx.shapeCtor ·)
    | throwError "internal error: unexpected shape{indentExpr s}"
  let idx := c.idx.map fun e => ctx.inProof hs <|
    e.replaceFVars (c.dataArgs.map (·.fvar)) (sargs.extract 0 c.dataArgs.size)
  let [g] ← Tactic.run g do
      Tactic.evalTactic (← `(tactic|
        refine congrArg (Codata.Signature.Obj.mk _) (funext fun b => ?_)))
    | throwError "internal error: expected one goal"
  g.withContext do
  let b := (← getLCtx).lastDecl.get!.toExpr
  let g ← g.replaceLocalDeclDefEq b.fvarId! (ctx.inProof hs (← ctx.bAt idx s))
  for sg in ← casesPos g b.fvarId! do sg.mvarId.refl

/-- `T.ofC_toC`, `T.toC_ofC`, `T.ofC_map`. -/
def genIsoLaws : TermElabM Unit := do
  let np := ctx.params.size
  let pI ← ctx.packI
  -- `ofC_toC`
  do
    let fresh := ctx.freshLevels 1
    let w := ctx.holeLevel (.param fresh[0]!)
    ctx.withFamX `X w fun X => do
    let X' ← ctx.curryFam X
    withLocalDeclD `a (← ctx.fAt w X' ctx.idx) fun a => do
    let xs := ctx.params ++ #[X] ++ ctx.idx ++ #[a]
    let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
      mkForallFVars xs (← mkEq (← ctx.ofCAt w X ctx.idx (← ctx.toCAt w X ctx.idx a)) a)
    let value ← prove type fun g => do
      let (hs, g) ← g.intros
      let hs := hs.map mkFVar
      for sg in ← g.cases hs.back!.fvarId! do
        let some c := ctx.ctors.find? fun c => sg.ctorName == some (ctx.fCtor c)
          | throwError "internal error: unexpected case {sg.ctorName}"
        if !c.hasNest then
          sg.mvarId.refl
          continue
        -- `ofC (toC (F.c ys))` unfolds to `F.c ys'`, with `ofC o ⟨(toC o x).1, (toC o x).2⟩` for
        -- a nested `x`, which `ofC_toC'` rewrites.
        sg.mvarId.withContext do
        let some (_, _, rhs) := (← instantiateMVars (← sg.mvarId.getType)).eq?
          | throwError "internal error: expected an equation"
        let args := rhs.getAppArgs
        let ys := args.extract (np + 1) args.size
        let X1 := hs[np]!
        let ρ (e : Expr) := (ctx.inProof hs e).replaceFVars c.fvars ys
        let ys' ← (c.args.zip ys).mapM fun (a, y) => do
          let .nest n := a.kind | return y
          let o := substLevel ctx.uT w (ρ n.occ)
          let t ← ctx.occFn `toC o (ctx.holeFam X1) #[y]
          ctx.mkOfC o (ctx.holeFam X1) (← mkAppM ``Sigma.fst #[t]) fun q => do
            return mkApp (← mkAppM ``Sigma.snd #[t]) q
        let g ← sg.mvarId.replaceTargetDefEq
          (← mkEq (mkAppN rhs.getAppFn (args.extract 0 (np + 1) ++ ys')) rhs)
        simpOnly g #[``Codata.Occ.ofC_toC', ``Codata.IOcc.ofC_toC']
    addThm ctx.ofC_toC (← ctx.levelParamsOf fresh #[type]) type value ctx.ref
  -- `toC_ofC`
  do
    let fresh := ctx.freshLevels 1
    let w := ctx.holeLevel (.param fresh[0]!)
    ctx.withFamX `X w fun X => do
    withLocalDeclD `z (← ctx.objAt w X pI) fun z => do
    let xs := ctx.params ++ #[X] ++ ctx.idx ++ #[z]
    let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
      mkForallFVars xs (← mkEq (← ctx.toCAt w X ctx.idx (← ctx.ofCAt w X ctx.idx z)) z)
    let value ← prove type fun g => do
      let (hs, g) ← g.intros
      let hs := hs.map mkFVar
      let idx := hs.extract (np + 1) (hs.size - 1)
      discard <| ctx.casesLayer hs g hs.back! idx fun c sg => sg.mvarId.withContext do
        let some (_, lhs, rhs) := (← instantiateMVars (← sg.mvarId.getType)).eq?
          | throwError "internal error: expected an equation"
        let mut g ← sg.mvarId.replaceTargetDefEq (← mkEq (← whnf lhs) rhs)
        -- The nested layers `toC o (ofC o z)`, rewritten one by one: they occur in the shape and
        -- in the children, whose types depend on the shape.
        for _ in c.nests do
          let thm := if ctx.idxed then ``Codata.IOcc.toC_ofC else ``Codata.Occ.toC_ofC
          let r ← g.rewrite (← g.getType) (← mkConstWithFreshMVarLevels thm)
          g ← g.replaceTargetEq r.eNew r.eqProof
        ctx.finishLayer hs g
    addThm ctx.toC_ofC (← ctx.levelParamsOf fresh #[type]) type value ctx.ref
  -- `ofC_map`
  let fresh := ctx.freshLevels 2
  let wX := ctx.holeLevel (.param fresh[0]!)
  let wY := ctx.holeLevel (.param fresh[1]!)
  ctx.withFamX `X wX fun X => do
  ctx.withFamX `Y wY fun Y => do
  let ixp ← ctx.ixp
  let fTy ← withLocalDeclD `q ixp fun q => do
    mkForallFVars #[q] (← mkArrow (mkApp X q) (mkApp Y q))
  withLocalDeclD `f fTy fun f => do
  withLocalDeclD `z (← ctx.objAt wX X pI) fun z => do
  let σE ← ctx.sigE
  let mapped := mkAppN (← ctx.sigConst ``Codata.Signature.Obj.map [wX, wY]) #[σE, X, Y, f, pI, z]
  let lhs ← ctx.ofCAt wY Y ctx.idx mapped
  let rhs ← ctx.mapAt wX wY (← ctx.curryFam X) (← ctx.curryFam Y) (← ctx.curryN f 1) ctx.idx
    (← ctx.ofCAt wX X ctx.idx z)
  let xs := ctx.params ++ #[X, Y, f] ++ ctx.idx ++ #[z]
  let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    mkForallFVars xs (← mkEq lhs rhs)
  let value ← prove type fun g => do
    let (hs, g) ← g.intros
    let hs := hs.map mkFVar
    let idx := hs.extract (np + 3) (hs.size - 1)
    discard <| ctx.casesLayer hs g hs.back! idx fun c sg => do
      if !c.hasNest then return ← sg.mvarId.refl
      sg.mvarId.withContext do
      let some (_, lhs, rhs) := (← instantiateMVars (← sg.mvarId.getType)).eq?
        | throwError "internal error: expected an equation"
      let g ← sg.mvarId.replaceTargetDefEq (← mkEq (← whnf lhs) (← whnf rhs))
      -- `IOcc.map_ofC` applies to the children `fun q => c (B.cᵢ_x q)` only once their type
      -- `X (sig.idx (B.cᵢ_x q))` is unfolded to the index of the structure.
      withUnfolding do
        if let some g ← simpOnlyStep g #[``Codata.Signature.Obj.map, ``Codata.Occ.map_ofC,
            ``Codata.IOcc.map_ofC] then
          g.refl
  addThm ctx.ofC_map (← ctx.levelParamsOf fresh #[type]) type value ctx.ref

/-- Step 2, the isomorphism (without `rel_ofC`, `Gen/Rel.lean`). -/
def genIso : TermElabM Unit := do
  ctx.genToC
  ctx.genOfC
  ctx.genIsoLaws

end Ctx

end Codata.Gen
