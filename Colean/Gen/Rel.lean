import Colean.Gen.Iso

/-!
# Generators on `Expr`: the lifting to relations

*Spec.* Input: the context, `T.F` and (for `rel_ofC`) the isomorphism. Output, for `codata`:

* `T.F.Rel R : T.F params X idx → T.F params Y idx → Prop`, the inductive lifting of a relation:
  the same constructor, the same data, related recursive arguments (`R` at their index, pointwise
  under a telescope, `Occ.Rel` for a nested argument);
* `T.F.rel_map`: the images of one value under pointwise related functions are related;
* `T.rel_ofC`: the lifting through the isomorphism is the signature's (`Signature.Obj.Rel`).

`T.F.Rel` belongs to the surface (step 4), but the model's `rel_ofC` and the contract's `bisim`
are stated with it, so it is generated before them (a boundary violation recorded in
`architecture.md`). The two lemmas are proved by tactic scripts: `cases`,
then `constructor` and the hypothesis for `rel_map`; for `rel_ofC`, the layers written as
`toC a`, `toC a'` (`toC_ofC`), `cases` on the hypothesis, which is then at variables, the layers
of the nested arguments rewritten with the hypotheses on them, then the witnesses, and the
positions by cases in general position (`casesPos`).
-/

open Lean Meta Elab Term

namespace Codata.Gen

namespace Ctx

variable (ctx : Ctx)

/-- `X → Y → Prop`, or `∀ j₁ j₂, X j₁ j₂ → Y j₁ j₂ → Prop`. -/
def famRel (X Y : Expr) : TermElabM Expr :=
  ctx.withJs fun js => do
    mkForallFVars js (← mkArrow (mkAppN X js) (← mkArrow (mkAppN Y js) (mkSort .zero)))

/-- `@T.F.Rel params X Y R idx a b`, at the universes `wX`, `wY` of `X`, `Y`. -/
def relAt (wX wY : Level) (X Y R : Expr) (idx : Array Expr) (a b : Expr) : MetaM Expr := do
  ctx.genAt ctx.Rel [wX, wY] (#[X, Y, R] ++ idx ++ #[a, b])

/-- The constructor of `T.F.Rel` for `c`, at the local variables `X`, `Y`, `R` and `Rv` for
`T.F.Rel` itself. -/
def relCtorType (c : Ctor) (wX wY : Level) (X Y R Rv : Expr) : TermElabM Expr := do
  ctx.withArgsAt c (mkAppN X) wX fun ys σ => do
  -- The primed copies of the recursive arguments, at `Y`.
  let recs := (c.args.zip ys).filter (!·.1.kind.isData)
  let rec primes (i : Nat) (acc : Array Expr) (k : Array Expr → TermElabM Expr) :
      TermElabM Expr := do
    if h : i < recs.size then
      let (a, _) := recs[i]
      withLocalDeclD (a.name.appendAfter "'") (ctx.replaceOcc (σ a.type) (mkAppN Y) wY)
        fun y' => primes (i + 1) (acc.push y') k
    else k acc
  primes 0 #[] fun ys' => do
  let hyps ← (recs.zip ys').mapM fun ((a, y), y') => do
    match a.kind with
    | .plain idx => pure (mkAppN R (idx.map σ ++ #[y, y']))
    | .fn n => openFn n (← inferType y) fun zs idx => do
      mkForallFVars zs (mkAppN R (idx ++ #[mkAppN y zs, mkAppN y' zs]))
    | .nest n =>
      let oX := ctx.nestAt n wX σ
      let oY := ctx.nestAt n wY σ
      if ctx.idxed then
        let RP ← if ctx.k ≤ 1 then pure R else
          withLocalDeclD `p ctx.J fun p => do mkLambdaFVars #[p] (mkAppN R (← ctx.projs p))
        mkAppM ``Codata.IOcc.Rel #[oX, oY, RP, y, y']
      else mkAppM ``Codata.Occ.Rel #[oX, oY, R, y, y']
    | .data => unreachable!
  -- The fields: each argument, followed by its primed copy if recursive; then the hypotheses.
  let mut fields := #[]
  let mut ysY := #[]
  let mut j := 0
  for a in c.args, y in ys do
    fields := fields.push y
    if a.kind.isData then ysY := ysY.push y
    else
      fields := fields.push ys'[j]!
      ysY := ysY.push ys'[j]!
      j := j + 1
  let lhs := mkAppN (← ctx.constWith (ctx.fCtor c) [wX]) (ctx.params ++ #[X] ++ ys)
  let rhs := mkAppN (← ctx.constWith (ctx.fCtor c) [wY]) (ctx.params ++ #[Y] ++ ysY)
  let body := mkAppN Rv (ctx.params ++ #[X, Y, R] ++ c.idx.map σ ++ #[lhs, rhs])
  let rec withHyps (i : Nat) (acc : Array Expr) : TermElabM Expr := do
    if h : i < hyps.size then
      withLocalDeclD (← mkFreshUserName `h) hyps[i] fun hv => withHyps (i + 1) (acc.push hv)
    else
      withBinderInfo (ctx.params ++ #[X, Y, R]) .implicit do
        mkForallFVars (ctx.params ++ #[X, Y, R] ++ fields ++ acc) body
  withHyps 0 #[]

/-- `T.F.Rel`. -/
def genRelType : TermElabM Unit := do
  let fresh := ctx.freshLevels 2
  let (wX, wY) := (ctx.holeLevel (.param fresh[0]!), ctx.holeLevel (.param fresh[1]!))
  withLocalDecl `X .implicit (← ctx.famType wX) fun X => do
  withLocalDecl `Y .implicit (← ctx.famType wY) fun Y => do
  withLocalDeclD `R (← ctx.famRel X Y) fun R => do
  let ty ← withLocalDeclD `a (← ctx.fAt wX X ctx.idx) fun a => do
    withLocalDeclD `b (← ctx.fAt wY Y ctx.idx) fun b => do
    withBinderInfo (ctx.params ++ ctx.idx) .implicit do
      mkForallFVars (ctx.params ++ #[X, Y, R] ++ ctx.idx ++ #[a, b]) (mkSort .zero)
  withLocalDeclD `Rel ty fun Rv => do
  let ctorTys ← ctx.ctors.mapM (ctx.relCtorType · wX wY X Y R Rv)
  let us ← ctx.levelParamsOf fresh (ctorTys.push ty)
  let Rc := Lean.mkConst ctx.Rel (us.map mkLevelParam)
  addInductive us (ctx.params.size + 3) [{
    name := ctx.Rel, type := ty
    ctors := (ctx.ctors.zip ctorTys).toList.map fun (c, t) =>
      { name := ctx.relCtor c, type := t.replaceFVar Rv Rc } }] ctx.ref

/-- `T.F.rel_map`. -/
def genRelMap : TermElabM Unit := do
  let fresh := ctx.freshLevels 3
  let [wX, wY, wZ] := fresh.map fun u => ctx.holeLevel (.param u) | unreachable!
  withLocalDecl `X .implicit (← ctx.famType wX) fun X => do
  withLocalDecl `Y .implicit (← ctx.famType wY) fun Y => do
  withLocalDecl `Z .implicit (← ctx.famType wZ) fun Z => do
  withLocalDeclD `R (← ctx.famRel Y Z) fun R => do
  withLocalDeclD `f (← ctx.famFn X Y) fun f => do
  withLocalDeclD `g (← ctx.famFn X Z) fun g => do
  withLocalDeclD `a (← ctx.fAt wX X ctx.idx) fun a => do
  let hTy ← ctx.withJs fun js => withLocalDeclD `x (mkAppN X js) fun x => do
    mkForallFVars (js.push x) (mkAppN R (js ++ #[mkAppN f (js.push x), mkAppN g (js.push x)]))
  withLocalDeclD `h hTy fun h => do
  let xs := ctx.params ++ #[X, Y, Z, R, f, g] ++ ctx.idx ++ #[a, h]
  let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    mkForallFVars xs (← ctx.relAt wY wZ Y Z R ctx.idx (← ctx.mapAt wX wY X Y f ctx.idx a)
      (← ctx.mapAt wX wZ X Z g ctx.idx a))
  let map := mkCIdent ctx.Fmap
  let value ← prove type fun goal => do
    let (_, goal) ← goal.introN (xs.size - 2)
    runTac goal (← `(tactic| (
      intro a h
      cases a
      all_goals simp only [$map:ident]
      all_goals constructor
      all_goals intros
      all_goals first
        | apply h
        | (apply Codata.Occ.rel_map; intro; apply h)
        | (apply Codata.IOcc.rel_map; intro; intro; apply h))))
  addThm ctx.Frel_map (← ctx.levelParamsOf fresh #[type]) type value ctx.ref

/-- `T.rel_ofC`. -/
def genRelOfC : TermElabM Unit := do
  let fresh := ctx.freshLevels 2
  let wX := ctx.holeLevel (.param fresh[0]!)
  let wY := ctx.holeLevel (.param fresh[1]!)
  ctx.withFamX `X wX fun X => do
  ctx.withFamX `Y wY fun Y => do
  let ixp ← ctx.ixp
  let RTy ← withLocalDeclD `q ixp fun q => do
    mkForallFVars #[q] (← mkArrow (mkApp X q) (← mkArrow (mkApp Y q) (mkSort .zero)))
  withLocalDeclD `R RTy fun R => do
  let pI ← ctx.packI
  withLocalDeclD `z (← ctx.objAt wX X pI) fun z => do
  withLocalDeclD `z' (← ctx.objAt wY Y pI) fun z' => do
  let (X', Y') := (← ctx.curryFam X, ← ctx.curryFam Y)
  let hTy ← ctx.relAt wX wY X' Y' (← ctx.curryN R 0) ctx.idx (← ctx.ofCAt wX X ctx.idx z)
    (← ctx.ofCAt wY Y ctx.idx z')
  withLocalDeclD `h hTy fun h => do
  let objRel := mkAppN (← ctx.sigConst ``Codata.Signature.Obj.Rel [wX, wY])
    #[← ctx.sigE, X, Y, R, pI, z, z']
  let xs := ctx.params ++ #[X, Y, R] ++ ctx.idx ++ #[z, z', h]
  let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do mkForallFVars xs objRel
  -- The layers are written as `toC a`, `toC a'`, so that the hypothesis is on variables
  -- `a`, `a'` and at the index variables: `cases` on it needs no unification.
  let ofC := mkCIdent ctx.ofC
  let toC_ofC := mkCIdent ctx.toC_ofC
  let start ← `(tactic| (
    intro z z' h
    rw [← $toC_ofC:ident z, ← $toC_ofC:ident z']
    generalize $ofC:ident z = a at h ⊢
    generalize $ofC:ident z' = a' at h ⊢
    clear z z'
    cases h))
  let value ← prove type fun g => do
    let (_, g) ← g.introN (xs.size - 3)
    let gs ← Tactic.run g (Tactic.evalTactic start)
    unless gs.length == ctx.ctors.size do
      throwError "internal error: unexpected cases of `{ctx.Rel}`"
    for g in gs, c in ctx.ctors do
      -- `toC (F.c …)` unfolded to its layer, where a nested argument's layer `toC o x` occurs.
      let g ← g.withContext do
        let tgt ← instantiateMVars (← g.getType)
        let args := tgt.getAppArgs
        g.replaceTargetDefEq (mkAppN tgt.getAppFn
          (args.extract 0 (args.size - 2) ++ #[← whnf args[args.size - 2]!, ← whnf args.back!]))
      -- The hypothesis on a nested pair gives its two layers, with one shape, and the relation
      -- on their contents.
      let recs := c.recArgs
      let mut steps : Array (TSyntax `tactic) := #[]
      if c.hasNest then
        let hs := recs.map fun a => mkIdent (Name.mkSimple s!"h_{a.name}")
        steps := steps.push (← `(tactic| rename_i $[$hs:ident]*))
        for hId in hs, a in recs do
          if a.kind.isNest then
            let e := mkIdent (Name.mkSimple s!"e_{a.name}")
            let e' := mkIdent (Name.mkSimple s!"e'_{a.name}")
            steps := steps.push
              (← `(tactic| obtain ⟨_, _, _, $e:ident, $e':ident, $hId:ident⟩ := $hId))
            steps := steps.push (← `(tactic| rw [$e:ident, $e':ident]))
      steps := steps.push (← `(tactic| refine ⟨_, _, _, rfl, rfl, fun b => ?_⟩))
      let [g] ← Tactic.run g (Tactic.evalTactic (← `(tactic| ($[$steps:tactic]*))))
        | throwError "internal error: expected one goal"
      -- The positions, by cases in general position.
      let b ← g.withContext do return (← getLCtx).lastDecl.get!.fvarId
      for sg in ← casesPos g b do runTac sg.mvarId (← `(tactic| solve_by_elim))
  addThm ctx.rel_ofC (← ctx.levelParamsOf fresh #[type]) type value ctx.ref

end Ctx

end Codata.Gen
