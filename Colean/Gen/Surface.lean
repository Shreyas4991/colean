import Colean.Gen.Extras

/-!
# Generators on `Expr`, step 4: the surface

*Spec.* Input: the constructor list and the declarations of steps 2–3. Output, assembled without
tactic proofs from what exists:

* the constructors `T.cᵢ := T.ctor (T.F.cᵢ …)` with the simp lemmas `T.dtor_cᵢ`, `T.ctor_cᵢ`,
  injectivity `T.cᵢ_inj` (`Codata.inj_of` at `T.F.cᵢ.injEq`, without the proof arguments, as
  `injEq`) and disjointness `T.cᵢ_ne_cⱼ` (`Codata.ne_of`), the last two when their statements
  make sense;
* the case analysis `T.casesOn` (by cases on `F` after `dtor`, cast along `ctor_dtor`; the
  `cases` eliminator), `T.casesOnAux`, `T.casesOn_ctor` and the simp lemmas `T.casesOn_cᵢ`;
* for `data`, the computation rules `T.rec_cᵢ` and `T.fold_cᵢ` (simp lemmas), the hypothesis of
  a nested argument given as `fun t _ => T.rec … t` on its members; in a block the rules of the
  block-level recursor are `Blk.rec_cᵢ`, with the block-level names of the constructors;
* in a block, the types `Tₘ params idx := Blk params (.Tₘ idx)` (`genTypes`, before everything
  that mentions them), and the aliases `Tₘ.corec`, `Tₘ.bisim` (`codata`) or `Tₘ.fold` (`data`)
  restricting the block-level declarations to a type;
* in a `data` block, the recursors per type `Tₘ.rec`, in the shape of Lean's mutual inductives
  (a motive per type), as `Blk.rec` at the motive made of them, and their rules `Tₘ.rec_cᵢ`,
  which are the block-level rules by unfolding; a hypothesis by `IPolyIso.Mem` is one per type
  of the argument there;
* the info tree for the names of the types and the constructors in the declaration
  (`addDeclInfo`), once everything else is declared.

The constructors, their lemmas and `casesOn` are per type, with the types `Tₘ` in their
statements; in a block, `Tₘ.casesOnAux` is by `cases` on a goal metavariable, which discards the
constructors of the other types. `T.F.Rel` is part of the surface too, generated earlier
(`Gen/Rel.lean`).
-/

open Lean Meta Elab Term

namespace Codata.Gen

namespace Ctx

variable (ctx : Ctx)

/-! ### The constructors -/

/-- `T.cᵢ`, `T.dtor_cᵢ`, `T.ctor_cᵢ`, `T.cᵢ_inj`, `T.cᵢ_ne_cⱼ`. -/
def genCtors : TermElabM Unit := do
  let L ← ctx.tLvl
  let T ← ctx.tFam
  let thm (c : Ctor) (n : Name) (xs : Array Expr) (stmt value : Expr) : TermElabM Unit := do
    let (type, value) ← withBinderInfo ctx.params .implicit do
      return (← mkForallFVars (ctx.params ++ xs) stmt, ← mkLambdaFVars (ctx.params ++ xs) value)
    addThm n (← ctx.levelParamsOf [] #[type]) type value ctx.types[c.owner]!.ref
    addSimp n
  for c in ctx.ctors do
    ctx.withTArgs c fun ys σ => do
    let idx := c.idx.map σ
    let fapp ← ctx.fCtorApp c L T ys
    let (type, value) ← withBinderInfo ctx.params .implicit do
      return (← mkForallFVars (ctx.params ++ ys) (← ctx.tyAt c.owner (c.uidx.map σ)),
        ← mkLambdaFVars (ctx.params ++ ys) (← ctx.appAt ctx.ctor idx #[fapp]))
    let ref := ctx.types[c.owner]!.ref
    addDef (ctx.tCtor c) (← ctx.levelParamsOf [] #[type, value]) type value ref
    addRangesUser (ctx.tCtor c) ref
    let capp ← ctx.tCtorApp c ys
    thm c (ctx.tName' c "dtor_" "") ys (← mkEq (← ctx.appAt ctx.dtor idx #[capp]) fapp)
      (← ctx.appAt ctx.dtor_ctor idx #[fapp])
    thm c (ctx.tName' c "ctor_" "") ys (← mkEq (← ctx.appAt ctx.ctor idx #[fapp]) capp)
      (← mkEqRefl capp)
  -- Injectivity, for constructors with explicit, independent arguments. As in `T.F.c.injEq`,
  -- the proofs are left out of the conjunction, and there is no lemma if nothing is left.
  for c in ctx.ctors do
    if c.args.isEmpty || c.args.any (!·.bi.isExplicit) || c.dependent || c.idxDependent then
      continue
    ctx.withTArgs c fun ys σ => do
    ctx.withTArgs c (rename := (·.appendAfter "'")) fun ys' _ => do
    let idx := c.idx.map σ
    let eqs ← (ys.zip ys').filterMapM fun (y, y') => do
      if ← isProof y then return none
      return some (← mkEq y y')
    if eqs.isEmpty then return
    let conj := eqs.pop.foldr (init := eqs.back!) mkAnd
    let stmt := mkIff (← mkEq (← ctx.tCtorApp c ys) (← ctx.tCtorApp c ys')) conj
    let injEq ← ctx.genAt (ctx.fCtor c ++ `injEq) [L] (#[T] ++ ys ++ ys')
    let value ← mkAppOptM ``Codata.inj_of #[none, none, ← ctx.appAt ctx.ctor idx #[],
      ← ctx.appAt ctx.ctor_injective idx #[], ← ctx.fCtorApp c L T ys, ← ctx.fCtorApp c L T ys',
      none, injEq]
    thm c (ctx.tName' c "" "_inj") (ys ++ ys') stmt value
  -- Disjointness, for constructors of the same type at the same, independent, index.
  for c in ctx.ctors do
    for c' in ctx.ctors do
      if c.name == c'.name || c.owner != c'.owner then continue
      if c.idxDependent || c'.idxDependent || c.idx != c'.idx then continue
      ctx.withTArgs c fun ys σ => do
      ctx.withTArgs c' (rename := (·.appendAfter "'")) fun ys' _ => do
      let idx := c.idx.map σ
      let stmt ← mkAppM ``Ne #[← ctx.tCtorApp c ys, ← ctx.tCtorApp c' ys']
      let (fa, fb) := (← ctx.fCtorApp c L T ys, ← ctx.fCtorApp c' L T ys')
      let hab ← lam `h (← mkEq fa fb) fun h => mkNoConfusion (mkConst ``False) h
      let value ← mkAppOptM ``Codata.ne_of #[none, none, ← ctx.appAt ctx.dtor idx #[], none,
        none, none, none, mkAppN (← ctx.constWith (ctx.tName' c "dtor_" "") []) (ctx.params ++ ys),
        mkAppN (← ctx.constWith (ctx.tName' c' "dtor_" "") []) (ctx.params ++ ys'), hab]
      thm c (ctx.tyName c.owner ++ Name.mkSimple (c.name.toString ++ "_ne_" ++ c'.name.toString))
        (ys ++ ys') stmt value

/-! ### Case analysis -/

/-- The value of `Tₘ.casesOnAux` in a block, on its statement `∀ params motive idx y minors, …`:
by `cases` on `y : T.F params T (.Tₘ idx)`, which leaves the constructors of the `m`-th type
(the others have another constructor of `Blk.Ix` as their index), then the minor premise. -/
def casesAuxBlock (m : Nat) (cs : Array Ctor) (g : MVarId) : TermElabM Unit := do
  let (hs, g) ← g.intros
  let y := hs[ctx.params.size + 1 + ctx.types[m]!.idx.size]!
  let minors := hs.extract (hs.size - cs.size) hs.size
  for sg in ← g.cases y do
    let some k := cs.findIdx? fun c => sg.ctorName == some (ctx.fCtor c)
      | throwError "internal error: unexpected case {sg.ctorName}"
    sg.mvarId.withContext do
    let v := mkAppN (sg.subst.apply (mkFVar minors[k]!)) sg.fields
    unless ← isDefEq (← sg.mvarId.getType) (← inferType v) do
      throwError "internal error: ill-typed case{indentExpr v}"
    sg.mvarId.assign v

/-- `Tₘ.casesOnAux`, `Tₘ.casesOn` (the `cases` eliminator), `Tₘ.casesOn_ctor`,
`Tₘ.casesOn_cᵢ`, for the `m`-th type: its constructors only, its own indices. -/
def genCasesOf (m : Nat) : TermElabM Unit := do
  let L ← ctx.tLvl
  let T ← ctx.tFam
  let fresh := ctx.freshLevels 1
  let v := Level.param fresh[0]!
  let ty := ctx.types[m]!
  let ref := ty.ref
  let uidx := ty.idx
  let idx := ctx.wrap m uidx
  let cs := ctx.ctors.filter (·.owner == m)
  let auxN := ctx.tyGen m "casesOnAux"
  let casesN := ctx.tyGen m "casesOn"
  let ctorN := ctx.tyGen m "casesOn_ctor"
  ctx.withTypeMotive m v fun motive => do
  let minorTy (c : Ctor) : TermElabM Expr := ctx.withTArgs c fun ys σ => do
    mkForallFVars ys (mkAppN motive (c.uidx.map σ |>.push (← ctx.tCtorApp c ys)))
  let FT ← ctx.fAt L T idx
  let ctorAt (idx : Array Expr) (y : Expr) := ctx.appAt ctx.ctor idx #[y]
  let lvls (xs : Array Expr) := do ctx.levelParamsOf fresh xs
  let impl (xs : Array Expr) (stmt value : Expr) : TermElabM (Expr × Expr) :=
    withBinderInfo (ctx.params ++ uidx) .implicit do
      return (← mkForallFVars xs stmt, ← mkLambdaFVars xs value)
  withLocalDeclD `y FT fun y => do
  ctx.withMinors (cs := cs) (·.name) minorTy fun minors => do
  -- `casesOnAux`, by cases on `F`.
  let xs := ctx.params ++ #[motive] ++ uidx ++ #[y] ++ minors
  let stmt := mkAppN motive (uidx.push (← ctorAt idx y))
  let (type, value) ← if ctx.isBlock then do
      let type ← withBinderInfo (ctx.params ++ uidx) .implicit do mkForallFVars xs stmt
      pure (type, ← prove type (ctx.casesAuxBlock m cs))
    else do
      let np := ctx.params.size + 1
      let value ← mkCasesOnApp ctx.F (← ctx.levelsWith ctx.F [L]) FT.getAppArgs y v
        (fun is y => do
          let idx ← fullIdx ctx.F np FT.getAppArgs is
          return mkAppN motive (idx.push (← ctorAt idx y)))
        (fun cname xs => do
          let some k := cs.findIdx? (ctx.fCtor · == cname)
            | throwError "internal error: unexpected constructor {cname}"
          return mkAppN minors[k]! (← ctorArgsOf ctx.F np FT.getAppArgs xs cs[k]!.args.size))
      impl xs stmt value
  addDef auxN (← lvls #[type, value]) type value ref
  let auxAt (y : Expr) : MetaM Expr := do
    ctx.genAt auxN [v] (#[motive] ++ uidx ++ #[y] ++ minors)
  -- `casesOn`
  let casesAt (uidx : Array Expr) (t : Expr) : MetaM Expr := do
    ctx.genAt casesN [v] (#[motive] ++ uidx ++ #[t] ++ minors)
  let motiveI := mkAppN motive uidx
  do
    withLocalDeclD `t (← ctx.tyAt m uidx) fun t => do
    let h ← mkCongrArg motiveI (← ctx.appAt ctx.ctor_dtor idx #[t])
    let value ← mkAppM ``Eq.mp #[h, ← auxAt (← ctx.appAt ctx.dtor idx #[t])]
    let (type, value) ← impl (ctx.params ++ #[motive] ++ uidx ++ #[t] ++ minors)
      (mkAppN motive (uidx.push t)) value
    addDef casesN (← lvls #[type, value]) type value ref
    addAttrs casesN #[← `(Parser.Term.attrInstance| elab_as_elim),
      ← `(Parser.Term.attrInstance| cases_eliminator)]
  -- `casesOn_ctor`: the cast disappears once `dtor (ctor y) = y` is substituted.
  do
    let aux ← lam `y FT fun y => auxAt y
    let value ← mkAppOptM ``Codata.cast_ctor_dtor #[none, none, motiveI,
      ← ctx.appAt ctx.ctor idx #[], ← ctx.appAt ctx.dtor idx #[],
      ← ctx.appAt ctx.ctor_dtor idx #[], ← ctx.appAt ctx.dtor_ctor idx #[], aux, y]
    let (type, value) ← impl xs (← mkEq (← casesAt uidx (← ctorAt idx y)) (← auxAt y)) value
    addThm ctorN (← lvls #[type]) type value ref
  -- `casesOn_cᵢ`
  for c in cs, k in [0:cs.size] do
    ctx.withTArgs c fun ys σ => do
    let fapp ← ctx.fCtorApp c L T ys
    let lhs ← casesAt (c.uidx.map σ) (← ctx.tCtorApp c ys)
    let value := mkAppN (← ctx.constWith ctorN [v])
      (ctx.params ++ #[motive] ++ c.uidx.map σ ++ #[fapp] ++ minors)
    let xs := ctx.params ++ #[motive] ++ ys ++ minors
    let (type, value) ← withBinderInfo ctx.params .implicit do
      return (← mkForallFVars xs (← mkEq lhs (mkAppN minors[k]! ys)), ← mkLambdaFVars xs value)
    let n := ctx.tName' c "casesOn_" ""
    addThm n (← lvls #[type]) type value ref
    addSimp n

/-- Case analysis for every type. -/
def genCases : TermElabM Unit := do
  for m in [0:ctx.types.size] do ctx.genCasesOf m

/-! ### Blocks: the types and the aliases -/

/-- In a block, the types: `Tₘ params idx := Blk params (.Tₘ idx)`. Declared after the family and
before anything that mentions them. -/
def genTypes : TermElabM Unit := do
  unless ctx.isBlock do return
  let L ← ctx.tLvl
  for m in [0:ctx.types.size] do
    let t := ctx.types[m]!
    let xs := ctx.params ++ t.idx
    let value ← mkLambdaFVars xs (← ctx.tAt (ctx.wrap m t.idx))
    let type ← withBinderInfo ctx.declParams .default do mkForallFVars xs (mkSort L.succ)
    addDef t.name (← ctx.levelParamsOf [] #[type, value]) type value t.ref
    addRangesUser t.name t.ref

/-- In a `codata` block, the block-level `corec` and `bisim` restricted to each type. `dtor` and
`ctor` are not aliased: dot notation `t.dtor` resolves to the block-level `dtor` through the
definition of the type, and an alias at the head of a lemma would not be seen through by `rw`. -/
def genAliases : TermElabM Unit := do
  unless ctx.isBlock do return
  let L ← ctx.tLvl
  let T ← ctx.tFam
  let fresh := ctx.freshLevels 1
  let wS := ctx.holeLevel (.param fresh[0]!)
  -- `Tₘ.corec`
  do
    withLocalDecl (← ctx.userName `S) .implicit (← ctx.famType wS) fun S => do
    withLocalDeclD `c (← ctx.famFn S (← ctx.fFam wS S)) fun c => do
    for m in [0:ctx.types.size] do
      let t := ctx.types[m]!
      let idx := ctx.wrap m t.idx
      withLocalDeclD `s (mkAppN S idx) fun s => do
      let xs := ctx.params ++ #[S, c] ++ t.idx ++ #[s]
      let value ← ctx.genAt ctx.corec [wS] (#[S, c] ++ idx ++ #[s])
      let (type, value) ← withBinderInfo (ctx.params ++ t.idx) .implicit do
        return (← mkForallFVars xs (← ctx.tyAt m t.idx), ← mkLambdaFVars xs value)
      addDef (ctx.tyGen m "corec") (← ctx.levelParamsOf fresh #[type, value]) type value t.ref
        (reducible := true)
  -- `Tₘ.bisim`
  withLocalDeclD `R (← ctx.famRel T T) fun R => do
  let HTy ← withLocalDeclD `x (← ctx.tAt ctx.idx) fun x => do
    withLocalDeclD `y (← ctx.tAt ctx.idx) fun y => do
      let rel ← ctx.relAt L L T T R ctx.idx (← ctx.appAt ctx.dtor ctx.idx #[x])
        (← ctx.appAt ctx.dtor ctx.idx #[y])
      mkForallFVars (ctx.idx ++ #[x, y]) (← mkArrow (mkAppN R (ctx.idx ++ #[x, y])) rel)
  withLocalDeclD `H HTy fun H => do
  for m in [0:ctx.types.size] do
    let t := ctx.types[m]!
    let idx := ctx.wrap m t.idx
    let Ti ← ctx.tyAt m t.idx
    withLocalDecl `x .implicit Ti fun x => do
    withLocalDecl `y .implicit Ti fun y => do
    withLocalDeclD `h (mkAppN R (idx ++ #[x, y])) fun h => do
    let xs := ctx.params ++ #[R, H] ++ t.idx ++ #[x, y, h]
    let value ← ctx.genAt ctx.bisim [] (#[R, H] ++ idx ++ #[x, y, h])
    let (type, value) ← withBinderInfo (ctx.params ++ t.idx) .implicit do
      return (← mkForallFVars xs (← mkEq x y), ← mkLambdaFVars xs value)
    addThm (ctx.tyGen m "bisim") (← ctx.levelParamsOf [] #[type]) type value t.ref

/-- In a `data` block, the block-level `fold` restricted to each type (`dtor` and `ctor` are
reached by dot notation, see `genAliases`). The recursors per type are `genTypeRecs`. -/
def genDataAliases : TermElabM Unit := do
  unless ctx.isBlock do return
  let fresh := ctx.freshLevels 1
  let wS := ctx.holeLevel (.param fresh[0]!)
  withLocalDecl (← ctx.userName `S) .implicit (← ctx.famType wS) fun S => do
  withLocalDeclD `a (← ctx.famFn (← ctx.fFam wS S) S) fun a => do
  for m in [0:ctx.types.size] do
    let t := ctx.types[m]!
    let idx := ctx.wrap m t.idx
    withLocalDeclD `t (← ctx.tyAt m t.idx) fun tv => do
    let xs := ctx.params ++ #[S, a] ++ t.idx ++ #[tv]
    let value ← ctx.genAt ctx.fold [wS] (#[S, a] ++ idx ++ #[tv])
    let (type, value) ← withBinderInfo (ctx.params ++ t.idx) .implicit do
      return (← mkForallFVars xs (mkAppN S idx), ← mkLambdaFVars xs value)
    addDef (ctx.tyGen m "fold") (← ctx.levelParamsOf fresh #[type, value]) type value t.ref
      (reducible := true)

/-! ### The info tree -/

/-- The names the user wrote, the types and the constructors, as the declarations they name in
the info tree: for hovering and go-to-definition, as `inductive` does. -/
def addDeclInfo : TermElabM Unit := withSaveInfoContext do
  for t in ctx.types do
    addTermInfo' t.nameRef (← mkConstWithLevelParams t.name) (isBinder := true)
  for c in ctx.ctors do
    addTermInfo' c.nameRef (← mkConstWithLevelParams (ctx.tCtor c)) (isBinder := true)

/-! ### `data`: the computation rules of `rec` and `fold` -/

/-- The induction hypotheses of `c` with arguments `ys` (as those of `T.c`) as values, the
recursor applied to the recursive arguments: `recAt idx x` at the family-level index arguments
`idx`; for a nested argument, `fun t _ => recAt idx t` on its members, or with `pos` the
recursor at every position of its structure (`T.recPos`), with `split` one per type as in
`recIHsWith`. The right-hand side of `rec_cᵢ` is the minor premise applied to `ys` and these. -/
def recIHVals (recAt : Array Expr → Expr → TermElabM Expr) (c : Ctor) (ys : Array Expr)
    (σ : Expr → Expr) (pos split : Bool := false) : TermElabM (Array Expr) := do
  let L ← ctx.tLvl
  let mut out := #[]
  for a in c.args, y in ys do
    match a.kind with
    | .data => pure ()
    | .plain idx => out := out.push (← recAt (idx.map σ) y)
    | .fn n =>
      out := out.push (← ctx.openTFn n (← inferType y) fun zs idx => do
        mkLambdaFVars zs (← recAt idx (mkAppN y zs)))
    | .nest n =>
      if pos then
        let t ← ctx.nestToC (ctx.nestAt n L σ) y
        out := out.push (← ctx.withNestPos n σ t fun q idx => do
          mkLambdaFVars #[q] (← recAt idx (mkApp (← mkAppM ``Sigma.snd #[t]) q)))
      else
        let nm ← ctx.nestMem a n σ
        if split && ctx.isBlock && nm.idx?.isNone then
          for m in ctx.occTypes a.type do
            out := out.push (← ctx.withTypeMember nm y m (h := `_) fun uidx t h => do
              mkLambdaFVars (uidx ++ #[t, h]) (← recAt (ctx.wrap m uidx) t))
        else out := out.push (← ctx.memVal nm y recAt)
  return out

/-- The name of the computation rule of the family's `rec` for `c`: `T.rec_cᵢ`, or in a block
`Blk.rec_cᵢ` with the block-level name of `c` (`Even_Odd.rec_Even_succ`), since `Tₘ.rec_cᵢ` is
the rule of the per-type recursor. -/
def recRuleN (c : Ctor) : Name :=
  if ctx.isBlock then ctx.gen ("rec_" ++ c.fname.toString) else ctx.tName' c "rec_" ""

/-- `T.rec_cᵢ` (in a block `Blk.rec_cᵢ`) and `T.fold_cᵢ`. The rule of `rec` is that of
`recPos` (`T.recPos_ctor`, at the minor premises of `rec`), followed by `PolyIso.memRec_pos` at
each nested argument (`memValEq`). -/
def genRecLemmas : TermElabM Unit := do
  let L ← ctx.tLvl
  let T ← ctx.tFam
  -- `rec_cᵢ`
  do
    let fresh := ctx.freshLevels 1
    let v := Level.param fresh[0]!
    ctx.withMotive v fun motive => do
    let recAt (minors idx : Array Expr) (t : Expr) : TermElabM Expr := do
      ctx.genAt ctx.recN [v] (#[motive] ++ minors ++ idx ++ #[t])
    for c in ctx.ctors, k in [0:ctx.ctors.size] do
      ctx.withTArgs c fun ys σ => do
      ctx.withMinors (·.fname) (ctx.recMinorTy motive) fun minors => do
      let idx := c.idx.map σ
      let lhs ← recAt minors idx (← ctx.tCtorApp c ys)
      let rhs := mkAppN minors[k]! (ys ++ (← ctx.recIHVals (recAt minors) c ys σ))
      -- The proof, with `recPos` at the minor premises of `rec`.
      let pminors ← ctx.posMinors motive minors
      let recPosAt (idx : Array Expr) (t : Expr) : TermElabM Expr := do
        ctx.genAt ctx.recPos [v] (#[motive] ++ pminors ++ idx ++ #[t])
      let h₁ := mkAppN (← ctx.constWith ctx.recPos_ctor [v])
        (ctx.params ++ #[motive] ++ pminors ++ idx ++ #[← ctx.fCtorApp c L T ys])
      let mid := pminors[k]!.beta (ys ++ (← ctx.recIHVals recPosAt c ys σ (pos := true)))
      let vals ← ctx.recIHVals recPosAt c ys σ
      let mut h₂ ← mkEqRefl (mkAppN minors[k]! ys)
      for ((a, y), x) in ((c.args.zip ys).filter (!·.1.kind.isData)).zip vals do
        let e ← match a.kind with
          | .nest n => ctx.memValEq (← ctx.nestMem a n σ) y recPosAt
          | _ => mkEqRefl x
        h₂ ← mkCongr h₂ e
      let value := mkAppN (.const ``Eq.trans [v]) #[← inferType lhs,
        (← inferType h₁).appFn!.appArg!, mid, mkAppN minors[k]! (ys ++ vals), h₁, h₂]
      let xs := ctx.params ++ #[motive] ++ ys ++ minors
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs (← mkEq lhs rhs), ← mkLambdaFVars xs value)
      let n := ctx.recRuleN c
      addThm n (← ctx.levelParamsOf fresh #[type]) type value ctx.ref
      addSimp n
  -- `fold_cᵢ`
  let fresh := ctx.freshLevels 1
  let wS := ctx.holeLevel (.param fresh[0]!)
  withLocalDecl (← ctx.userName `S) .implicit (← ctx.famType wS) fun S => do
  withLocalDeclD `a (← ctx.famFn (← ctx.fFam wS S) S) fun a => do
  let foldAt (idx : Array Expr) (t : Expr) : MetaM Expr := do
    ctx.genAt ctx.fold [wS] (#[S, a] ++ idx ++ #[t])
  for c in ctx.ctors do
    ctx.withTArgs c fun ys σ => do
    let idx := c.idx.map σ
    let mapped ← (c.args.zip ys).mapM fun (a, y) => do
      match a.kind with
      | .data => pure y
      | .plain idx => foldAt (idx.map σ) y
      | .fn n => ctx.openTFn n (← inferType y) fun zs idx => do
        mkLambdaFVars zs (← foldAt idx (mkAppN y zs))
      | .nest n =>
        let (oT, oS) := (ctx.nestAt n L σ, ctx.nestAt n wS σ)
        if ctx.idxed then
          let f ← lam `p ctx.J fun p => do
            let ps ← ctx.projs p
            lam `t (← ctx.tAt ps) fun t => foldAt ps t
          mkAppM ``Codata.IOcc.map #[oT, oS, f, y]
        else
          let f ← lam `t (← ctx.tAt #[]) fun t => foldAt #[] t
          mkAppM ``Codata.Occ.map #[oT, oS, f, y]
    let lhs ← foldAt idx (← ctx.tCtorApp c ys)
    let rhs := mkAppN a (idx.push (← ctx.fCtorApp c wS S mapped))
    let value := mkAppN (← ctx.constWith ctx.fold_ctor [wS])
      (ctx.params ++ #[S, a] ++ idx ++ #[← ctx.fCtorApp c L T ys])
    let xs := ctx.params ++ #[S, a] ++ ys
    let (type, value) ← withBinderInfo ctx.params .implicit do
      return (← mkForallFVars xs (← mkEq lhs rhs), ← mkLambdaFVars xs value)
    let n := ctx.tName' c "fold_" ""
    addThm n (← ctx.levelParamsOf fresh #[type]) type value ctx.ref
    addSimp n

/-! ### `data` blocks: the recursors per type -/

/-- In a block, the type that the block index `i` is at, with its index arguments: `(k, idx)`
when `i` reduces to `Blk.Ix.Tₖ params idx`. A nested argument's positions have their index
computed from the layer, so it is reduced first. -/
def typeAt? (i : Expr) : MetaM (Option (Nat × Array Expr)) := do
  let i ← whnf i
  let some k := ctx.ixCtors.findIdx? (i.getAppFn.isConstOf ·.getAppFn.constName!)
    | return none
  return some (k, i.getAppArgs.extract ctx.params.size i.getAppNumArgs)

/-- Run `k` on the motives `{motive_1 : ∀ j₁ j₂, T₁ params j₁ j₂ → Sort v} …` of the types of a
block, in block order, and the block-level motive they make,
`fun i x => Blk.Ix.casesOn i motive_1 … x`. -/
def withTypeMotives (v : Level) (k : Array Expr → Expr → TermElabM α) : TermElabM α := do
  let rec go (m : Nat) (motives : Array Expr) : TermElabM α := do
    if m < ctx.types.size then
      ctx.withTypeMotive m v (name := .mkSimple s!"motive_{m + 1}") fun x =>
        go (m + 1) (motives.push x)
    else
      let ixTy ← inferType ctx.idx[0]!
      let .const ix us := ixTy.getAppFn | throwError "internal error: no block index"
      -- `Blk.Ix` has no indices and its constructors are in block order: the minor premises are
      -- the motives themselves.
      let M ← ctx.withJs fun js => do
        let i := js[0]!
        withLocalDeclD `x (← ctx.tAt js) fun x => do
        let tgt ← mkArrow (← ctx.tAt #[i]) (mkSort v)
        let lvl := (← getLevel tgt).normalize
        let value := mkAppN (.const (mkCasesOnName ix) (lvl :: us))
          (ixTy.getAppArgs ++ #[← mkLambdaFVars #[i] tgt, i] ++ motives)
        mkLambdaFVars #[i, x] (mkApp value x)
      k motives M
  termination_by ctx.types.size - m
  go 0 #[]

/-- In a `data` block, `Tₘ.rec` for every type, the recursor in the shape of Lean's mutual
inductives: a motive per type (`motive_1`, … in block order), the minor premises of every
constructor of the block (with their block-level names), then `Tₘ`'s indices and the target. It
is `Blk.rec` at the motive `fun i x => Blk.Ix.casesOn i motive_1 … x`, whose minor premises are
these by unfolding, but for a hypothesis by `IPolyIso.Mem` (a nested argument with positions at
several types): that one is given to each type of the argument at its constructor of `Blk.Ix`,
where the motive is the type's (`splitMinors`). Also the computation rules `Tₘ.rec_cᵢ` of the
constructors of each type, with the induction hypotheses by the recursors of their types: they
are the block-level rules `Blk.rec_cᵢ` by unfolding. -/
def genTypeRecs : TermElabM Unit := do
  unless ctx.isBlock do return
  let fresh := ctx.freshLevels 1
  let v := Level.param fresh[0]!
  ctx.withTypeMotives v fun motives M => do
  let app (idx : Array Expr) (x : Expr) : TermElabM Expr := do
    match ← ctx.typeAt? idx[0]! with
    | some (k, uidx) => return mkAppN motives[k]! (uidx.push x)
    | none => return (mkAppN M (idx.push x)).headBeta
  ctx.withMinors (·.fname) (ctx.recMinorTyWith app (split := true)) fun minors => do
  let bminors ← ctx.splitMinors M minors
  -- `Tₘ.rec`
  for m in [0:ctx.types.size] do
    let t := ctx.types[m]!
    withLocalDeclD `t (← ctx.tyAt m t.idx) fun tv => do
    let xs := ctx.params ++ motives ++ minors ++ t.idx ++ #[tv]
    let value ← ctx.genAt ctx.recN [v] (#[M] ++ bminors ++ ctx.wrap m t.idx ++ #[tv])
    let (type, value) ← withBinderInfo (ctx.params ++ t.idx) .implicit do
      return (← mkForallFVars xs (mkAppN motives[m]! (t.idx.push tv)), ← mkLambdaFVars xs value)
    let n := ctx.tyGen m "rec"
    addDef n (← ctx.levelParamsOf fresh #[type, value]) type value t.ref
    addAttrs n #[← `(Parser.Term.attrInstance| elab_as_elim)]
  -- `Tₘ.rec_cᵢ`
  let recAt (idx : Array Expr) (x : Expr) : TermElabM Expr := do
    match ← ctx.typeAt? idx[0]! with
    | some (k, uidx) => ctx.genAt (ctx.tyGen k "rec") [v] (motives ++ minors ++ uidx.push x)
    | none => ctx.genAt ctx.recN [v] (#[M] ++ bminors ++ idx.push x)
  for c in ctx.ctors, k in [0:ctx.ctors.size] do
    ctx.withTArgs c fun ys σ => do
    let lhs ← recAt (c.idx.map σ) (← ctx.tCtorApp c ys)
    let rhs := mkAppN minors[k]! (ys ++ (← ctx.recIHVals recAt c ys σ (split := true)))
    let stmt ← mkEq lhs rhs
    let value := mkAppN (← ctx.constWith (ctx.recRuleN c) [v]) (ctx.params ++ #[M] ++ ys ++ bminors)
    unless ← isDefEq stmt (← inferType value) do
      throwError "internal error: the rule of the block is not{indentExpr stmt}"
    let xs := ctx.params ++ motives ++ ys ++ minors
    let (type, value) ← withBinderInfo ctx.params .implicit do
      return (← mkForallFVars xs stmt, ← mkLambdaFVars xs value)
    let n := ctx.tName' c "rec_" ""
    addThm n (← ctx.levelParamsOf fresh #[type]) type value ctx.types[c.owner]!.ref
    addSimp n

end Ctx

end Codata.Gen
