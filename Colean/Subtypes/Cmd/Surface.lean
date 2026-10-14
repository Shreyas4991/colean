import Colean.Subtypes.Cmd.Extras

/-!
# The command, step 4: the surface

*Spec.* Input: the constructor list and the declarations of steps 2–3. Output: the type-specific
conveniences, assembled without tactic proofs from what exists:

* the constructors `T.cᵢ := T.ctor (T.F.cᵢ …)` with `T.dtor_cᵢ`, `T.ctor_cᵢ`, injectivity and
  disjointness (`Codata.inj_of`, `Codata.ne_of` at `T.F.cᵢ.injEq`), and `T.casesOn` (a match on
  `F` closed by `ctor_dtor`, the `cases` eliminator) with `T.casesOn_cᵢ`;
* `T.rec_cᵢ` and `T.fold_cᵢ`, the computation rules at each constructor;
* in mutual blocks, the per-type types `Tₘ` and the aliases `Tₘ.corec`, `Tₘ.bisim`, `Tₘ.fold`;
* the inductive characterisation `T.F.Rel` of the canonical relation, with `T.F.rel_map`. This
  one is proved by tactic and generated before the model (the model's `rel_ofC` and the
  contract's `bisim` are stated with it): a boundary violation recorded in `architecture.md`.
-/

open Lean Elab Command Lean.Parser.Term

namespace Codata

open Ctx

/-- `F.Rel`, the lifting to relations, and `F.rel_map`; for `codata` only. -/
def genRel (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let xTy ← ctx.famTy
  let ib ← ctx.ixB
  let jB ← ctx.jB
  let holes ← ctx.holes
  let jArgs := ctx.jArgs
  let X ← `(X)
  let Y ← `(Y)
  let fTy ← ctx.famFn X Y
  let FX ← ctx.atI (← `($(ctx.Fp) X))
  let FY ← ctx.atI (← `($(ctx.Fp) Y))
  -- `F.Rel`: same constructor, equal non-recursive data, related recursive arguments.
  let relCtors ← ctx.ctors.mapM fun c => do
    let mut bs : Array (TSyntax ``bracketedBinderF) := #[]
    let mut hyps : Array (TSyntax ``bracketedBinderF) := #[]
    let mut xs : Array Term := #[]
    let mut ys : Array Term := #[]
    for g in c.groups do
      match g.kind with
      | .data =>
        bs := bs.push (← mkBinder g.implicit g.ids g.ty)
        xs := xs ++ g.ids.map idT
        ys := ys ++ g.ids.map idT
      | .pos idx =>
        let Xi ← appT X idx
        let Yi ← appT Y idx
        for t in g.ids do
          let t' := prime t
          bs := bs.push (← `(bracketedBinderF| ($t : $Xi)))
          bs := bs.push (← `(bracketedBinderF| ($t' : $Yi)))
          hyps := hyps.push (← `(bracketedBinderF| (_ : R $holes* $t $t')))
          xs := xs.push (idT t)
          ys := ys.push (idT t')
      | .fn tele idx =>
        let Xi ← mkPi tele (← appT X idx)
        let Yi ← mkPi tele (← appT Y idx)
        let ps := teleIds tele
        for t in g.ids do
          let t' := prime t
          bs := bs.push (← `(bracketedBinderF| ($t : $Xi)))
          bs := bs.push (← `(bracketedBinderF| ($t' : $Yi)))
          hyps := hyps.push
            (← `(bracketedBinderF| (_ : ∀ $[$ps:ident]*, R $holes* ($t $ps*) ($t' $ps*))))
          xs := xs.push (idT t)
          ys := ys.push (idT t')
      | .occ info =>
        let Xi ← info.tree.ty fun idx => appT X idx
        let Yi ← info.tree.ty fun idx => appT Y idx
        let o := info.o
        for t in g.ids do
          let t' := prime t
          bs := bs.push (← `(bracketedBinderF| ($t : $Xi)))
          bs := bs.push (← `(bracketedBinderF| ($t' : $Yi)))
          -- The packed index is bound by name: a `_` index leaves a metavariable that
          -- unification cannot solve when a hole's index is not a variable (e.g. `p.1`).
          let pId ← freshId "p"
          let pProjs ← ctx.projs (idT pId)
          let RP ← if ctx.k == 1 then `(R) else `(fun $pId:ident => R $pProjs*)
          hyps := hyps.push (← if info.indexed then
              `(bracketedBinderF| (_ : Codata.IOcc.Rel $o $o $RP $t $t'))
            else `(bracketedBinderF| (_ : Codata.Occ.Rel $o $o (R $holes*) $t $t')))
          xs := xs.push (idT t)
          ys := ys.push (idT t')
    let lhs ← ctx.fApp c X xs
    let rhs ← ctx.fApp c Y ys
    `(Parser.Command.ctor| | $(c.fname):ident $[$bs]* $[$hyps]* : $(ctx.Rel) R $lhs $rhs)
  let relTy ← ctx.famRel X Y
  if ctx.idxed then
    elabCommand (← `(inductive $(ctx.Rel):ident $[$pImp]* {X Y : $xTy} (R : $relTy) :
        ∀ $[$ib]*, $FX → $FY → Prop where
      $[$relCtors:ctor]*))
  else
    elabCommand (← `(inductive $(ctx.Rel):ident $[$pImp]* {X Y : $xTy} (R : $relTy) :
        $FX → $FY → Prop where
      $[$relCtors:ctor]*))
  let rTy ← ctx.famRel Y (← `(Z))
  let gTy' ← ctx.famFn X (← `(Z))
  let hTy ← if ctx.idxed then `(∀ $[$jB]* x, R $jArgs* (f $jArgs* x) (g $jArgs* x))
    else `(∀ x, R (f x) (g x))
  elabCommand (← `(theorem $(ctx.Frel_map):ident $[$pImp]* {X Y Z : $xTy}
      (R : $rTy) (f : $fTy) (g : $gTy') $[$ib]* (a : $FX) (h : $hTy) :
      $(ctx.Rel) R ($(ctx.Fmap) f a) ($(ctx.Fmap) g a) := by
    cases a
    all_goals simp only [$(ctx.Fmap):ident]
    all_goals constructor
    all_goals intros
    all_goals first | apply h | (apply Codata.Occ.rel_map; intro; apply h) | (apply Codata.IOcc.rel_map; intro; intro; apply h)))

/-- The individual constructors, with their destructor equations, the `ctor` equations,
injectivity and disjointness (the last two when well-typed). -/
def genCtors (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  for c in ctx.ctors do
    let cId := ctx.tCtor c
    let bs ← binders c
    let fapp ← ctx.fApp c ctx.Tp (c.allIds.map idT)
    let capp ← ctx.tApp c
    let Tc ← ctx.tyAt c
    let FTc ← appT (← `($(ctx.Fp) $(ctx.Tp))) c.idx
    elabCommand (← `(def $cId:ident $[$pImp]* $[$bs]* : $Tc := $(ctx.ctor) $fapp))
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "dtor_" ""):ident $[$pImp]* $[$bs]* :
        $(ctx.dtor) ($capp : $Tc) = $fapp := $(ctx.dtor_ctor) $fapp))
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "ctor_" ""):ident $[$pImp]* $[$bs]* :
        $(ctx.ctor) ($fapp : $FTc) = $capp := rfl))
  for c in ctx.ctors do
    if c.args.isEmpty || c.hasImplicit || c.dependent || c.idxDependent then continue
    let bs ← binders c
    let bs' ← binders' c
    let Tc ← ctx.tyAt c
    let capp ← mkAppT (ctx.tCtor c) (c.args.map idT)
    let capp' ← mkAppT (ctx.tCtor c) ((c.args.map prime).map idT)
    let eqs ← (c.args.zip (c.args.map prime)).mapM fun (x, x') => `($x:ident = $x':ident)
    let conj ← eqs.foldrM (init := eqs.back!) (start := eqs.size - 1) fun e acc => `($e ∧ $acc)
    let injEq := mkIdent (ctx.F.getId ++ c.fname.getId ++ `injEq)
    let fapp ← mkAppT (ctx.fCtor c) (c.args.map idT)
    let fapp' ← mkAppT (ctx.fCtor c) ((c.args.map prime).map idT)
    let args := c.args.map idT ++ (c.args.map prime).map idT
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "" "_inj"):ident $[$pImp]* $[$bs]*
        $[$bs']* : ($capp : $Tc) = $capp' ↔ $conj :=
      Codata.inj_of $(ctx.ctor) $(ctx.ctor_injective) $fapp $fapp' ($injEq $args:term*)))
  for c in ctx.ctors do
    for c' in ctx.ctors do
      if c.name.getId == c'.name.getId || c.owner != c'.owner then continue
      unless idxEq c.idx c'.idx && !c.idxDependent && !c'.idxDependent do continue
      let bs ← binders c
      let bs' ← binders' c'
      let Tc ← ctx.tyAt c
      let capp ← mkAppT (ctx.tCtor c) (c.args.map idT)
      let capp' ← mkAppT (ctx.tCtor c') ((c'.args.map prime).map idT)
      let name := mkIdent (ctx.tyName c.owner ++
        Name.mkSimple (c.name.getId.toString ++ "_ne_" ++ c'.name.getId.toString))
      let dtorC ← mkAppT (ctx.tName' c "dtor_" "") (c.args.map idT)
      let dtorC' ← mkAppT (ctx.tName' c' "dtor_" "") ((c'.args.map prime).map idT)
      elabCommand (← `(@[simp] theorem $name:ident $[$pImp]* $[$bs]* $[$bs']* :
          ($capp : $Tc) ≠ $capp' :=
        Codata.ne_of $(ctx.dtor) $dtorC $dtorC' fun h => nomatch h))

/-- Case analysis, per type of the block: `t = ctor (dtor t)`, and `dtor t` is an inductive
value whose possible constructors are those of the type. -/
def genCases (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let pTerms := ctx.pTerms
  let ib ← ctx.uIxB
  let jB ← ctx.uJB
  let iArg := ctx.uIArgs
  let motive := ctx.motiveId
  for m in [0:ctx.types.size] do
    let ctors := ctx.ctors.filter (·.owner == m)
    let Tm ← ctx.tyP m
    let mTy ← if ctx.uIdxed then `(∀ $[$jB]*, $(← appT Tm ctx.uJArgs) → Sort _)
      else `($Tm → Sort _)
    let mI ← appT (idT motive) iArg
    let Ti ← ctx.tyAtU m
    let FTi ← appT (← `($(ctx.Fp) $(ctx.Tp))) (ctx.fullArgs m)
    let casesOnAux := ctx.tyId m "casesOnAux"
    let casesOnId := ctx.tyId m "casesOn"
    let casesOn_ctor := ctx.tyId m "casesOn_ctor"
    let minors ← ctors.mapM fun c => do
      let bs ← binders c
      let capp ← ctx.tApp c
      let mc ← appT (idT motive) (ctx.uIdxOf c)
      let ty ← if c.groups.isEmpty then `($mc $capp) else `(∀ $[$bs]*, $mc $capp)
      `(bracketedBinderF| ($(c.name) : $ty))
    let auxAlts : Array (TSyntax ``matchAlt) ← ctors.mapM fun c => do
      ctx.uAlt c #[← ctx.fPat c] (← mkAppT c.name ((ctx.valArgs c).map idT))
    let discrsY := ctx.uDiscrs (← `(y))
    elabCommand (← `(def $casesOnAux:ident $[$pImp]* {$motive : $mTy} $[$ib]* (y : $FTi)
        $[$minors]* : $mI ($(ctx.ctor) y) := match $[$discrsY:term],* with $auxAlts:matchAlt*))
    let minorIds := ctors.map fun c => idT c.name
    elabCommand (← `(@[elab_as_elim, cases_eliminator]
      def $casesOnId:ident $[$pImp]* {$motive : $mTy} $[$ib]* (t : $Ti) $[$minors]* :
          $mI t :=
        (congrArg $mI ($(ctx.ctor_dtor) t)).mp ($casesOnAux ($(ctx.dtor) t) $minorIds:term*)))
    -- Its computation rules: the cast disappears once `dtor (ctor y) = y` is substituted.
    elabCommand (← `(theorem $casesOn_ctor:ident $[$pImp]* {$motive : $mTy} $[$ib]*
        (y : $FTi) $[$minors]* :
        @$casesOnId $pTerms:term* $motive $iArg:term* ($(ctx.ctor) y) $minorIds:term* =
          $casesOnAux y $minorIds:term* :=
      Codata.cast_ctor_dtor $(ctx.ctor) $(ctx.dtor) $(ctx.ctor_dtor) $(ctx.dtor_ctor)
        (fun y => $casesOnAux y $minorIds:term*) y))
    for c in ctors do
      let bs ← binders c
      let capp ← ctx.tApp c
      let fapp ← ctx.fApp c ctx.Tp (c.allIds.map idT)
      let rhs ← mkAppT c.name (c.args.map idT)
      let cidx := ctx.uIdxOf c
      elabCommand (← `(@[simp] theorem $(ctx.tName' c "casesOn_" ""):ident $[$pImp]*
          {$motive : $mTy} $[$bs]* $[$minors]* :
          @$casesOnId $pTerms:term* $motive $cidx:term* $capp $minorIds:term* = $rhs :=
        $casesOn_ctor $fapp $minorIds:term*))

/-! ### Mutual blocks: the user-facing types and aliases -/

/-- In a mutual block, the user-facing types: `Tₘ params i… := Blk params .Tₘ i…`. Defined
after the family and before anything that mentions the types in a binder. -/
def genTypes (ctx : Ctx) : CommandElabM Unit := do
  unless ctx.isMutual do return
  let pExp := ctx.pExp
  let ixBExp ← ctx.uIxBExp
  for m in [0:ctx.types.size] do
    let body ← appT ctx.Tp (ctx.fullArgs m)
    elabCommand (← `(def $(ctx.types[m]!):ident $[$pExp]* $[$ixBExp]* : Type _ := $body))

/-- In a mutual `codata` block, the block-level `corec` and `bisim` restricted to each type.
`dtor` and `ctor` are not aliased: dot notation `t.dtor` resolves to the block-level `dtor`
through the definition of the type, and an alias at the head of a lemma would not be seen
through by `rw`. -/
def genAliases (ctx : Ctx) : CommandElabM Unit := do
  unless ctx.isMutual do return
  let pImp := ctx.pImp
  let xTy ← ctx.famTy
  let ixBExp ← ctx.ixBExp
  let iArgs := ctx.iArgs
  let S := ctx.Sid
  let cTy ← ctx.famFn (idT S) (← `($(ctx.Fp) $S))
  let RTy ← ctx.famRel ctx.Tp ctx.Tp
  let Rixy ← appT (← `(R)) (iArgs ++ #[← `(x), ← `(y)])
  let HTy ← `(∀ $[$ixBExp]* x y, $Rixy → $(ctx.Rel) R ($(ctx.dtor) x) ($(ctx.dtor) y))
  let ib ← ctx.uIxB
  for m in [0:ctx.types.size] do
    let Ti ← ctx.tyAtU m
    let Si ← appT (idT S) (ctx.fullArgs m)
    let Rm ← appT (← `(R)) (ctx.fullArgs m ++ #[← `(x), ← `(y)])
    elabCommand (← `(abbrev $(ctx.tyId m "corec"):ident $[$pImp]* {$S : $xTy} (c : $cTy) $[$ib]*
        (s : $Si) : $Ti := $(ctx.corec) c s))
    elabCommand (← `(theorem $(ctx.tyId m "bisim"):ident $[$pImp]* (R : $RTy) (H : $HTy) $[$ib]*
        {x y : $Ti} (h : $Rm) : x = y := $(ctx.bisim) R H h))

/-- The computation rules of `T.rec` on the constructors, `T.rec_cᵢ`, and the `fold` equations
`T.fold_cᵢ`. -/
def genRecLemmas (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let pTerms := ctx.pTerms
  let jB ← ctx.jB
  let motive := ctx.motiveId
  let mTy ← if ctx.idxed then `(∀ $[$jB]*, $(← appT ctx.Tp ctx.jArgs) → Sort _)
    else `($(ctx.Tp) → Sort _)
  let S := ctx.Sid
  let xTy ← ctx.famTy
  let aTy ← ctx.famFn (← `($(ctx.Fp) $S)) (idT S)
  let minors ← recMinors ctx
  let minorIds := ctx.ctors.map fun c => idT c.fname
  let recApp (ix : Array Term) (t : Term) : CommandElabM Term :=
    `(@$(ctx.recId) $pTerms* $motive $minorIds* $ix* $t)
  for c in ctx.ctors do
    let bs ← binders c
    let capp ← ctx.tApp c
    let fapp ← ctx.fApp c ctx.Tp (c.allIds.map idT)
    let mut ihArgs : Array Term := #[]
    for g in c.groups do
      match g.kind with
      | .data => pure ()
      | .pos idx =>
        for x in g.ids do
          ihArgs := ihArgs.push (← recApp idx (idT x))
      | .fn tele idx =>
        let ys := (teleIds tele).map idT
        let ys' := teleIds tele
        for x in g.ids do
          let body ← recApp idx (← `($x $ys*))
          ihArgs := ihArgs.push (← `(fun $[$ys':ident]* => $body))
      | .occ info =>
        for x in g.ids do
          let toC := occId info.indexed `toC
          let o := info.o
          let idx ← if info.indexed then ctx.projs (← `($(info.pidx) ($toC $o $x).1 q))
            else pure info.idx
          let body ← recApp idx (← `(($toC $o $x).2 q))
          ihArgs := ihArgs.push (← `(fun q => $body))
    let rhs ← mkAppT c.fname (c.args.map idT ++ ihArgs)
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "rec_" ""):ident $[$pImp]* {$motive : $mTy}
        $[$bs]* $[$minors]* : $(← recApp c.idx capp) = $rhs :=
      $(ctx.rec_ctor) $minorIds:term* $fapp))
  -- The `fold` equations on the constructors.
  for c in ctx.ctors do
    let bs ← binders c
    let capp ← ctx.tApp c
    let fapp ← ctx.fApp c ctx.Tp (c.allIds.map idT)
    let mapped ← ctx.mappedArgs c false (some fun x => `($(ctx.fold) a $x))
      (some (← `(fun t => $(ctx.fold) a t)))
    let rhs ← appT (← `(a)) (c.idx ++ #[← ctx.fApp c (idT S) mapped])
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "fold_" ""):ident $[$pImp]* {$S : $xTy}
        (a : $aTy) $[$bs]* : $(ctx.fold) a $capp = $rhs := $(ctx.fold_ctor) a $fapp))


/-- In a mutual `data` block, the block-level `fold` restricted to each type (`dtor` and `ctor`
are reached by dot notation, see `genAliases`). Induction stays at the block level (`Blk.rec`,
with its motive over the block), as Lean's own mutual recursors, so there is no per-type
`rec`. -/
def genDataAliases (ctx : Ctx) : CommandElabM Unit := do
  unless ctx.isMutual do return
  let pImp := ctx.pImp
  let xTy ← ctx.famTy
  let S := ctx.Sid
  let aTy ← ctx.famFn (← `($(ctx.Fp) $S)) (idT S)
  let ib ← ctx.uIxB
  for m in [0:ctx.types.size] do
    let Ti ← ctx.tyAtU m
    let Si ← appT (idT S) (ctx.fullArgs m)
    elabCommand (← `(abbrev $(ctx.tyId m "fold"):ident $[$pImp]* {$S : $xTy} (a : $aTy) $[$ib]*
        (t : $Ti) : $Si := $(ctx.fold) a t))

end Codata
