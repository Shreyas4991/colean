import Colean.Data
import Colean.CodataCmd

/-!
# The `data` command

The inductive twin of `codata`, with the same syntax and the same scope (parameters, indices,
recursive arguments under telescopes):

```
data FinList (α : Type u)
  | nil
  | cons (a : α) (l : FinList α)

data Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)
```

The analysis of the declaration and the generators of `T.F`, the signature `T.sig` and the
isomorphism `T.toC`/`T.ofC` are those of `CodataCmd.lean`; `T.F.Rel` is not generated. The
command then produces, from the generic theory of `Data.lean`:

* the contract: `T := Intype sig`, `T.ctor : F T i → T i`, `T.fold : (∀ i, F S i → S i) →
  T i → S i` for a family `S` in any universe, `T.fold_ctor`, and `T.contract : Data.Contract`,
  whose `induction` field (for the canonical lifting `Data.All`) is instantiated at the packed
  index directly from `Signature.induction_of`;
* derived from the contract: `T.dtor` (Lambek), `T.dtor_ctor`, `T.ctor_dtor`,
  `T.ctor_injective`, `T.fold_eq`, `T.fold_unique`; the constructors `T.ctorᵢ` with `T.dtor_ctorᵢ`,
  `T.ctor_ctorᵢ`, `T.fold_ctorᵢ`, injectivity and disjointness, and `T.casesOn`, as for `codata`;
* the dependent recursor `T.rec : {motive : ∀ i, T i → Sort v} → minors → ∀ {i} (t : T i),
  motive i t`, with one minor premise per constructor carrying an induction hypothesis for each
  recursive argument (`∀ ys, motive _ (k ys)` under a telescope), registered as the
  `induction` eliminator, and its computation rules `T.rec_ctorᵢ` as simp lemmas. It is
  `Signature.rec_of` at the packed index, with the minor premises assembled by a `match` on
  `F T i` (`T.recAux`); its computation rules are propositional, since the generic recursor is
  built from `WellFounded.fix`.

The `Prop` instance of `T.rec` is induction with per-constructor hypotheses; the contract's
`induction` with the `Data.All` hypothesis is not curried for the user.
-/

open Lean Elab Command Lean.Parser.Term

namespace Codata

/-- `data T (params) [: (i₁ : I₁) → I₂ → Type u] | ctor₁ … | ctor₂ …` declares an inductive
type, or family, as a subtype of `Raw`. -/
syntax (name := dataCmd) "data " ident (ppSpace bracketedBinder)* (" : " term)?
  codataCtor* : command

open Ctx

/-! ### The contract: the type, its constructor and its fold -/

def genDataContract (ctx : Ctx) : CommandElabM Unit := do
  let pExp := ctx.pExp
  let pImp := ctx.pImp
  let pTerms := ctx.pTerms
  let xTy ← ctx.famTy
  let ib ← ctx.ixB
  let ixBExp ← ctx.ixBExp
  let iIds := ctx.iIds
  let iArgs := ctx.iArgs
  let S := ctx.Sid
  let Ti ← ctx.atI ctx.Tp
  let FTi ← ctx.atI (← `($(ctx.Fp) $(ctx.Tp)))
  let Si ← ctx.atI (idT S)
  let aTy ← ctx.famFn (← `($(ctx.Fp) $S)) (idT S)
  let Int ← ctx.famT
  if ctx.k == 0 then
    elabCommand (← `(def $(ctx.T):ident $[$pExp]* : Type _ := $Int ()))
  else if ctx.packed then
    elabCommand (← `(def $(ctx.T):ident $[$pExp]* : ∀ $[$ixBExp]*, Type _ :=
      fun $[$iIds:ident]* => $Int $(← ctx.pack iArgs)))
  else
    elabCommand (← `(def $(ctx.T):ident $[$pExp]* : ∀ $[$ixBExp]*, Type _ := $Int))
  let cv ← mkConv ctx
  elabCommand (← `(def $(ctx.ctor):ident $[$pImp]* $[$ib]* (y : $FTi) : $Ti :=
    $(ctx.sigId `ctorI) (@$(ctx.toC) $pTerms* $Int $iArgs* y)))
  let pArgs ← ctx.projs (← `(p))
  let alg ← `(fun (p : $(ctx.Ixp)) z =>
    $(← appT (← `(a)) (pArgs ++ #[← `(@$(ctx.ofC) $pTerms* $(cv.Sp) $pArgs* z)])))
  elabCommand (← `(def $(ctx.fold):ident $[$pImp]* {$S : $xTy} (a : $aTy) $[$ib]* (t : $Ti) :
      $Si := $(ctx.sigId `foldI) (σ := $(ctx.sigp)) (S := $(cv.Sp)) (i := $(cv.pI)) $alg t))
  let foldFn ← if ctx.k == 0 then `($(ctx.fold) a)
    else `(fun $[$(← ctx.holes)]* t => $(ctx.fold) a t)
  let ay ← appT (← `(a)) (iArgs ++ #[← `($(ctx.Fmap) $foldFn y)])
  let z : Ident := ⟨(← `(z)).raw⟩
  elabCommand (← `(theorem $(ctx.fold_ctor):ident $[$pImp]* {$S : $xTy} (a : $aTy) $[$ib]*
      (y : $FTi) : $(ctx.fold) a ($(ctx.ctor) y) = $ay :=
    $(ctx.sigId `fold_ctor_of) (σ := $(ctx.sigp)) (S := $(cv.Sp)) (FS := $(cv.FSp))
      (FT := $(cv.FTp)) (i := $(cv.pI)) $(cv.toCT) $(cv.ofC) $(cv.ofCS) $(cv.map) $(cv.ofC_toCT)
      $(cv.ofC_mapTS) $(← ctx.uncurryN (← `(a)) #[z]) y))

/-! ### Derived from the contract -/

def genDataDerived (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let pTerms := ctx.pTerms
  let xTy ← ctx.famTy
  let ib ← ctx.ixB
  let ixBExp ← ctx.ixBExp
  let iArgs := ctx.iArgs
  let S := ctx.Sid
  let Ti ← ctx.atI ctx.Tp
  let FTi ← ctx.atI (← `($(ctx.Fp) $(ctx.Tp)))
  let aTy ← ctx.famFn (← `($(ctx.Fp) $S)) (idT S)
  let cv ← mkConv ctx
  let pArgs ← ctx.projs (← `(p))
  let x : Ident := ⟨(← `(x)).raw⟩
  let z : Ident := ⟨(← `(z)).raw⟩
  let t : Ident := ⟨(← `(t)).raw⟩
  let y : Ident := ⟨(← `(y)).raw⟩
  -- The contract, at the packed index; each field converts a curried piece.
  let Fpk ← if ctx.packed then
      `(fun (X : $(ctx.Ixp) → Type _) (p : $(ctx.Ixp)) =>
        $(← appT (← `($(ctx.Fp) $(← ctx.curryFam (← `(X))))) pArgs))
    else pure ctx.Fp
  let cur (f : Term) (extra : Array Ident) := ctx.curryN f extra
  let mapP ← `(fun {_ _} f {_} a => $(ctx.Fmap) $(← cur (← `(f)) #[x]) a)
  let ofCP ← `(fun {X} {p} z => @$(ctx.ofC) $pTerms* X $pArgs* z)
  let ofCmapP ← `(fun {X Y} f {p} z => @$(ctx.ofC_map) $pTerms* X Y f $pArgs* z)
  elabCommand (← `(def $(ctx.contract):ident $[$pImp]* :
      Data.Contract (I := $(ctx.Ixp)) $(cv.Tpk) $Fpk where
    map := $mapP
    map_id := fun {_ _} a => $(ctx.Fmap_id) a
    map_comp := fun {_ _ _} g f {_} a => $(ctx.Fmap_comp) $(← cur (← `(g)) #[]) $(← cur (← `(f)) #[]) a
    ctor := fun {_} y => $(ctx.ctor) y
    fold := fun {_} a {_} t => $(ctx.fold) $(← cur (← `(a)) #[z]) t
    fold_ctor := fun {_} a {_} y => $(ctx.fold_ctor) $(← cur (← `(a)) #[z]) y
    induction := $(ctx.sigId `induction_of) (σ := $(ctx.sigp)) (F := $Fpk) $mapP $(cv.toCT) $ofCP
      $(cv.toC_ofC) $(cv.ofC_toCT) $ofCmapP))
  elabCommand (← `(def $(ctx.dtor):ident $[$pImp]* $[$ib]* (t : $Ti) : $FTi :=
    Data.Contract.dtor $(ctx.contract) (i := $(cv.pI)) t))
  elabCommand (← `(theorem $(ctx.dtor_ctor):ident $[$pImp]* $[$ib]* (y : $FTi) :
      $(ctx.dtor) ($(ctx.ctor) y) = y :=
    Data.Contract.dtor_ctor $(ctx.contract) (i := $(cv.pI)) y))
  elabCommand (← `(theorem $(ctx.ctor_dtor):ident $[$pImp]* $[$ib]* (t : $Ti) :
      $(ctx.ctor) ($(ctx.dtor) t) = t :=
    Data.Contract.ctor_dtor $(ctx.contract) (i := $(cv.pI)) t))
  elabCommand (← `(theorem $(ctx.ctor_injective):ident $[$pImp]* $[$ib]* :
      Function.Injective ($(ctx.ctor) : $FTi → $Ti) :=
    Data.Contract.ctor_injective $(ctx.contract) (i := $(cv.pI))))
  -- `fold_eq` and `fold_unique`, for families in any universe.
  let foldFn ← if ctx.k == 0 then `($(ctx.fold) a)
    else `(fun $[$(← ctx.holes)]* t => $(ctx.fold) a t)
  let adt ← appT (← `(a)) (iArgs ++ #[← `($(ctx.Fmap) $foldFn ($(ctx.dtor) t))])
  elabCommand (← `(theorem $(ctx.fold_eq):ident $[$pImp]* {$S : $xTy} (a : $aTy) $[$ib]*
      (t : $Ti) : $(ctx.fold) a t = $adt :=
    Data.fold_eq_of (T := $(cv.Tpk)) (S := $(cv.Sp)) (FS := $(cv.FSp)) (FT := $(cv.FTp))
      (i := $(cv.pI)) (fun {_} t => $(ctx.dtor) t) (fun {_} y => $(ctx.ctor) y)
      (fun a {_} t => $(ctx.fold) $(← cur (← `(a)) #[z]) t) $(cv.map)
      (fun a {_} y => $(ctx.fold_ctor) $(← cur (← `(a)) #[z]) y) (fun {_} t => $(ctx.ctor_dtor) t)
      $(← ctx.uncurryN (← `(a)) #[z]) t))
  let hTy ← ctx.famFn ctx.Tp (idT S)
  let hy ← appT (← `(h)) (iArgs ++ #[← `($(ctx.ctor) y)])
  let ahy ← appT (← `(a)) (iArgs ++ #[← `($(ctx.Fmap) h y)])
  let hhTy ← `(∀ $[$ixBExp]* (y : $FTi), $hy = $ahy)
  let ht ← appT (← `(h)) (iArgs ++ #[← `(t)])
  elabCommand (← `(theorem $(ctx.fold_unique):ident $[$pImp]* {$S : $xTy} (a : $aTy) (h : $hTy)
      (hh : $hhTy) $[$ib]* (t : $Ti) : $ht = $(ctx.fold) a t :=
    Data.fold_unique_of (T := $(cv.Tpk)) (F := $Fpk) (S := $(cv.Sp)) (FS := $(cv.FSp))
      (i := $(cv.pI)) $mapP (fun {_} y => $(ctx.ctor) y) (Data.Contract.induction $(ctx.contract))
      (fun a {_} t => $(ctx.fold) $(← cur (← `(a)) #[z]) t)
      (fun {_} f {_} a => $(ctx.Fmap) $(← cur (← `(f)) #[x]) a)
      (fun a {_} y => $(ctx.fold_ctor) $(← cur (← `(a)) #[z]) y)
      (fun {_} g f {_} z => $(ctx.Fmap_comp) $(← cur (← `(g)) #[]) $(← cur (← `(f)) #[]) z)
      $(← ctx.uncurryN (← `(a)) #[z]) $(← ctx.uncurryN (← `(h)) #[t])
      $(← ctx.uncurryN (← `(hh)) #[y]) t))

/-! ### The dependent recursor -/

/-- `x_ih`, the induction hypothesis for the argument `x`. -/
def ihId (x : Ident) : Ident := mkIdent (x.getId.appendAfter "_ih")

/-- The recursor with one minor premise per constructor, the `fold` equations on the
constructors, and the computation rules. -/
def genRec (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let pTerms := ctx.pTerms
  let ib ← ctx.ixB
  let jB ← ctx.jB
  let iArg := ctx.iArg
  let motive := ctx.motiveId
  let mTy ← if ctx.idxed then `(∀ $[$jB]*, $(← appT ctx.Tp ctx.jArgs) → Sort _)
    else `($(ctx.Tp) → Sort _)
  let mI ← appT (idT motive) iArg
  let Ti ← ctx.atI ctx.Tp
  let FTi ← ctx.atI (← `($(ctx.Fp) $(ctx.Tp)))
  let Int ← ctx.famT
  let cv ← mkConv ctx
  let pArgs ← ctx.projs (← `(p))
  let S := ctx.Sid
  let xTy ← ctx.famTy
  let aTy ← ctx.famFn (← `($(ctx.Fp) $S)) (idT S)
  -- The minor premises: the constructor's binders, then an induction hypothesis per recursive
  -- argument.
  let minors ← ctx.ctors.mapM fun c => do
    let bs ← binders c
    let capp ← ctx.tApp c
    let mc ← appT (idT motive) c.idx
    let mut ihs : Array (TSyntax ``bracketedBinderF) := #[]
    for g in c.groups do
      match g.kind with
      | .data => pure ()
      | .pos idx =>
        for x in g.ids do
          ihs := ihs.push (← `(bracketedBinderF| ($(ihId x) : $(← appT (idT motive) (idx ++ #[idT x])))))
      | .fn tele idx =>
        let tbs ← teleBinders tele
        let ys := (teleIds tele).map idT
        for x in g.ids do
          let body ← appT (idT motive) (idx ++ #[← `($x $ys*)])
          ihs := ihs.push (← `(bracketedBinderF| ($(ihId x) : ∀ $[$tbs]*, $body)))
    let allBs := bs ++ ihs
    let ty ← if allBs.isEmpty then `($mc $capp) else `(∀ $[$allBs]*, $mc $capp)
    `(bracketedBinderF| ($(c.name) : $ty))
  let minorIds := ctx.ctors.map fun c => idT c.name
  -- `recAux`: the minor premises assembled into the hypothesis of the generic recursor, whose
  -- induction hypotheses are indexed by the positions of `toC`.
  let bId : Ident := ⟨(← `(b)).raw⟩
  let ihId' : Ident := ⟨(← `(ih)).raw⟩
  let idxB ← ctx.projs (← `(Codata.Signature.idx $(ctx.sigp) $bId))
  let mIdxB ← appT (idT motive) idxB
  let ihTy ← `(∀ $bId:ident, $mIdxB ((@$(ctx.toC) $pTerms* $Int $iArg* y).child $bId))
  let auxAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.mapM fun c => do
    let valData := (ctx.valDataIds c).map idT
    let mut ihArgs : Array Term := #[]
    for g in c.groups do
      match g.kind with
      | .data => pure ()
      | .pos _ =>
        for x in g.ids do
          ihArgs := ihArgs.push (← `($ihId' (@$(ctx.bCtor c x) $pTerms* $valData*)))
      | .fn tele _ =>
        let ys := teleIds tele
        for x in g.ids do
          ihArgs := ihArgs.push
            (← `(fun $[$ys:ident]* => $ihId' (@$(ctx.bCtor c x) $pTerms* $valData* $ys*)))
    let rhs ← mkAppT c.name ((ctx.valArgs c).map idT ++ ihArgs)
    ctx.alt c #[← ctx.fPat c] (← `(fun $ihId':ident => $rhs))
  let discrsY := ctx.discrs (← `(y))
  elabCommand (← `(def $(ctx.recAux):ident $[$pImp]* {$motive : $mTy} $[$minors]* $[$ib]*
      (y : $FTi) : $ihTy → $mI ($(ctx.ctor) y) := match $[$discrsY:term],* with $auxAlts:matchAlt*))
  let H ← `(fun p y ih => @$(ctx.recAux) $pTerms* $motive $minorIds* $pArgs* y ih)
  let motiveP ← ctx.uncurryN (idT motive) #[⟨(← `(t)).raw⟩]
  elabCommand (← `(@[elab_as_elim, induction_eliminator]
    def $(ctx.recId):ident $[$pImp]* {$motive : $mTy} $[$minors]* $[$ib]* (t : $Ti) : $mI t :=
      $(ctx.sigId `rec_of) (σ := $(ctx.sigp)) (FT := $(cv.FTp)) (motive := $motiveP)
        (i := $(cv.pI)) $(cv.toCT) $(cv.ofC) $(cv.toC_ofC) $H t))
  -- Its computation rules.
  let recApp (ix : Array Term) (t : Term) : CommandElabM Term :=
    `(@$(ctx.recId) $pTerms* $motive $minorIds* $ix* $t)
  let ihFn ← `(fun $bId:ident =>
    $(← recApp idxB (← `((@$(ctx.toC) $pTerms* $Int $iArg* y).child $bId))))
  elabCommand (← `(theorem $(ctx.rec_ctor):ident $[$pImp]* {$motive : $mTy} $[$minors]* $[$ib]*
      (y : $FTi) : $(← recApp iArg (← `($(ctx.ctor) y))) =
        @$(ctx.recAux) $pTerms* $motive $minorIds* $iArg* y $ihFn :=
    $(ctx.sigId `rec_of_ctor) (σ := $(ctx.sigp)) (FT := $(cv.FTp)) (motive := $motiveP)
      (i := $(cv.pI)) $(cv.toCT) $(cv.ofC) $(cv.toC_ofC) $(cv.ofC_toCT) $H y))
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
    let rhs ← mkAppT c.name (c.args.map idT ++ ihArgs)
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "rec_" ""):ident $[$pImp]* {$motive : $mTy}
        $[$bs]* $[$minors]* : $(← recApp c.idx capp) = $rhs :=
      $(ctx.rec_ctor) $minorIds:term* $fapp))
  -- The `fold` equations on the constructors.
  for c in ctx.ctors do
    let bs ← binders c
    let capp ← ctx.tApp c
    let fapp ← ctx.fApp c ctx.Tp (c.allIds.map idT)
    let mapped ← ctx.mappedArgs c false (some fun x => `($(ctx.fold) a $x))
    let rhs ← appT (← `(a)) (c.idx ++ #[← ctx.fApp c (idT S) mapped])
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "fold_" ""):ident $[$pImp]* {$S : $xTy}
        (a : $aTy) $[$bs]* : $(ctx.fold) a $capp = $rhs := $(ctx.fold_ctor) a $fapp))

/-! ### The command -/

@[command_elab dataCmd] def elabData : CommandElab := fun stx => do
  let `(data $T:ident $paramsStx:bracketedBinder* $[: $sortStx]? $ctorsStx:codataCtor*) := stx
    | throwUnsupportedSyntax
  let ctx ← mkCtx false T paramsStx sortStx ctorsStx
  genFunctor ctx
  genSignature ctx
  genIso ctx
  -- The encoding decides equality of shapes classically, and the recursor is by well-founded
  -- recursion: the type's constructors and recursors are noncomputable.
  elabCommand (← `(noncomputable section))
  genDataContract ctx
  genDataDerived ctx
  genCtors ctx
  genCases ctx
  genRec ctx
  elabCommand (← `(end))

end Codata
