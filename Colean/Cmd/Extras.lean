import Colean.Cmd.Framework

/-!
# The command, step 2b: what is read off the model beyond the contract

*Spec.* Input: the model (signature, isomorphism, `T.ctor`). Output, all justified by the
encoding rather than by the contract (`architecture.md`, step 2b):

* the dependent recursor `T.rec` into any `Sort`, from the model's well-founded recursion, with
  its computation rule `T.rec_ctor` (propositional).

This is a candidate for derivation from the contract.
-/

open Lean Elab Command Lean.Parser.Term

namespace Codata

open Ctx

/-- `x_ih`, the induction hypothesis for the argument `x`. -/
def ihId (x : Ident) : Ident := mkIdent (x.getId.appendAfter "_ih")

/-- The minor premises of `T.rec`: the constructor's binders, then an induction hypothesis per
recursive argument (`∀ ys, motive _ (k ys)` under a telescope, `∀ q, motive _ ((toC o x).2 q)`
for a nested argument). -/
def recMinors (ctx : Ctx) : CommandElabM (Array (TSyntax ``bracketedBinderF)) := do
  let motive := ctx.motiveId
  ctx.ctors.mapM fun c => do
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
      | .occ info =>
        for x in g.ids do
          let toC := occId info.indexed `toC
          let o := info.o
          let idx ← if info.indexed then ctx.projs (← `($(info.pidx) ($toC $o $x).1 q))
            else pure info.idx
          let body ← appT (idT motive) (idx ++ #[← `(($toC $o $x).2 q)])
          ihs := ihs.push (← `(bracketedBinderF| ($(ihId x) : ∀ q, $body)))
    let allBs := bs ++ ihs
    let ty ← if allBs.isEmpty then `($mc $capp) else `(∀ $[$allBs]*, $mc $capp)
    `(bracketedBinderF| ($(c.fname) : $ty))

/-! ### The dependent recursor -/

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
  let minors ← recMinors ctx
  let minorIds := ctx.ctors.map fun c => idT c.fname
  -- `recAux`: the minor premises assembled into the hypothesis of the generic recursor, whose
  -- induction hypotheses are indexed by the positions of `toC`.
  let bId : Ident := ⟨(← `(b)).raw⟩
  let ihId' : Ident := ⟨(← `(ih)).raw⟩
  let idxB ← ctx.projs (← `(Codata.Signature.idx $(ctx.sigp) $bId))
  let mIdxB ← appT (idT motive) idxB
  let ihTy ← `(∀ $bId:ident, $mIdxB ((@$(ctx.toC) $pTerms* $Int $iArg* y).child $bId))
  let auxAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.mapM fun c => do
    let mut ihArgs : Array Term := #[]
    for g in c.groups do
      match g.kind with
      | .data => pure ()
      | .pos _ =>
        for x in g.ids do
          ihArgs := ihArgs.push (← `($ihId' $(← ctx.bApp c x #[])))
      | .fn tele _ =>
        let ys := teleIds tele
        for x in g.ids do
          ihArgs := ihArgs.push
            (← `(fun $[$ys:ident]* => $ihId' $(← ctx.bApp c x (ys.map idT))))
      | .occ .. =>
        for x in g.ids do
          ihArgs := ihArgs.push (← `(fun q => $ihId' $(← ctx.bApp c x #[← `(q)])))
    let rhs ← mkAppT c.fname ((ctx.valArgs c).map idT ++ ihArgs)
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
end Codata
