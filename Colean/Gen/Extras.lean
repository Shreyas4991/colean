import Colean.Gen.Framework

/-!
# Generators on `Expr`, step 2b: the dependent recursor

*Spec.* Input: the model (signature, isomorphism, `T.ctor`) and the constructors `T.cᵢ` (step
4). Output, for `data`, justified by the encoding rather than by the contract (`architecture.md`,
step 2b):

* `T.rec`, the dependent recursor into any `Sort`, with one minor premise per constructor
  carrying an induction hypothesis per recursive argument (`∀ ys, motive _ (k ys)` under a
  telescope, `∀ q, motive _ ((toC o x).2 q)` for a nested argument), registered as the
  `induction` eliminator; it is `Signature.rec_of` at the packed index, the minor premises
  assembled by cases on `F T i` (`T.recAux`);
* its computation rule `T.rec_ctor` (propositional: the generic recursor is by well-founded
  recursion).

The minor premises are stated with the constructors `T.cᵢ`, so this runs after them.
-/

open Lean Meta Elab Term

namespace Codata.Gen

namespace Ctx

variable (ctx : Ctx)

/-- `@T.c params args`. -/
def tCtorApp (c : Ctor) (ys : Array Expr) : MetaM Expr := do
  ctx.genAt (ctx.tCtor c) [] ys

/-- `@T.F.c params X args`, for `X` at universe `w`. -/
def fCtorApp (c : Ctor) (w : Level) (X : Expr) (ys : Array Expr) : MetaM Expr := do
  ctx.genAt (ctx.fCtor c) [w] (#[X] ++ ys)

/-- Run `k` on the arguments of `c` as those of `T.c`: the occurrences are `Tₘ params idx`, with
the per-type constants in a block. -/
def withTArgs (c : Ctor) (k : Array Expr → (Expr → Expr) → TermElabM α)
    (rename : Name → Name := id) : TermElabM α := do
  let tys ← (Array.range ctx.types.size).mapM fun m => ctx.constWith (ctx.tyName m) []
  ctx.withArgsAtU c (fun m idx => mkAppN tys[m]! (ctx.params ++ idx)) (← ctx.tLvl) k rename

/-- Open the telescope of an argument of kind `.fn n` of `T.c`, with type `ty`: `k ys idx` with
the bound variables and the family-level index arguments of the result. -/
def openTFn (n : Nat) (ty : Expr) (k : Array Expr → Array Expr → TermElabM α) : TermElabM α :=
  withReducible <| forallBoundedTelescope ty n fun ys body => do
    k ys (ctx.famIdxOf (← whnfOcc body))

/-- The layer `Occ.toC o x` of a nested argument `x` of `T.c` or of `T.F T` (`IOcc.toC` with
indices), the occurrences being at the type. -/
def nestToC (o x : Expr) : TermElabM Expr := do
  let T ← ctx.tFam
  if ctx.idxed then
    mkAppOptM ``Codata.IOcc.toC #[none, none, none, none, none, o, ← ctx.packFam T, x]
  else mkAppOptM ``Codata.Occ.toC #[none, none, none, o, T, x]

/-- Run `k` on a position `q` of the layer `t` of a nested argument with structure `n` (`σ` the
substitution of the constructor's arguments), with the index arguments of the occurrence at
`q`: `pidx t.1 q` unpacked, or none without indices. -/
def withNestPos (n : Nest) (σ : Expr → Expr) (t : Expr)
    (k : Expr → Array Expr → TermElabM α) : TermElabM α := do
  let snd ← mkAppM ``Sigma.snd #[t]
  let qTy := (← whnf (← inferType snd)).bindingDomain!.headBeta
  withLocalDeclD `q qTy fun q => do
    let idx ← match n.pidx? with
      | some pidx => ctx.projs (mkApp2 (σ pidx) (← mkAppM ``Sigma.fst #[t]) q)
      | none => pure #[]
    k q idx

/-- The induction hypotheses of a constructor `c` with arguments `ys` (as those of `T.c`), for
the motive given by `app idx x`, the motive at the family-level index arguments `idx` and `x`: one
per recursive argument, `x_ih`. -/
def recIHsWith (app : Array Expr → Expr → TermElabM Expr) (c : Ctor) (ys : Array Expr)
    (σ : Expr → Expr) : TermElabM (Array (Name × Expr)) := do
  let L ← ctx.tLvl
  (c.args.zip ys).filterMapM fun (a, y) => do
    if a.kind.isData then return none
    let ty ← match a.kind with
      | .data => unreachable!
      | .plain idx => app (idx.map σ) y
      | .fn n => ctx.openTFn n (← inferType y) fun zs idx => do
        mkForallFVars zs (← app idx (mkAppN y zs))
      | .nest n =>
        let t ← ctx.nestToC (ctx.nestAt n L σ) y
        ctx.withNestPos n σ t fun q idx => do
          mkForallFVars #[q] (← app idx (mkApp (← mkAppM ``Sigma.snd #[t]) q))
    return some (a.name.appendAfter "_ih", ty)

/-- The induction hypotheses of `c` for the motive `motive` (`recIHsWith`). -/
def recIHs (motive : Expr) (c : Ctor) (ys : Array Expr) (σ : Expr → Expr) :
    TermElabM (Array (Name × Expr)) :=
  ctx.recIHsWith (fun idx x => pure (mkAppN motive (idx.push x))) c ys σ

/-- The minor premise for `c` of a recursor whose motive is given by `app` (`recIHsWith`):
`∀ args ihs, motive idx (T.c args)`. -/
def recMinorTyWith (app : Array Expr → Expr → TermElabM Expr) (c : Ctor) : TermElabM Expr := do
  ctx.withTArgs c fun ys σ => do
  let ihs ← ctx.recIHsWith app c ys σ
  withLocalDeclsDND ihs fun ihs => do
    mkForallFVars (ys ++ ihs) (← app (c.idx.map σ) (← ctx.tCtorApp c ys))

/-- The minor premise of `T.rec` for `c`: `∀ args ihs, motive idx (T.c args)`. -/
def recMinorTy (motive : Expr) (c : Ctor) : TermElabM Expr :=
  ctx.recMinorTyWith (fun idx x => pure (mkAppN motive (idx.push x))) c

/-- Run `k` on local variables for the minor premises `mk c` of the constructors `cs` (all by
default), named after them (`names c`). -/
def withMinors (names : Ctor → Name) (mk : Ctor → TermElabM Expr)
    (k : Array Expr → TermElabM α) (cs : Array Ctor := ctx.ctors) : TermElabM α := do
  let rec go (i : Nat) (acc : Array Expr) : TermElabM α := do
    if h : i < cs.size then
      let c := cs[i]
      withLocalDeclD (names c) (← mk c) fun m => go (i + 1) (acc.push m)
    else k acc
  go 0 #[]

/-- Run `k` on the motive `{motive : ∀ j₁ j₂, T params j₁ j₂ → Sort v}`, `v` the added universe;
in a block, over the block. -/
def withMotive (v : Level) (k : Expr → TermElabM α) : TermElabM α := do
  let mTy ← ctx.withJs fun js => do
    withLocalDeclD `t (← ctx.tAt js) fun t => do mkForallFVars (js.push t) (mkSort v)
  withLocalDecl (← ctx.userName `motive) .implicit mTy k

/-- Run `k` on the motive `{motive : ∀ j₁ j₂, Tₘ params j₁ j₂ → Sort v}` of the `m`-th type,
named `name`. -/
def withTypeMotive (m : Nat) (v : Level) (k : Expr → TermElabM α) (name : Name := `motive) :
    TermElabM α := do
  let idx := ctx.types[m]!.idx
  let names := (Array.range idx.size).map fun i =>
    Name.mkSimple s!"j{Nat.toSubscriptString (i + 1)}"
  let mTy ← withCopies idx names .default fun js => do
    withLocalDeclD `t (← ctx.tyAt m js) fun t => do mkForallFVars (js.push t) (mkSort v)
  withLocalDecl (← ctx.userName name) .implicit mTy k

/-- `∀ b, motive (σ.idx b) ((toC y).child b)`: the induction hypotheses of `T.recAux` at `y`,
indexed by the positions of `toC y`. -/
def recAuxIH (motive : Expr) (idx : Array Expr) (y : Expr) : TermElabM Expr := do
  let L ← ctx.tLvl
  let σE ← ctx.sigE
  let fam ← ctx.modelFam
  let pI ← ctx.pack idx
  let tc ← ctx.toCAt L fam idx y
  let shape := mkApp4 (← ctx.sigConst ``Codata.Signature.Obj.shape [L]) σE fam pI tc
  withLocalDeclD `b (mkApp3 (← ctx.sigConst ``Codata.Signature.B) σE pI shape) fun b => do
    let i := mkApp4 (← ctx.sigConst ``Codata.Signature.idx) σE pI shape b
    let child := mkApp5 (← ctx.sigConst ``Codata.Signature.Obj.child [L]) σE fam pI tc b
    mkForallFVars #[b] (mkAppN motive ((← ctx.projs i).push child))

/-- `T.recAux`, `T.rec` and `T.rec_ctor`. -/
def genRec : TermElabM Unit := do
  let L ← ctx.tLvl
  let T ← ctx.tFam
  let σE ← ctx.sigE
  let fam ← ctx.modelFam
  let fresh := ctx.freshLevels 1
  let v := Level.param fresh[0]!
  ctx.withMotive v fun motive => do
  ctx.withMinors (·.fname) (ctx.recMinorTy motive) fun minors => do
  let ctorAt (idx : Array Expr) (y : Expr) : MetaM Expr := do
    ctx.genAt ctx.ctor [] (idx ++ #[y])
  -- `recAux`: the minor premises assembled, by cases on `y`.
  let FT ← ctx.fAt L T ctx.idx
  let np := ctx.params.size + 1
  withLocalDeclD `y FT fun y => do
  let body (idx : Array Expr) (y : Expr) : TermElabM Expr := do
    mkArrow (← ctx.recAuxIH motive idx y) (mkAppN motive (idx.push (← ctorAt idx y)))
  let value ← mkCasesOnApp ctx.F (← ctx.levelsWith ctx.F [L]) FT.getAppArgs y
    (← getLevel (← body ctx.idx y))
    (fun is y => do body (← fullIdx ctx.F np FT.getAppArgs is) y)
    (fun cname xs => do
      let some k := ctx.ctors.findIdx? (ctx.fCtor · == cname)
        | throwError "internal error: unexpected constructor {cname}"
      let c := ctx.ctors[k]!
      let ys ← ctorArgsOf ctx.F np FT.getAppArgs xs c.args.size
      let σ (e : Expr) := e.replaceFVars c.fvars ys
      let idx := c.idx.map σ
      withLocalDeclD `ih (← ctx.recAuxIH motive idx (← ctx.fCtorApp c L T ys)) fun ih => do
        let data := (c.args.zip ys).filterMap fun (a, y) => if a.kind.isData then some y else none
        let shs ← c.nests.mapM fun (a, n) => do
          let some j := c.args.findIdx? (·.fvar == a.fvar) | unreachable!
          mkAppM ``Sigma.fst #[← ctx.nestToC (ctx.nestAt n L σ) ys[j]!]
        let ihArgs ← (c.args.zip ys).filterMapM fun (a, y) => do
          match a.kind with
          | .data => return none
          | .plain _ => return some (mkApp ih (← ctx.bCtorApp c a (data ++ shs)))
          | .fn n => some <$> ctx.openTFn n (← inferType y) fun zs _ => do
            mkLambdaFVars zs (mkApp ih (← ctx.bCtorApp c a (data ++ shs ++ zs)))
          | .nest n =>
            let t ← ctx.nestToC (ctx.nestAt n L σ) y
            some <$> ctx.withNestPos n σ t fun q _ => do
              mkLambdaFVars #[q] (mkApp ih (← ctx.bCtorApp c a (data ++ shs |>.push q)))
        mkLambdaFVars #[ih] (mkAppN minors[k]! (ys ++ ihArgs)))
  let xs := ctx.params ++ #[motive] ++ minors ++ ctx.idx ++ #[y]
  let (type, value) ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    return (← mkForallFVars xs (← body ctx.idx y), ← mkLambdaFVars xs value)
  addDef ctx.recAux (← ctx.levelParamsOf fresh #[type, value]) type value ctx.ref
  -- The instances of `rec_of` and `rec_of_ctor`.
  let FTp ← ctx.packFam (← ctx.fFam L T)
  let recAuxAt (idx : Array Expr) (y ih : Expr) : MetaM Expr := do
    ctx.genAt ctx.recAux [v] (#[motive] ++ minors ++ idx ++ #[y, ih])
  let H ← lam `p (← ctx.ixp) fun p => do
    let ps ← ctx.projs p
    lam `y (mkApp FTp p).headBeta fun y => do
      lam `ih (← ctx.recAuxIH motive ps y) fun ih => recAuxAt ps y ih
  let toCT ← ctx.lamP fun p => do lam `y (mkApp FTp p).headBeta fun y => do
    ctx.toCAt L fam (← ctx.projs p) y
  let ofCT ← ctx.lamP fun p => do lam `z (← ctx.objAt L fam p) fun z => do
    ctx.ofCAt L fam (← ctx.projs p) z
  let toC_ofC ← ctx.lamP fun p => do lam `z (← ctx.objAt L fam p) fun z => do
    ctx.genAt ctx.toC_ofC [L] (#[fam] ++ (← ctx.projs p) ++ #[z])
  let ofC_toC ← ctx.lamP fun p => do lam `y (mkApp FTp p).headBeta fun y => do
    ctx.genAt ctx.ofC_toC [L] (#[fam] ++ (← ctx.projs p) ++ #[y])
  let motiveP ← ctx.uncurryN motive 1
  let pI ← ctx.packI
  -- `rec`
  do
    withLocalDeclD `t (← ctx.tAt ctx.idx) fun t => do
    let value ← mkAppOptM ``Codata.Signature.rec_of
      (#[σE, FTp, toCT, ofCT, toC_ofC, motiveP, H, pI, t].map some)
    let xs := ctx.params ++ #[motive] ++ minors ++ ctx.idx ++ #[t]
    let (type, value) ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
      return (← mkForallFVars xs (mkAppN motive (ctx.idx.push t)), ← mkLambdaFVars xs value)
    addDef ctx.recN (← ctx.levelParamsOf fresh #[type, value]) type value ctx.ref
    addAttrs ctx.recN #[← `(Parser.Term.attrInstance| elab_as_elim),
      ← `(Parser.Term.attrInstance| induction_eliminator)]
  -- `rec_ctor`
  let recAt (idx : Array Expr) (t : Expr) : MetaM Expr := do
    ctx.genAt ctx.recN [v] (#[motive] ++ minors ++ idx ++ #[t])
  let ih ← do
    let tc ← ctx.toCAt L fam ctx.idx y
    let shape := mkApp4 (← ctx.sigConst ``Codata.Signature.Obj.shape [L]) σE fam pI tc
    lam `b (mkApp3 (← ctx.sigConst ``Codata.Signature.B) σE pI shape) fun b => do
      let i := mkApp4 (← ctx.sigConst ``Codata.Signature.idx) σE pI shape b
      let child := mkApp5 (← ctx.sigConst ``Codata.Signature.Obj.child [L]) σE fam pI tc b
      recAt (← ctx.projs i) child
  let lhs ← recAt ctx.idx (← ctorAt ctx.idx y)
  let rhs ← recAuxAt ctx.idx y ih
  let xs := ctx.params ++ #[motive] ++ minors ++ ctx.idx ++ #[y]
  let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do mkForallFVars xs (← mkEq lhs rhs)
  let value ← mkAppOptM ``Codata.Signature.rec_of_ctor
    (#[σE, FTp, toCT, ofCT, toC_ofC, ofC_toC, motiveP, H, pI, y].map some)
  addThm ctx.rec_ctor (← ctx.levelParamsOf fresh #[type]) type (← mkLambdaFVars xs value) ctx.ref

end Ctx

end Codata.Gen
