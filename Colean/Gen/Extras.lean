import Colean.Gen.Framework

/-!
# Generators on `Expr`, step 2b: the dependent recursor

*Spec.* Input: the model (signature, isomorphism, `T.ctor`) and the constructors `T.cᵢ` (step
4). Output, for `data`, justified by the encoding rather than by the contract (`architecture.md`,
step 2b):

* `T.rec`, the dependent recursor into any `Sort`, with one minor premise per constructor
  carrying an induction hypothesis per recursive argument: `motive _ x` for a plain one,
  `∀ ys, motive _ (k ys)` under a telescope, and for a nested argument `c` one by membership,
  `∀ t, PolyIso.Mem (fun X => G X) t c → motive _ t`, with the argument's type `G` as a function
  of the occurrences and the instance of `PolyIso.lean` that is its occurrence structure; when
  its positions are at several indices of a family, `∀ j t, IPolyIso.Mem G j t c → motive j t`.
  When they are at one index only after cases on them, through a product (`T n × T n`,
  `T n × Nat`), the hypothesis is by `PolyIso.Mem` at that index, the hypothesis at the positions
  brought to it by these cases (`bridgeIH`). It is the `induction` eliminator;
* `T.recPos`, the same with the hypothesis of a nested argument at every position of its
  structure, `∀ q, motive _ ((toC o c).2 q)`: it is `Signature.rec_of` at the packed index, the
  minor premises assembled by cases on `F T i` (`T.recAux`), with its computation rule
  `T.recPos_ctor` (propositional: the generic recursor is by well-founded recursion). `T.rec` is
  `T.recPos` with the hypotheses turned into membership by `PolyIso.memRec`.

The minor premises are stated with the constructors `T.cᵢ`, so this runs after them.
-/

open Lean Meta Elab Term

namespace Codata.Gen

/-! ### Instances of occurrence structures -/

/-- How an occurrence structure is read as an instance (`isoOf`). -/
inductive IsoMode where
  /-- An `Occ`, as `PolyIso`. -/
  | plain
  /-- An `IOcc`, as `IPolyIso`. -/
  | fam
  /-- An `IOcc` whose positions are all at one index, as `PolyIso` at that index. -/
  | flat

/-- The arguments of `e` at the explicit binders of its head constant. -/
def explicitArgs (e : Expr) : MetaM (Array Expr) := do
  let args := e.getAppArgs
  forallBoundedTelescope (← inferType e.getAppFn) args.size fun xs _ => do
    let mut out := #[]
    for x in xs, a in args do
      if (← x.fvarId!.getBinderInfo).isExplicit then out := out.push a
    return out

/-- The instance `n` at the instances `insts`, its instance-implicit arguments in order, the other
arguments by unification with the class application `expected`. -/
def appInst (n : Name) (insts : Array Expr) (expected : Expr) : MetaM Expr := do
  let f ← mkConstWithFreshMVarLevels n
  let (xs, bis, ty) ← forallMetaTelescope (← inferType f)
  let mut i := 0
  for x in xs, bi in bis do
    if bi.isInstImplicit then
      unless ← isDefEq x insts[i]! do
        throwError "internal error: ill-typed instance argument of `{n}`{indentExpr insts[i]!}"
      i := i + 1
  unless ← isDefEq ty expected do
    throwError "internal error: `{n}` is not an instance of{indentExpr expected}"
  let r ← instantiateMVars (mkAppN f xs)
  if r.hasMVar then throwError "internal error: undetermined arguments of `{n}`{indentExpr r}"
  return r

/-- The instance of the functor of the occurrence structure `o`: `o` read as an instance. The
instances of `PolyIso.lean` for the built-in forms are the combinators by definition
(`Model/Occ.lean`, `Occ.ofIso_prod`, …), and a leaf is `Occ.ofIso` of its instance. -/
partial def isoOf (o : Expr) (mode : IsoMode) : MetaM Expr := do
  let o ← instantiateMVars o
  let ta := (← whnfR (← inferType o)).getAppArgs
  let expected ← match mode with
    | .plain => mkAppM ``Codata.PolyIso #[ta[2]!, ta[0]!, ta[1]!]
    | .fam => mkAppOptM ``Codata.IPolyIso #[ta[0]!, ta[4]!, ta[1]!, ta[2]!, ta[3]!]
    | .flat => do
      -- The functor of a type: the family constant.
      let G := ta[4]!
      let .forallE _ dom _ _ ← whnf (← inferType G)
        | throwError "internal error: not a functor on families{indentExpr G}"
      let .forallE _ J cod _ ← whnf dom
        | throwError "internal error: not a functor on families{indentExpr G}"
      let F ← withLocalDeclD `X cod fun X => do
        mkLambdaFVars #[X] (← Core.betaReduce (mkApp G (.lam `_ J X .default)))
      mkAppM ``Codata.PolyIso #[F, ta[1]!, ta[2]!]
  let ex ← explicitArgs o
  let under (o' : Expr) (m : IsoMode) : MetaM Expr :=
    lambdaBoundedTelescope o' 1 fun xs b => do mkLambdaFVars xs (← isoOf b m)
  let app (n : Name) (insts : Array Expr) : MetaM Expr := appInst n insts expected
  let head := o.getAppFn.constName?.getD .anonymous
  match mode, head with
  | .plain, ``Codata.Occ.ofIso | .fam, ``Codata.IOcc.ofIso => return o.appArg!
  | .plain, ``Codata.Occ.const | .flat, ``Codata.IOcc.const => app ``Codata.instPolyIsoEmpty #[]
  | .plain, ``Codata.Occ.hole | .flat, ``Codata.IOcc.hole => app ``Codata.instPolyIsoUnit #[]
  | .plain, ``Codata.Occ.prod =>
    app ``Codata.PolyIso.instProd #[← isoOf ex[0]! .plain, ← isoOf ex[1]! .plain]
  | .plain, ``Codata.Occ.sum =>
    app ``Codata.PolyIso.instSum #[← isoOf ex[0]! .plain, ← isoOf ex[1]! .plain]
  | .plain, ``Codata.Occ.pi => app ``Codata.PolyIso.instPi #[← under ex[1]! .plain]
  | .plain, ``Codata.Occ.piP => app ``Codata.PolyIso.instPiP #[← under ex[1]! .plain]
  | .plain, ``Codata.Occ.sigma => app ``Codata.PolyIso.instSigma #[← under ex[1]! .plain]
  | .plain, ``Codata.Occ.comp =>
    app ``Codata.PolyIso.instComp #[← isoOf ex[0]! .plain, ← isoOf ex[1]! .plain]
  | .plain, ``Codata.Occ.ofI => app ``Codata.PolyIso.instOfI #[← isoOf ex[0]! .fam]
  | .plain, ``Codata.Occ.compI =>
    app ``Codata.PolyIso.instCompI #[← isoOf ex[0]! .fam, ← under ex[1]! .plain]
  | .fam, ``Codata.IOcc.const => app ``Codata.IPolyIso.instConst #[]
  | .fam, ``Codata.IOcc.hole => app ``Codata.IPolyIso.instHole #[]
  | .fam, ``Codata.IOcc.ofOcc => app ``Codata.IPolyIso.instAt #[← isoOf ex[0]! .plain]
  | .fam, ``Codata.IOcc.reidx => app ``Codata.IPolyIso.instReidx #[← isoOf ex[0]! .fam]
  | .fam, ``Codata.IOcc.prod =>
    app ``Codata.IPolyIso.instProd #[← isoOf ex[0]! .fam, ← isoOf ex[1]! .fam]
  | .fam, ``Codata.IOcc.sum =>
    app ``Codata.IPolyIso.instSum #[← isoOf ex[0]! .fam, ← isoOf ex[1]! .fam]
  | .fam, ``Codata.IOcc.pi => app ``Codata.IPolyIso.instPi #[← under ex[1]! .fam]
  | .fam, ``Codata.IOcc.piP => app ``Codata.IPolyIso.instPiP #[← under ex[1]! .fam]
  | .fam, ``Codata.IOcc.sigma => app ``Codata.IPolyIso.instSigma #[← under ex[1]! .fam]
  | .fam, ``Codata.IOcc.compC =>
    app ``Codata.IPolyIso.instCompC #[← isoOf ex[0]! .plain, ← isoOf ex[1]! .fam]
  | .fam, ``Codata.IOcc.compI =>
    app ``Codata.IPolyIso.instCompI #[← isoOf ex[0]! .fam, ← under ex[1]! .fam]
  | .flat, ``Codata.IOcc.ofOcc => isoOf ex[0]! .plain
  | .flat, ``Codata.IOcc.reidx => app ``Codata.PolyIso.instOfI #[← isoOf ex[0]! .fam]
  | .flat, ``Codata.IOcc.pi => app ``Codata.PolyIso.instPi #[← under ex[1]! .flat]
  | .flat, ``Codata.IOcc.piP => app ``Codata.PolyIso.instPiP #[← under ex[1]! .flat]
  | .flat, ``Codata.IOcc.sigma => app ``Codata.PolyIso.instSigma #[← under ex[1]! .flat]
  | .flat, ``Codata.IOcc.prod =>
    app ``Codata.PolyIso.instProd #[← isoOf ex[0]! .flat, ← isoOf ex[1]! .flat]
  | .flat, ``Codata.IOcc.compC =>
    app ``Codata.PolyIso.instComp #[← isoOf ex[0]! .plain, ← isoOf ex[1]! .flat]
  | .flat, ``Codata.IOcc.compI =>
    app ``Codata.PolyIso.instCompI #[← isoOf ex[0]! .fam, ← under ex[1]! .flat]
  | _, _ => throwError "internal error: no instance for the occurrence structure{indentExpr o}"

/-- The induction hypothesis of a nested argument by membership: its functor, the functor's
instance and the type or family of the members. -/
structure NestMem where
  /-- When the positions are all at one index (always without indices): that index, as
  family-level index arguments; the hypothesis is by `PolyIso.Mem`. Otherwise by
  `IPolyIso.Mem`, over the packed index `Ctx.J`. -/
  idx? : Option (Array Expr)
  /-- The argument's type as a function of the occurrences: of a type, or of a family on the
  packed index. -/
  fn : Expr
  /-- Its instance, `PolyIso` or `IPolyIso`. -/
  inst : Expr
  /-- The members' type `Tₘ params idx`, or their family on the packed index. -/
  elem : Expr
  /-- At one index only after cases on the positions, through products (`T n × T n`): the
  hypothesis at the positions is turned into one at that index by these cases (`bridgeIH`). -/
  bridged : Bool := false

/-- The application of a family-level motive at index arguments. -/
def motiveApp (motive : Expr) (idx : Array Expr) (x : Expr) : TermElabM Expr :=
  pure (mkAppN motive (idx.push x))

namespace Ctx

variable (ctx : Ctx)

/-- `@T.c params args`. -/
def tCtorApp (c : Ctor) (ys : Array Expr) : MetaM Expr := do
  ctx.genAt (ctx.tCtor c) [] ys

/-- `@T.F.c params X args`, for `X` at universe `w`. -/
def fCtorApp (c : Ctor) (w : Level) (X : Expr) (ys : Array Expr) : MetaM Expr := do
  ctx.genAt (ctx.fCtor c) [w] (#[X] ++ ys)

/-- Run `k` on the arguments of `c` as those of `T.c`: the occurrences are `Tₘ params idx`, with
the per-type constants in a block, and in the outermost run of a mixed block the types of the
runs inside are their closed types (`Ctx.foldTy`). -/
def withTArgs (c : Ctor) (k : Array Expr → (Expr → Expr) → TermElabM α)
    (rename : Name → Name := id) : TermElabM α := do
  let tys ← (Array.range ctx.types.size).mapM fun m => ctx.constWith (ctx.tyName m) []
  ctx.withArgsAtU c (fun m idx => mkAppN tys[m]! (ctx.params ++ idx)) (← ctx.tLvl) k rename
    ctx.foldTy

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

/-! ### Hypotheses by membership -/

/-- Is the index of a position of the indexed structure `o` the same at variables, mentioning
neither the shape nor the position? That index. -/
def constIdx (o : Expr) : MetaM (Option Expr) := do
  let args := (← whnfR (← inferType o)).getAppArgs
  let (sh, pos, pidx) := (args[1]!, args[2]!, args[3]!)
  withLocalDeclD `s sh fun s => do
  withLocalDeclD `q (mkApp pos s).headBeta fun q => do
    let i ← Core.betaReduce (mkApp2 pidx s q)
    return if i.containsFVar s.fvarId! || i.containsFVar q.fvarId! then none else some i

/-- Are the positions of the indexed structure `o` at one index after cases on them, through
products, functions and composites down to structures at one index at variables, or without
positions (`some none`)? That index. -/
partial def oneAfterCases (o : Expr) : MetaM (Option (Option Expr)) := do
  let head := o.getAppFn.constName?.getD .anonymous
  if head == ``Codata.IOcc.const then return some none
  if let some i ← constIdx o then return some (some i)
  let ex ← explicitArgs o
  match head with
  | ``Codata.IOcc.prod =>
    let some i ← oneAfterCases ex[0]! | return none
    let some j ← oneAfterCases ex[1]! | return none
    match i, j with
    | some i, some j => return if ← isDefEq i j then some (some i) else none
    | some i, none | none, some i => return some (some i)
    | none, none => return some none
  | ``Codata.IOcc.pi =>
    lambdaBoundedTelescope ex[1]! 1 fun xs b => do
      let some i ← oneAfterCases b | return none
      return if i.any fun i => xs.any (i.containsFVar ·.fvarId!) then none else some i
  | ``Codata.IOcc.compC => oneAfterCases ex[1]!
  | _ => return none

/-- `fun q => ih q` at the type `ty`, `∀ q, motive idx (child q)`, from `ih` at the indices of the
positions, `∀ q, motive (pidx q) (child q)`, which are `idx` only after cases on `q`: by these
cases, as deep as needed. -/
partial def bridgeIH (ty ih : Expr) : MetaM Expr := do
  let g ← mkFreshExprSyntheticOpaqueMVar ty
  let (q, g') ← g.mvarId!.intro1
  let rec go (g : MVarId) (pos : Expr) (x : FVarId) : MetaM Unit := g.withContext do
    let v := mkApp ih pos
    if ← withUnfolding <| isDefEq (← g.getType) (← inferType v) then
      g.assign v
      return
    for sg in ← g.cases x do
      let some y := sg.fields.back? | throwError "internal error: cases on a position"
      go sg.mvarId (sg.subst.apply pos) y.fvarId!
  go g' (mkFVar q) q
  instantiateMVars g

/-- `bridgeIH ty ih = f` for `f` equal to `ih` at every position, by the same cases: an
equation of functions on the positions. -/
partial def bridgeEq (ty ih f : Expr) : MetaM Expr := do
  let b ← bridgeIH ty ih
  let eqTy ← forallTelescope ty fun qs _ => do
    mkForallFVars qs (← mkEq (mkApp b qs[0]!).headBeta (mkApp f qs[0]!).headBeta)
  let g ← mkFreshExprSyntheticOpaqueMVar eqTy
  let (q, g') ← g.mvarId!.intro1
  let rec go (g : MVarId) (x : FVarId) : MetaM Unit := g.withContext do
    let ok ← try withUnfolding g.refl; pure true catch _ => pure false
    if ok then return
    for sg in ← g.cases x do
      let some y := sg.fields.back? | throwError "internal error: cases on a position"
      go sg.mvarId y.fvarId!
  go g' q
  mkFunExt (← instantiateMVars g)

/-- The membership data of the nested argument `a` of `c` with structure `n`, for the arguments
`ys` of `T.c` (`σ` the substitution of the analysis' arguments by them). The positions are at
one index when the index of a position, at variables, mentions neither: then the members are
the occurrences of the argument's type, which are all at that index. -/
def nestMem (a : ArgInfo) (n : Nest) (σ : Expr → Expr) : TermElabM NestMem := do
  let L ← ctx.tLvl
  let o := ctx.nestAt n L σ
  let ty := σ a.type
  let one ← match n.pidx? with
    | none => pure true
    | some pidx =>
      let sub (e : Expr) := substLevel ctx.uT L (σ e)
      withLocalDeclD `s (sub n.sh) fun s => do
      withLocalDeclD `q (mkApp (sub n.pos) s).headBeta fun q => do
        let i ← Core.betaReduce (mkApp2 (sub pidx) s q)
        return !i.containsFVar s.fvarId! && !i.containsFVar q.fvarId!
  -- At one index after cases on the positions, through products.
  let bridged ← if one || n.pidx?.isNone then pure false else
    pure ((← oneAfterCases o).join).isSome
  if one || bridged then
    let some e := ty.find? fun e => (ctx.occ? e).isSome
      | throwError "internal error: no occurrence in a nested argument{indentExpr ty}"
    let some (m, idx) := ctx.occ? e | unreachable!
    let elem ← ctx.tyAt m idx
    let fn ← withLocalDeclD `X (mkSort L.succ) fun X => do
      mkLambdaFVars #[X] (ctx.replaceOccU ty (fun _ _ => X) L)
    let inst ← isoOf o (if ctx.idxed then .flat else .plain)
    return { idx? := some (ctx.wrap m idx), fn, inst, elem, bridged }
  else
    let J := ctx.J
    let fn ← withLocalDeclD `X (← mkArrow J (mkSort L.succ)) fun X => do
      let cur ← ctx.withJs fun js => do mkLambdaFVars js (mkApp X (← ctx.pack js))
      mkLambdaFVars #[X] (ctx.replaceOccU ty (fun m idx => cur.beta (ctx.wrap m idx)) L)
    let elem ← if ctx.k == 1 then ctx.tFam else
      withLocalDeclD `p J fun p => do mkLambdaFVars #[p] (← ctx.tAt (← ctx.projs p))
    return { idx? := none, fn, inst := ← isoOf o .fam, elem }

/-- The membership statement `PolyIso.Mem G t y`, or `IPolyIso.Mem G ⟨js⟩ t y` at the
family-level index arguments `js`; in the outermost run of a mixed block, `t ∈ y` for a closed
type with a membership instance (`Ctx.foldTy`). -/
def memProp (nm : NestMem) (y t : Expr) (js : Array Expr) : TermElabM Expr := do
  if nm.idx?.isSome then
    let args : Array (Option Expr) := #[nm.fn, none, none, nm.inst, nm.elem, t, y]
    return ctx.foldTy (← withUnfolding <| mkAppOptM ``Codata.PolyIso.Mem args)
  else
    let args : Array (Option Expr) :=
      #[none, nm.fn, none, none, none, nm.inst, nm.elem, ← ctx.pack js, t, y]
    withUnfolding <| mkAppOptM ``Codata.IPolyIso.Mem args

/-- Run `k` on the variables of a hypothesis by membership of `y`: the member `t` (after the
indices `js`, without a single one) and the membership `h`. -/
def withMember (nm : NestMem) (y : Expr) (k : Array Expr → Expr → Expr → TermElabM α)
    (h : Name := `h) : TermElabM α := do
  match nm.idx? with
  | some _ =>
    withLocalDeclD `t nm.elem fun t => do
    withLocalDeclD h (← ctx.memProp nm y t #[]) fun h => k #[] t h
  | none =>
    ctx.withJs fun js => do
    withLocalDeclD `t (← ctx.tAt js) fun t => do
    withLocalDeclD h (← ctx.memProp nm y t js) fun h => k js t h

/-- The hypothesis by membership of `y` for the motive given by `app` (`recIHsWith`):
`∀ t, PolyIso.Mem G t y → app idx t`, or `∀ j₁ j₂ t, IPolyIso.Mem G ⟨j₁, j₂⟩ t y → app js t`. -/
def memIH (nm : NestMem) (y : Expr) (app : Array Expr → Expr → TermElabM Expr) :
    TermElabM Expr :=
  ctx.withMember nm y fun js t h => do
    let idx := nm.idx?.getD js
    mkForallFVars (js ++ #[t]) (← mkArrow (← inferType h) (← app idx t))

/-- In a block, the types that occur in `e`, in block order. -/
def occTypes (e : Expr) : Array Nat :=
  (Array.range ctx.types.size).filter fun m =>
    (e.find? fun s => (ctx.occ? s).any (·.1 == m)).isSome

/-- In a block, run `k` on the variables of a hypothesis by membership of `y` at the `m`-th type:
its indices `uidx`, the member `t : Tₘ uidx` and the membership `h` at `Blk.Ix.Tₘ uidx`. -/
def withTypeMember (nm : NestMem) (y : Expr) (m : Nat)
    (k : Array Expr → Expr → Expr → TermElabM α) (h : Name := `h) : TermElabM α := do
  let idx := ctx.types[m]!.idx
  let names := (Array.range idx.size).map fun i =>
    Name.mkSimple s!"j{Nat.toSubscriptString (i + 1)}"
  withCopies idx names .default fun uidx => do
  withLocalDeclD `t (← ctx.tyAt m uidx) fun t => do
  withLocalDeclD h (← ctx.memProp nm y t (ctx.wrap m uidx)) fun h => k uidx t h

/-- In a block, the hypothesis by membership of `y` at the `m`-th type:
`∀ j₁ (t : Tₘ j₁), IPolyIso.Mem G (Blk.Ix.Tₘ j₁) t y → app (Blk.Ix.Tₘ j₁) t`. -/
def memIHAt (nm : NestMem) (y : Expr) (m : Nat) (app : Array Expr → Expr → TermElabM Expr) :
    TermElabM Expr :=
  ctx.withTypeMember nm y m fun uidx t h => do
    mkForallFVars (uidx ++ #[t]) (← mkArrow (← inferType h) (← app (ctx.wrap m uidx) t))

/-- `fun t => app idx t`, or `fun p t => app p.1 p.2 t` on the packed index: the motive of
`memRec`. -/
def memMotive (nm : NestMem) (app : Array Expr → Expr → TermElabM Expr) : TermElabM Expr := do
  match nm.idx? with
  | some idx => lam `t nm.elem fun t => app idx t
  | none => lam `p ctx.J fun p => do
      lam `t (mkApp nm.elem p).headBeta fun t => do app (← ctx.projs p) t

/-- The type of the hypothesis at the positions of `y` that `PolyIso.memRec` takes, at the motive
`motive` of `memMotive`: `∀ q, motive ((equiv y).2 q)`. -/
def memPosTy (nm : NestMem) (y motive : Expr) : TermElabM Expr := do
  let r ← withUnfolding <| mkAppOptM ``Codata.PolyIso.memRec
    #[nm.fn, none, none, nm.inst, nm.elem, y, motive]
  return (← whnf (← inferType r)).bindingDomain!

/-- The hypothesis by membership of `y`, from the one at the positions of its structure, `ih`:
`PolyIso.memRec ih`, curried over the indices with `IPolyIso.memRec`. -/
def memOfPos (nm : NestMem) (y : Expr) (app : Array Expr → Expr → TermElabM Expr) (ih : Expr) :
    TermElabM Expr := do
  let motive ← ctx.memMotive nm app
  if nm.idx?.isSome then
    let ih ← if nm.bridged then bridgeIH (← memPosTy nm y motive) ih else pure ih
    let args : Array (Option Expr) := #[nm.fn, none, none, nm.inst, nm.elem, y, motive, ih]
    withUnfolding <| mkAppOptM ``Codata.PolyIso.memRec args
  else
    let args : Array (Option Expr) :=
      #[none, nm.fn, none, none, none, nm.inst, nm.elem, y, motive, ih]
    let r ← withUnfolding <| mkAppOptM ``Codata.IPolyIso.memRec args
    ctx.withMember nm y fun js t h => do
      mkLambdaFVars (js ++ #[t, h]) (mkAppN r #[← ctx.pack js, t, h])

/-- The value of the hypothesis by membership of `y` in a computation rule, `recAt` the
recursor at the family-level index arguments: `fun t _ => recAt idx t`, or
`fun j₁ j₂ t _ => recAt js t`. -/
def memVal (nm : NestMem) (y : Expr) (recAt : Array Expr → Expr → TermElabM Expr) :
    TermElabM Expr :=
  ctx.withMember nm y (h := `_) fun js t h => do
    mkLambdaFVars (js ++ #[t, h]) (← recAt (nm.idx?.getD js) t)

/-- `memOfPos` of the hypothesis at the positions given by `recAt` is `memVal`: from
`PolyIso.memRec_pos`, curried over the indices. -/
def memValEq (nm : NestMem) (y : Expr) (recAt : Array Expr → Expr → TermElabM Expr)
    (ihPos : Expr) : TermElabM Expr := do
  let g ← ctx.memMotive nm fun idx t => recAt idx t
  if nm.idx?.isSome then
    let args : Array (Option Expr) := #[nm.fn, none, none, nm.inst, nm.elem, y, none, g]
    let e ← withUnfolding <| mkAppOptM ``Codata.PolyIso.memRec_pos args
    if !nm.bridged then return e
    -- `memRec (bridgeIH ihPos) = memRec (fun q => g …)` first, from the hypothesis at the
    -- positions `ihPos`, by cases on the positions.
    let some (_, lhs, _) := (← inferType e).eq? | throwError "internal error: not an equation"
    let f := lhs.appArg!
    let hb ← bridgeEq (← inferType f) ihPos f
    mkEqTrans (← mkCongrArg lhs.appFn! hb) e
  else
    let args : Array (Option Expr) :=
      #[none, nm.fn, none, none, none, nm.inst, nm.elem, y, none, g]
    let e ← withUnfolding <| mkAppOptM ``Codata.IPolyIso.memRec_pos args
    let some (FTy, _, _) := (← inferType e).eq? | throwError "internal error: not an equation"
    let curry ← lam `F FTy fun F => do
      ctx.withMember nm y fun js t h => do
        mkLambdaFVars (js ++ #[t, h]) (mkAppN F #[← ctx.pack js, t, h])
    mkCongrArg curry e

/-! ### The minor premises -/

/-- The induction hypotheses of a constructor `c` with arguments `ys` (as those of `T.c`), for
the motive given by `app idx x`, the motive at the family-level index arguments `idx` and `x`: one
per recursive argument, `x_ih`. A nested argument's is by membership, or with `pos` at the
positions of its structure (`T.recPos`). With `split`, in a block, a hypothesis by `IPolyIso.Mem`
is one per type of the block in the argument's type (`x_ih_Tₘ` when there are several), for the
recursors per type. -/
def recIHsWith (app : Array Expr → Expr → TermElabM Expr) (c : Ctor) (ys : Array Expr)
    (σ : Expr → Expr) (pos split : Bool := false) : TermElabM (Array (Name × Expr)) := do
  let L ← ctx.tLvl
  let mut out := #[]
  for a in c.args, y in ys do
    let n := a.name.appendAfter "_ih"
    match a.kind with
    | .data => pure ()
    | .plain idx => out := out.push (n, ← app (idx.map σ) y)
    | .fn k =>
      out := out.push (n, ← ctx.openTFn k (← inferType y) fun zs idx => do
        mkForallFVars zs (← app idx (mkAppN y zs)))
    | .nest nst =>
      if pos then
        let t ← ctx.nestToC (ctx.nestAt nst L σ) y
        out := out.push (n, ← ctx.withNestPos nst σ t fun q idx => do
          mkForallFVars #[q] (← app idx (mkApp (← mkAppM ``Sigma.snd #[t]) q)))
      else
        let nm ← ctx.nestMem a nst σ
        if split && ctx.isBlock && nm.idx?.isNone then
          let ms := ctx.occTypes a.type
          for m in ms do
            let nm' := if ms.size == 1 then n else
              n.appendAfter ("_" ++ ctx.shortName m)
            out := out.push (nm', ← ctx.memIHAt nm y m app)
        else out := out.push (n, ← ctx.memIH nm y app)
  return out

/-- The minor premise for `c` of a recursor whose motive is given by `app` (`recIHsWith`):
`∀ args ihs, motive idx (T.c args)`. -/
def recMinorTyWith (app : Array Expr → Expr → TermElabM Expr) (c : Ctor)
    (pos split : Bool := false) : TermElabM Expr := do
  ctx.withTArgs c fun ys σ => do
  let ihs ← ctx.recIHsWith app c ys σ pos split
  withLocalDeclsDND ihs fun ihs => do
    mkForallFVars (ys ++ ihs) (← app (c.idx.map σ) (← ctx.tCtorApp c ys))

/-- The minor premise of `T.rec` for `c` (of `T.recPos` with `pos`):
`∀ args ihs, motive idx (T.c args)`. -/
def recMinorTy (motive : Expr) (c : Ctor) (pos : Bool := false) : TermElabM Expr :=
  ctx.recMinorTyWith (motiveApp motive) c pos

/-- The minor premises of `T.recPos` from those of `T.rec`, `minors`: each is the minor premise
of `T.rec` with the hypotheses of the nested arguments turned into membership (`memOfPos`). -/
def posMinors (motive : Expr) (minors : Array Expr) : TermElabM (Array Expr) := do
  let app := motiveApp motive
  ctx.ctors.zipIdx.mapM fun (c, k) => do
    ctx.withTArgs c fun ys σ => do
    let ihs ← ctx.recIHsWith app c ys σ (pos := true)
    withLocalDeclsDND ihs fun ihVars => do
      let recs := (c.args.zip ys).filter (!·.1.kind.isData)
      let conv ← (recs.zip ihVars).mapM fun ((a, y), ih) => do
        match a.kind with
        | .nest n => ctx.memOfPos (← ctx.nestMem a n σ) y app ih
        | _ => pure ih
      mkLambdaFVars (ys ++ ihVars) (mkAppN minors[k]! (ys ++ conv))

/-- In a block, the minor premises of `Blk.rec` at the motive `M` from those of the recursors
per type, `minors` (`recIHsWith` with `split`): a hypothesis by `IPolyIso.Mem` of `Blk.rec` is
given to each type at its constructor of `Blk.Ix`, where `M` is that type's motive. -/
def splitMinors (M : Expr) (minors : Array Expr) : TermElabM (Array Expr) := do
  let app := motiveApp M
  ctx.ctors.zipIdx.mapM fun (c, k) => do
    ctx.withTArgs c fun ys σ => do
    let ihs ← ctx.recIHsWith app c ys σ
    withLocalDeclsDND ihs fun ihVars => do
      let recs := (c.args.zip ys).filter (!·.1.kind.isData)
      let conv ← (recs.zip ihVars).flatMapM fun ((a, y), ih) => do
        let .nest n := a.kind | return #[ih]
        let nm ← ctx.nestMem a n σ
        if nm.idx?.isSome then return #[ih]
        (ctx.occTypes a.type).mapM fun m => do
          ctx.withTypeMember nm y m fun uidx t h => do
            mkLambdaFVars (uidx ++ #[t, h]) (mkAppN ih (ctx.wrap m uidx ++ #[t, h]))
      mkLambdaFVars (ys ++ ihVars) (mkAppN minors[k]! (ys ++ conv))

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

/-- `T.recAux`, `T.recPos`, `T.recPos_ctor` and `T.rec`. -/
def genRec : TermElabM Unit := do
  let L ← ctx.tLvl
  let T ← ctx.tFam
  let σE ← ctx.sigE
  let fam ← ctx.modelFam
  let fresh := ctx.freshLevels 1
  let v := Level.param fresh[0]!
  ctx.withMotive v fun motive => do
  -- `T.recPos` and its parts, with the hypotheses at the positions.
  ctx.withMinors (·.fname) (ctx.recMinorTy motive (pos := true)) fun minors => do
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
  -- `recPos`
  do
    withLocalDeclD `t (← ctx.tAt ctx.idx) fun t => do
    let value ← mkAppOptM ``Codata.Signature.rec_of
      (#[σE, FTp, toCT, ofCT, toC_ofC, motiveP, H, pI, t].map some)
    let xs := ctx.params ++ #[motive] ++ minors ++ ctx.idx ++ #[t]
    let (type, value) ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
      return (← mkForallFVars xs (mkAppN motive (ctx.idx.push t)), ← mkLambdaFVars xs value)
    addDef ctx.recPos (← ctx.levelParamsOf fresh #[type, value]) type value ctx.ref
  -- `recPos_ctor`
  let recPosAt (idx : Array Expr) (t : Expr) : MetaM Expr := do
    ctx.genAt ctx.recPos [v] (#[motive] ++ minors ++ idx ++ #[t])
  let ih ← do
    let tc ← ctx.toCAt L fam ctx.idx y
    let shape := mkApp4 (← ctx.sigConst ``Codata.Signature.Obj.shape [L]) σE fam pI tc
    lam `b (mkApp3 (← ctx.sigConst ``Codata.Signature.B) σE pI shape) fun b => do
      let i := mkApp4 (← ctx.sigConst ``Codata.Signature.idx) σE pI shape b
      let child := mkApp5 (← ctx.sigConst ``Codata.Signature.Obj.child [L]) σE fam pI tc b
      recPosAt (← ctx.projs i) child
  let lhs ← recPosAt ctx.idx (← ctorAt ctx.idx y)
  let rhs ← recAuxAt ctx.idx y ih
  let xs := ctx.params ++ #[motive] ++ minors ++ ctx.idx ++ #[y]
  let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do mkForallFVars xs (← mkEq lhs rhs)
  let value ← mkAppOptM ``Codata.Signature.rec_of_ctor
    (#[σE, FTp, toCT, ofCT, toC_ofC, ofC_toC, motiveP, H, pI, y].map some)
  addThm ctx.recPos_ctor (← ctx.levelParamsOf fresh #[type]) type (← mkLambdaFVars xs value)
    ctx.ref
  -- `rec`: `recPos` at the minor premises with the hypotheses by membership.
  ctx.withMinors (·.fname) (ctx.recMinorTy motive) fun minors => do
  withLocalDeclD `t (← ctx.tAt ctx.idx) fun t => do
  let value := mkAppN (← ctx.constWith ctx.recPos [v])
    (ctx.params ++ #[motive] ++ (← ctx.posMinors motive minors) ++ ctx.idx ++ #[t])
  let xs := ctx.params ++ #[motive] ++ minors ++ ctx.idx ++ #[t]
  let (type, value) ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    return (← mkForallFVars xs (mkAppN motive (ctx.idx.push t)), ← mkLambdaFVars xs value)
  addDef ctx.recN (← ctx.levelParamsOf fresh #[type, value]) type value ctx.ref
  addAttrs ctx.recN #[← `(Parser.Term.attrInstance| elab_as_elim),
    ← `(Parser.Term.attrInstance| induction_eliminator)]

end Ctx

end Codata.Gen
