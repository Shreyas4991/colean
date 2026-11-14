import Colean.Gen.Derive.Fix

/-!
# Generators on `Expr`, step 5: the simp lemmas

`Tₘ.Poly.map_c` and `Tₘ.Poly.mem_c` for every constructor of the presentation (see the section
below).
-/

open Lean Meta Elab Term

namespace Codata.Gen

namespace Ctx

variable (ctx : Ctx)

/-! ### The simp lemmas

For every constructor `c` of a type `Tₘ`, two simp lemmas at the premises, so that `simp`
computes through the instances:

* `Tₘ.Poly.map_c`, the map on the constructor:
  `(Occ.ofIso fun X => Tₘ (H X) idx).map (Occ.ofIso fun X => Tₘ (H' X) idx) f (Tₘ.c args) =
  Tₘ.c args'`, the arguments mapped by kind: data unchanged, a field at a parameter position by
  the map of its structure in the premises (`(Occ.ofIso H).map (Occ.ofIso H') f a`, which `simp`
  makes `f a` at the identity, `Occ.map_ofIso_id`), a recursive argument by this map, a nested one
  by the map of its structure. The map is stated on the leaf `Occ.ofIso` of the instance, the form
  in which the generated rules of other types (`fold_c`, `F.map_c`) mention it. `PolyMap.map`
  takes the functor implicitly, so `simp` would unify the constructor's arguments first, at `H X`
  for an unknown `H` (`?H ?X =?= T` at the identity premise), and the rule would not apply;
  `Occ.ofIso` and `PolyIso.Mem` take it explicitly. It is `PolyFix.map_eq_of_d` at the constructor
  `ctor ∘ ofL`, after `dtor_c`; the right-hand side is the result by definition.
* `Tₘ.Poly.mem_c`, membership in the constructor: `PolyIso.Mem (fun X => Tₘ (H X) idx) x
  (Tₘ.c args) ↔ …`, a disjunct per field at a parameter position (membership through its
  structure in the premises) and per recursive argument (membership in it, under a telescope at
  some arguments, through a nested argument in some member of it), `False` without any. It is
  `PolyFix.exists_val_iff` after `dtor_c`, then cases on the positions of the layer.

The functors of the left-hand sides are not indexed (`no_index`): the leaves of other types'
rules are often eta-reduced (`Occ.ofIso Forest`). Both lemmas are stated for `codata` as for
`data`: a value of a `codata` type is the constructor of its `dtor` (`ctor_dtor`), and `corec_eq`
writes a corecursive value so; membership is one step for `codata` too, since a member is at a
finite depth.

The lemmas are per constructor of the presentation (`VCtor`): with a split argument they are
stated with its parts, the components `p.1`, `p.2` of a product, and for a sum one lemma per side,
on the constructor at an injection (`Tm.Poly.map_app_inl` for `Tm.app (Sum.inl t) arg`). An
argument with a structure in two variables is mapped by `Occ₂.map`, in the premise's variable by
`f` and in the occurrences by the map of the type's leaf, which `simp` computes through the
combinators (`Occ₂.map_comp`, …); its members are those of its structure in the holes alone, the
occurrences constant (`xStruct`), and through its structure in the occurrences, as for a nested
argument: two disjuncts, whose positions are the structure's by definition. Across a sum these
structures read as instances agree with it only after cases on the value, and the two disjuncts
are its members in each variable, `Occ₂.MemX` and `∃ t, Occ₂.MemY o t y ∧ …`, which `simp`
computes through the combinators. Without a hole (in a block, at one type after cases on the
positions), there are no members in the holes: the one disjunct of the occurrences, the other
refuted in the proof by `simp`. With indices, at one index after cases, the rules are the same,
at the type of the members (`mixPlain`); at several indices of a family, the map is `IOcc₂.map`
with the map of the family's leaf at each index, and a member in the occurrences is a pair with
its index (`IOcc₂.MemY`). A nested argument of a family at one index only after cases on its
positions has its members by `IPolyIso.Mem`, as at several indices: the cases on the positions of
the layer do not see the cases that bring them to one index (the recursor's `bridgeIH`). -/

/-- `e`, built at the premises `H`, their instances and `X`, at the primed premises `H'`, their
instances and `Y`, and the primed universes: the second instantiation of `PolyMap`. -/
def polyPrime (P : Poly) (X Y e : Expr) : Expr :=
  let e := e.replaceFVars (P.Hs ++ P.insts ++ #[X]) (P.Hs' ++ P.insts' ++ #[Y])
  P.prime (e.instantiateLevelParams [P.fresh[0]!] [P.lx'])

/-- `Tₘ.Poly.instPolyIso premises idx`, the instance of the `m`-th type at its index arguments. -/
def polyIsoOf (P : Poly) (m : Nat) (idx : Array Expr) : MetaM Expr := do
  return mkAppN (← polyConst (ctx.tyName m ++ `Poly ++ `instPolyIso)) (P.premises ++ idx)

/-- The functor of an instance `PolyIso F Sh Pos`, eta-reduced. -/
def isoFun (inst : Expr) : MetaM Expr := do
  return (← whnfR (← inferType inst)).getAppArgs[0]!.eta

/-- `PolyIso.Mem F x c` for the instance `inst` of `F`, with `X` the type of `x`. -/
def isoMem (inst X x c : Expr) : MetaM Expr := do
  withUnfolding <| mkAppOptM ``Codata.PolyIso.Mem #[← isoFun inst, none, none, inst, X, x, c]

/-- The limit of the rules for a nested argument `a` of a type of a block whose positions are at
several types of the block. -/
def throwSeveralTypes (a : ArgInfo) : MetaM α :=
  throwLimit m!"the positions of the nested argument `{a.name}` are at several types of the block"

/-- `Occ.ofIso (fun X => Tₘ (H X) idx)`: the `m`-th type at its index arguments as a leaf. -/
def polyLeaf (P : Poly) (m : Nat) (idx : Array Expr) : MetaM Expr := do
  let inst ← ctx.polyIsoOf P m idx
  mkAppOptM ``Codata.Occ.ofIso #[← isoFun inst, none, none, inst]

/-- The type `Tₘ ps idx` of a recursive argument, as `m` and `idx`. -/
def polyRecType (ty : Expr) : MetaM (Nat × Array Expr) := do
  let e ← whnfOcc ty
  let args := e.getAppArgs
  let some m := ctx.types.findIdx? (e.getAppFn.isConstOf ·.name)
    | throwError "internal error: not a type being defined{indentExpr ty}"
  return (m, args.extract ctx.params.size args.size)

/-- The parts of a value `y` of a template without sums: its projections. -/
partial def tplProjs : Tpl → Expr → MetaM (Array Expr)
  | .part _, y => pure #[y]
  | .prod l r, y => do
    return (← tplProjs l (← mkAppM ``Prod.fst #[y])) ++ (← tplProjs r (← mkAppM ``Prod.snd #[y]))
  | .sum .., _ => throwError "internal error: projections through a sum"

/-- A value of type `D` of the template `t` along the alternatives `choices` from the `ci`-th:
a local variable `name` for a template without sums, with its projections as its parts; through
a sum, its injection, of the value of the alternative taken; a pair of values otherwise. `k`
receives the value, its parts, the local variables and the next position in `choices`. -/
partial def withTplArg (choices : Array Bool) (t : Tpl) (name : Name) (bi : BinderInfo)
    (D : Expr) (ci : Nat) (k : Expr → Array Expr → Array Expr → Nat → TermElabM α) :
    TermElabM α := do
  if !t.hasSum then
    return ← withLocalDecl name bi D fun y => do k y (← tplProjs t y) #[y] ci
  let D ← whnfOcc D
  let (A, B) := (D.appFn!.appArg!, D.appArg!)
  match t with
  | .prod l r =>
    withTplArg choices l (name.appendAfter "_fst") .default A ci fun x px lx ci =>
      withTplArg choices r (name.appendAfter "_snd") .default B ci fun y py ly ci => do
        k (← mkAppOptM ``Prod.mk #[A, B, x, y]) (px ++ py) (lx ++ ly) ci
  | .sum l r _ _ =>
    if choices[ci]! then
      withTplArg choices l (name.appendAfter "_inl") .default A (ci + 1) fun x px lx ci => do
        k (← mkAppOptM ``Sum.inl #[A, B, x]) px lx ci
    else
      withTplArg choices r (name.appendAfter "_inr") .default B (ci + 1) fun x px lx ci => do
        k (← mkAppOptM ``Sum.inr #[A, B, x]) px lx ci
  | .part _ => throwError "internal error: a part with a sum"

/-- Run `k` on the arguments of the real constructor of `v` as those of `Tₘ.c` at the premises
applied to `X`: the occurrences `Tₘ params idx` become `Tₘ (H X) idx`, the holes `H X`; a split
argument down to the alternatives of `v` (`withTplArg`). `k` receives the local variables, the
arguments of the real constructor, those of `v`, and the substitution of the latter (of the
analysis' arguments of `v`) and of the holes. -/
def withPolyVArgs (P : Poly) (X : Expr) (v : VCtor)
    (k : Array Expr → Array Expr → Array Expr → (Expr → Expr) → TermElabM α) :
    TermElabM α := do
  let c := ctx.ctors[v.real]!
  let L ← ctx.tLvl
  let tys ← (Array.range ctx.types.size).mapM fun m => ctx.constWith (ctx.tyName m) []
  let ps := ctx.polyParams P P.Hs X
  let rec go (i ci : Nat) (reals vals locals : Array Expr) : TermElabM α := do
    if h : i < c.args.size then
      let a := c.args[i]
      let ty := ctx.replaceOccU (a.type.replaceFVars (c.fvars.extract 0 i) reals)
        (fun m idx => mkAppN tys[m]! (ps ++ idx)) L
      withTplArg v.choices v.tpls[i]! a.name a.bi (P.subX P.Hs X ty) ci fun y py ly ci =>
        go (i + 1) ci (reals.push y) (vals ++ py) (locals ++ ly)
    else k locals reals vals fun e => P.subX P.Hs X (e.replaceFVars v.ctor.fvars vals)
  go 0 0 #[] #[] #[]

/-- `e` under existentials over `zs`: `∃ z₁ z₂, e`. -/
def mkExistsOver (zs : Array Expr) (e : Expr) : MetaM Expr :=
  zs.foldrM (init := e) fun z b => do mkAppM ``Exists #[← mkLambdaFVars #[z] b]

/-- `⟨w, pf⟩` for the existential `ty`, a membership unfolded first. The type of `pf` is the
expected one up to unfolding, which the kernel checks. -/
def exIntro (ty w pf : Expr) : MetaM Expr := do
  let .app (.app (.const ``Exists [u]) α) p ← whnfD ty
    | throwError "internal error: not an existential{indentExpr ty}"
  return mkApp4 (.const ``Exists.intro [u]) α p w pf

/-- `⟨w₁, …, wₙ, pf⟩` for the existentials `ty`. -/
partial def exIntros (ty : Expr) (ws : Array Expr) (pf : Expr) : MetaM Expr := do
  let some w := ws[0]? | return pf
  let .app (.app (.const ``Exists _) _) p ← whnfD ty
    | throwError "internal error: not an existential{indentExpr ty}"
  exIntro ty w (← exIntros (mkApp p w).headBeta (ws.extract 1 ws.size) pf)

/-- The `j`-th of the `n` disjuncts of the right-nested disjunction `D`. -/
def orAt (D : Expr) (n j : Nat) : Expr := Id.run do
  let mut D := D
  for _ in [0:j] do D := D.appArg!
  return if j + 1 < n then D.appFn!.appArg! else D

/-- A proof of the right-nested disjunction `D` of `n` disjuncts from a proof of its `j`-th. -/
partial def orIntro (D : Expr) (n j : Nat) (pf : Expr) : Expr :=
  if n ≤ 1 then pf
  else
    let (A, B) := (D.appFn!.appArg!, D.appArg!)
    if j == 0 then mkApp3 (mkConst ``Or.inl) A B pf
    else mkApp3 (mkConst ``Or.inr) A B (orIntro B (n - 1) (j - 1) pf)

/-- Cases on a hypothesis `h` that is a right-nested disjunction of `n` disjuncts (`False` for
none): a goal per disjunct, with its hypothesis. -/
partial def splitOr (g : MVarId) (h : FVarId) (n : Nat) : MetaM (Array (MVarId × FVarId)) := do
  if n == 0 then
    unless (← g.cases h).isEmpty do throwError "internal error: cases on `False`"
    return #[]
  if n == 1 then return #[(g, h)]
  let #[l, r] ← g.cases h | throwError "internal error: cases on a disjunction"
  return #[(l.mvarId, l.fields[0]!.fvarId!)] ++ (← splitOr r.mvarId r.fields[0]!.fvarId! (n - 1))

/-- The constructor `n` of an inductive family at the type `ty`: its explicit arguments `args`,
the others by unification. -/
def mkCtorAt (n : Name) (ty : Expr) (args : Array Expr) : MetaM Expr := withUnfolding do
  let f ← mkConstWithFreshMVarLevels n
  let (xs, bis, rty) ← forallMetaTelescope (← inferType f)
  unless ← isDefEq rty ty do throwError "internal error: `{n}` is not of type{indentExpr ty}"
  let ex := (xs.zip bis).filterMap fun (x, bi) => if bi.isExplicit then some x else none
  for x in ex, a in args do
    unless ← isDefEq x a do throwError "internal error: ill-typed argument of `{n}`{indentExpr a}"
  let r ← instantiateMVars (mkAppN f xs)
  if r.hasMVar then throwError "internal error: undetermined arguments of `{n}`{indentExpr r}"
  return r

/-- `n`, or `n` with `₀` appended until it is not one of `taken`. -/
partial def avoidName (taken : Array Name) (n : Name) : Name :=
  if taken.contains n then avoidName taken (n.appendAfter "₀") else n

/-- The first of `names` that is not the name of an argument of `c`, for a binder of a lemma
about `c`; when all are, the first with `₀` appended (`avoidName`). -/
def freeName (c : Ctor) (names : List Name) : Name :=
  let taken := c.args.map (·.name)
  (names.find? fun n => !taken.contains n).getD (avoidName taken names.head!)

/-- The type and index arguments at an index `i` of the presentation that is a constructor
application: the family at `projs i`, or in a block the type of the constructor of
`Blk.Poly.Ix` with its arguments. -/
def polyIdxType (P : Poly) (i : Expr) : MetaM (Nat × Array Expr) := do
  if !ctx.isBlock then return (0, ← ctx.projs i)
  let n := ctx.polyName "Ix"
  let some m := (Array.range ctx.types.size).find? fun m =>
      i.isAppOf (n ++ Name.mkSimple (ctx.shortName m))
    | throwError "internal error: not an index of a type of the block{indentExpr i}"
  return (m, i.getAppArgs.extract P.consts.size i.getAppNumArgs)

/-- The plain structure in two variables of the argument `f`, at the universe `lvl` under the
substitution `σ`, with the type and index arguments of its positions in `Y`: without indices the
structure itself, with indices the plain one at one index (`MixField.flat?`); `none` for an
indexed structure with positions at several indices. -/
def mixPlain (P : Poly) (f : MixField) (lvl : Level) (σ : Expr → Expr) :
    MetaM (Option (Expr × Nat × Array Expr)) := do
  if !ctx.idxed then return some (ctx.mixOccAt f lvl σ, 0, #[])
  let some (o₂, i₀) := f.flat? | return none
  let (m, idx) ← ctx.polyIdxType P (σ i₀)
  return some (substLevel ctx.uT lvl (σ o₂), m, idx)

/-- The family of the types at the premises `Hs` and `X` on the index of the presentation,
`fun j => T (H X) (ι j)`, curried as the children of a layer (`polyLayFam`). -/
def polyTFam (P : Poly) (Hs : Array Expr) (X : Expr) : TermElabM Expr := do
  ctx.polyLayFam P Hs X (mkAppN (← ctx.constWith ctx.name []) (ctx.polyParams P Hs X))

/-- `Tₘ (H X) idx`, the `m`-th type at the premises and its index arguments. -/
def polyTyAt (P : Poly) (X : Expr) (m : Nat) (idx : Array Expr) : MetaM Expr := do
  return mkAppN (← ctx.constWith (ctx.tyName m) []) (ctx.polyParams P P.Hs X ++ idx)

/-- `PolyIso.Mem (fun X => T (H X) idx) x t`, membership in a member `t` of the family at the
index `j` of the presentation, its index arguments `projs j`. -/
def polyMemAt (P : Poly) (X x j t : Expr) : TermElabM Expr := do
  isoMem (← ctx.polyIsoOf P 0 (← ctx.projs j)) X x t

/-- `Occ.map (Occ.ofIso (fun X => Tₘ (H X) idx)) (Occ.ofIso (fun X => Tₘ (H' X) idx)) f x`. -/
def polyLeafMap (P : Poly) (X Y f : Expr) (m : Nat) (idx : Array Expr) (x : Expr) :
    TermElabM Expr := do
  let o ← ctx.polyLeaf P m idx
  mkAppOptM ``Codata.Occ.map #[none, none, none, o, none, polyPrime P X Y o, X, Y, f, x]

/-- The map of a nested argument `y` with structure `n`, `σ` the substitution of the analysis'
arguments: the map of its structure, at the members the map of the leaf of their type. In a
block, through the instance of the argument's type as a functor of its members, which are of one
type. -/
def polyNestMap (P : Poly) (X Y f : Expr) (a : ArgInfo) (n : Nest) (σ : Expr → Expr) (y : Expr) :
    TermElabM Expr := do
  let L ← ctx.tLvl
  let o := P.subX P.Hs X (ctx.nestAt n L σ)
  let TX := mkAppN (← ctx.constWith ctx.name []) (ctx.polyParams P P.Hs X)
  if !ctx.idxed then
    let g ← lam `t TX fun t => ctx.polyLeafMap P X Y f 0 #[] t
    return ← mkAppOptM ``Codata.Occ.map
      #[none, none, none, o, none, polyPrime P X Y o, none, none, g, y]
  if !ctx.isBlock then
    let g ← lam `p ctx.J fun p => do
      let idx ← ctx.projs p
      lam `t (mkAppN TX idx) fun t => ctx.polyLeafMap P X Y f 0 idx t
    return ← mkAppOptM ``Codata.IOcc.map
      #[none, none, none, none, none, o, none, polyPrime P X Y o, none, none, g, y]
  let nm ← ctx.nestMem a n σ
  let nm := { nm with fn := P.subX P.Hs X nm.fn, inst := P.subX P.Hs X nm.inst }
  if nm.idx?.isNone then
    throwSeveralTypes a
  let elem := P.subX P.Hs X nm.elem
  let (m, idx) ← ctx.polyRecType elem
  let oF ← mkAppOptM ``Codata.Occ.ofIso #[← isoFun nm.inst, none, none, nm.inst]
  let g ← lam `t elem fun t => ctx.polyLeafMap P X Y f m idx t
  mkAppOptM ``Codata.Occ.map #[none, none, none, oF, none, polyPrime P X Y oF, none, none, g, y]

/-- `Tₘ.F (H X) Tₘ idx` of `dtor_c` at the arguments `ys`, with the proof of `dtor_c`, and the
fixpoint `T.Poly.fix` at `X`, its layer `toL` and its constructor `ctor ∘ ofL` (a function on
the index of the presentation with indices), with the proof that `d` undoes it if asked. -/
structure PolyCtorData where
  dtorc : Expr
  fc : Expr
  M : Expr
  toL : Expr
  ctorL : Expr
  hc? : Option Expr
  /-- The index of `Tₘ.c ys` in the presentation, with indices. -/
  i? : Option Expr

/-- The data of `PolyCtorData` for `c` at the arguments `ys` at `X`, with the proof that `d`
undoes `ctor ∘ ofL` when `inv`. -/
def polyCtorData (P : Poly) (X : Expr) (c : Ctor) (ys : Array Expr) (σ : Expr → Expr)
    (inv : Bool) : TermElabM PolyCtorData := do
  let L ← ctx.tLvl
  let pX := ctx.polyParams P P.Hs X
  let T := mkAppN (← ctx.constWith ctx.name []) pX
  let yL := [(P.fresh[2]!, L)]
  let M ← ctx.polyFixAt P [] P.Hs P.insts X
  let dtorc := mkAppN (← ctx.constWith (ctx.dtorRuleN c) []) (pX ++ ys)
  let some (_, _, fc) := (← inferType dtorc).eq?
    | throwError "internal error: `dtor_{c.name}` is not an equation"
  let rwTac := rwSteps #[(false, ctx.dtor_ctor), (false, ctx.polyName "toL_ofL")] (close := true)
  if !ctx.idxed then
    let toL ← lam `y (← ctx.polyF P X T L) fun y => ctx.polyAt P "toL" yL #[X, T, y]
    let ctorL ← lam `z (← ctx.polyLay P X T) fun z => do
      return mkAppN (← ctx.constWith ctx.ctor []) (pX.push (← ctx.polyAt P "ofL" yL #[X, T, z]))
    let hcTy ← withLocalDeclD `z (← ctx.polyLay P X T) fun z => do
      let d := mkApp toL (mkAppN (← ctx.constWith ctx.dtor []) (pX.push (mkApp ctorL z)))
      mkForallFVars #[z] (← mkEq (← Core.betaReduce d) z)
    let hc? ← if inv then some <$> withUnfolding (proveOn hcTy (← rwTac)) else pure none
    return { dtorc, fc, M, toL, ctorL, hc?, i? := none }
  let idxAt (i : Expr) : MetaM (Array Expr) := do ctx.projs (← ctx.polyIota P P.Hs X i)
  let i ← σ <$> ctx.polyIdx P c.idx
  let toL ← lam `y (← inferType fc) fun y => ctx.polyAt P "toL" yL #[X, T, i, y]
  let ctorL ← lam `i P.I (bi := .implicit) fun i => do
    lam `z (← ctx.polyILay P X T i) fun z => do
      return mkAppN (← ctx.constWith ctx.ctor [])
        (pX ++ (← idxAt i) |>.push (← ctx.polyAt P "ofL" yL #[X, T, i, z]))
  let hcTy ← withLocalDecl `i .implicit P.I fun i => do
    withLocalDeclD `z (← ctx.polyILay P X T i) fun z => do
      let d ← ctx.polyAt P "toL" yL #[X, T, i, mkAppN (← ctx.constWith ctx.dtor [])
        (pX ++ (← idxAt i) |>.push (mkApp2 ctorL i z))]
      mkForallFVars #[i, z] (← mkEq (← Core.betaReduce d) z)
  let hc? ← if inv then some <$> withUnfolding (proveOn hcTy (← rwTac)) else pure none
  return { dtorc, fc, M, toL, ctorL, hc?, i? := some i }

/-- `M.d (Tₘ.c ys) = toL (F.c ys)`, from `dtor_c`, with the left-hand side `M.d (Tₘ.c ys)`. -/
def PolyCtorData.dEq (d : PolyCtorData) (capp : Expr) : MetaM (Expr × Expr) := do
  let dD ← match d.i? with
    | some i => mkAppOptM ``Codata.IPolyFix.d #[none, none, none, none, none, none, d.M, i, capp]
    | none => mkAppOptM ``Codata.PolyFix.d #[none, none, none, none, none, none, none, d.M, capp]
  let hD ← mkCongrArg d.toL d.dtorc
  return (dD, ← mkExpectedTypeHint hD (← mkEq dD (d.toL.beta #[d.fc])))

/-- `Tₘ.Poly.map_c`. -/
def genPolyMapRule (P : Poly) (mi : Nat) : TermElabM Unit := do
  let v := P.vc[mi]!
  let c := v.ctor
  let cr := ctx.ctors[v.real]!
  withLocalDecl (freeName c [`X]) .implicit (mkSort P.lx.succ) fun X => do
  withLocalDecl (freeName c [`Y]) .implicit (mkSort P.lx'.succ) fun Y => do
  withLocalDeclD (freeName c [`f, `g, `h]) (← mkArrow X Y) fun f => do
  ctx.withPolyVArgs P X v fun locals reals ys σ => do
  let σ₀ (e : Expr) := e.replaceFVars c.fvars ys
  let prime := polyPrime P X Y
  let args' ← (c.args.zip ys).zipIdx.mapM fun ((a, y), k) => do
    if let some fd := P.fields[mi]!.find? (·.k == k) then
      let o := σ fd.occ
      return ← mkAppOptM ``Codata.Occ.map #[none, none, none, o, none, prime o, X, Y, f, y]
    if let some fd := (P.mixAt mi).find? (·.k == k) then
      -- In `X` by `f`, in the occurrences by the map of the type's leaf; with indices, of the
      -- leaf of the type at each index of the presentation.
      let L ← ctx.tLvl
      if let some (o, m, idx) ← ctx.mixPlain P fd L σ then
        let g ← lam `t (← ctx.polyTyAt P X m idx) fun t => ctx.polyLeafMap P X Y f m idx t
        return ← mkAppM ``Codata.Occ₂.map #[o, prime o, f, g, y]
      -- At several indices of a family: the map of the family's leaf at each index.
      if ctx.isBlock then
        throwSeveralTypes a
      let o := ctx.mixOccAt fd L σ
      let YF ← ctx.polyTFam P P.Hs X
      let YF' := prime YF
      let g ← lam `j P.I fun j => do
        let idx ← ctx.projs j
        lam `t (← ctx.polyTyAt P X 0 idx) fun t => ctx.polyLeafMap P X Y f 0 idx t
      return ← mkAppOptM ``Codata.IOcc₂.map
        #[none, none, none, none, none, none, o, none, prime o, X, YF, Y, YF', f, g, y]
    match a.kind with
    | .data => pure y
    | .plain _ =>
      let (m, idx) ← ctx.polyRecType (← inferType y)
      ctx.polyLeafMap P X Y f m idx y
    | .fn n => withReducible <| forallBoundedTelescope (← inferType y) n fun zs body => do
      let (m, idx) ← ctx.polyRecType body
      mkLambdaFVars zs (← ctx.polyLeafMap P X Y f m idx (mkAppN y zs))
    | .nest n => ctx.polyNestMap P X Y f a n σ₀ y
  let Tc ← ctx.constWith (ctx.tCtor cr) []
  let capp := mkAppN Tc (ctx.polyParams P P.Hs X ++ reals)
  let lhs ← ctx.polyLeafMap P X Y f cr.owner (cr.uidx.map σ) capp
  let rhs ← applyVCtor v (mkAppN (P.prime Tc) (ctx.polyParams P P.Hs' Y)) fun vi _ =>
    pure args'[vi]!
  let ty ← inferType rhs
  -- `M.map M' f (Tₘ.c ys) = c' ⟨(M.d (Tₘ.c ys)).1, …⟩` with `c' = ctor ∘ ofL` at `H'`, then
  -- `dtor_c` in it.
  let d ← ctx.polyCtorData P X cr reals σ (inv := true)
  let some hc := d.hc? | throwError "internal error: no inverse of the layer"
  let eqA ← withUnfolding <| match d.i? with
    | some i => mkAppOptM ``Codata.IPolyFix.map_eq_of_d #[none, none, none, none, none, none,
        d.M, none, none, prime d.M, f, prime d.ctorL, prime hc, i, capp]
    | none => mkAppOptM ``Codata.PolyFix.map_eq_of_d #[none, none, none, none, none, none,
        none, d.M, none, none, prime d.M, f, prime d.ctorL, prime hc, capp]
  let (dD, hD) ← d.dEq capp
  let some (_, _, rA) := (← inferType eqA).eq? | throwError "internal error: not an equation"
  let abs ← kabstract rA dD
  unless abs.hasLooseBVars do throwError "internal error: no layer in{indentExpr rA}"
  let pf ← mkEqTrans eqA (← mkCongrArg (.lam `d (← inferType dD) abs .default) hD)
  -- The right-hand side is the computed one by definition, which the kernel checks.
  let noIdx (o : Expr) := mkAppN o.getAppFn (o.getAppArgs.modify 0 DiscrTree.mkNoindexAnnotation)
  let lhs := mkAppN lhs.getAppFn (lhs.getAppArgs.modify 3 noIdx |>.modify 5 noIdx)
  let stmt := mkApp3 (.const ``Eq [← getLevel ty]) ty lhs rhs
  let xs := P.consts ++ P.Hs ++ P.Hs' ++ P.SR ++ P.insts ++ P.insts' ++ #[X, Y, f] ++ locals
  let (type, value) ← withBinderInfo (P.consts ++ P.Hs ++ P.Hs' ++ P.SR) .implicit do
    return (← mkForallFVars xs stmt, ← mkLambdaFVars xs pf)
  let n := ctx.tyName c.owner ++ `Poly ++ Name.mkSimple ("map_" ++ c.name.toString)
  addThm n (← ctx.levelParamsOf P.fresh #[type]) type value ctx.types[c.owner]!.ref
  addSimp n

/-- The disjunct of a nested argument `y` with structure `n` in `Tₘ.Poly.mem_c`:
`∃ t, Mem G t y ∧ Mem (fun X => Tₘ (H X) idx) x t`, or on the packed index
`∃ p t, IPolyIso.Mem G p t y ∧ …` when its positions are at several indices, also when they are
at one index only after cases on them, which the cases on the positions of a layer do not see;
with `bridge`, for an argument presented by its plain structure at one index (`MixField.flat?`),
by `PolyIso.Mem` at that index then too. -/
def polyNestMem (P : Poly) (X x : Expr) (c : Ctor) (a : ArgInfo) (n : Nest) (σ : Expr → Expr)
    (y : Expr) (bridge := false) : TermElabM Expr := do
  let nm ← ctx.nestMem a n σ bridge (anySum := bridge)
  let sub := P.subX P.Hs X
  let nm : NestMem := { nm with fn := sub nm.fn, inst := sub nm.inst, elem := sub nm.elem }
  let memT (t : Expr) : TermElabM Expr := do
    let (m, idx) ← ctx.polyRecType (← inferType t)
    isoMem (← ctx.polyIsoOf P m idx) X x t
  if nm.idx?.isSome then
    return ← withLocalDeclD (freeName c [`t]) nm.elem fun t => do
      mkExistsOver #[t] (mkAnd (← ctx.memProp nm y t #[]) (← memT t))
  if ctx.isBlock then
    throwSeveralTypes a
  withLocalDeclD (freeName c [`p]) ctx.J fun p => do
  withLocalDeclD (freeName c [`t]) (mkApp nm.elem p).headBeta fun t => do
    let im ← withUnfolding <| mkAppOptM ``Codata.IPolyIso.Mem
      #[none, nm.fn, none, none, none, nm.inst, nm.elem, p, t, y]
    mkExistsOver #[p, t] (mkAnd im (← memT t))

/-- Does the structure in two variables `o` go through a sum? Then its membership is stated by
`Occ₂.MemX` and `Occ₂.MemY`. -/
def hasSum₂ (o : Expr) : Bool := (o.find? (·.isConstOf ``Codata.Occ₂.sum)).isSome

/-- The structure in `X` alone of a structure in two variables `o`, the occurrences at the
constant `Y₀` and the variable at `lx`: what its contents in `X` are the members of, read as an
instance (`isoOf`). Its positions and contents are those of `o` in `X` by definition, unless `o`
goes through a sum (`hasSum₂`). -/
partial def xStruct (o Y₀ : Expr) (lx : Level) : MetaM Expr := do
  let ex ← explicitArgs o
  let const (A : Expr) : MetaM Expr := do
    return mkApp (← constAt ``Codata.Occ.const [(`u, lx), (`v, ← typeLevel A)]) A
  let under (n : Name) : MetaM Expr := do
    let f ← withLocalDeclD `x ex[0]! fun x => do
      mkLambdaFVars #[x] (← xStruct (ex[1]!.beta #[x]) Y₀ lx)
    mkAppM n #[ex[0]!, f]
  match o.getAppFn.constName? with
  | some ``Codata.Occ₂.ofX => return ex[0]!
  | some ``Codata.Occ₂.ofY =>
    let GY := (← whnfR (← inferType ex[0]!)).getAppArgs[2]!
    const (← Core.betaReduce (mkApp GY Y₀))
  | some ``Codata.Occ₂.const => const ex[0]!
  | some ``Codata.Occ₂.prod =>
    mkAppM ``Codata.Occ.prod #[← xStruct ex[0]! Y₀ lx, ← xStruct ex[1]! Y₀ lx]
  | some ``Codata.Occ₂.sum =>
    mkAppM ``Codata.Occ.sum #[← xStruct ex[0]! Y₀ lx, ← xStruct ex[1]! Y₀ lx]
  | some ``Codata.Occ₂.comp => mkAppM ``Codata.Occ.comp #[ex[0]!, ← xStruct ex[1]! Y₀ lx]
  | some ``Codata.Occ₂.pi => under ``Codata.Occ.pi
  | some ``Codata.Occ₂.piP => under ``Codata.Occ.piP
  | some ``Codata.Occ₂.sigma => under ``Codata.Occ.sigma
  | _ => throwError "internal error: unexpected structure in two variables{indentExpr o}"

/-- Close the goal `g` by `simp` with the default `simp` set: the refutation of a membership
without positions. -/
def simpClose (g : MVarId) : TermElabM Unit := do
  let sctx ← Simp.mkContext (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r?, _) ← simpGoal g sctx #[← Simp.getSimprocs]
  if let some (_, g) := r? then
    throwError "internal error: `simp` did not close{indentD (MessageData.ofGoal g)}"

/-- `Tₘ.Poly.mem_c`. -/
def genPolyMemRule (P : Poly) (mi : Nat) : TermElabM Unit := do
  let vc := P.vc[mi]!
  let c := vc.ctor
  let cr := ctx.ctors[vc.real]!
  let L ← ctx.tLvl
  withLocalDecl (freeName c [`X]) .implicit (mkSort P.lx.succ) fun X => do
  withLocalDeclD (freeName c [`x, `y, `z]) X fun x => do
  ctx.withPolyVArgs P X vc fun locals reals ys σ => do
  let σ₀ (e : Expr) := e.replaceFVars c.fvars ys
  let memOf (inst y : Expr) : MetaM Expr := isoMem inst X x y
  let TX := mkAppN (← ctx.constWith ctx.name []) (ctx.polyParams P P.Hs X)
  let mixOf (k : Nat) : Option MixField := (P.mixAt mi).find? (·.k == k)
  -- An argument with a structure in two variables but no parameter (in a block, at a type of the
  -- block after cases on its positions) has no members in `X`.
  let vacuous (fd : MixField) : Bool := (ctx.outside P.holes fd.arg.type).isEmpty
  -- Its disjunct for these, left out of the statement and refuted in the proof (`simp`).
  let vacuousX (k : Nat) : TermElabM (Option (Expr × Expr)) := do
    let some fd := mixOf k | return none
    if !vacuous fd then return none
    let some (o, m, idx) ← ctx.mixPlain P fd L σ | return none
    let y := ys[k]!
    let dX ← if hasSum₂ o then
        withUnfolding <| mkAppOptM ``Codata.Occ₂.MemX #[none, none, none, none, X,
          ← ctx.polyTyAt P X m idx, o, x, y]
      else memOf (← isoOf (← xStruct o (← ctx.polyTyAt P X m idx) P.lx) .plain) y
    return some (dX, ← proveHere (mkNot dX) simpClose)
  -- The disjuncts, with their arguments; an argument with a structure in two variables has two,
  -- its members in `X` (`false`) and the members of its occurrences (`true`).
  let ds ← (c.args.zip ys).zipIdx.flatMapM fun ((a, y), k) => do
    if let some fd := P.fields[mi]!.find? (·.k == k) then
      return #[((k, false), ← memOf (← isoOf (σ fd.occ) .plain) y)]
    if let some fd := mixOf k then
      -- The plain structure, at the type of its positions in `Y`: as without indices.
      if let some (o, m, idx) ← ctx.mixPlain P fd L σ then
        let TT ← ctx.polyTyAt P X m idx
        -- Across a sum the structures in each variable alone, read as instances, agree with the
        -- structure in two variables only after cases on the value: membership by the latter.
        if hasSum₂ o then
          let memY ← withLocalDeclD (freeName c [`t]) TT fun t => do
            let mY ← withUnfolding <| mkAppOptM ``Codata.Occ₂.MemY
              #[none, none, none, none, X, TT, o, t, y]
            mkExistsOver #[t] (mkAnd mY (← memOf (← ctx.polyIsoOf P m idx) t))
          if vacuous fd then return #[((k, true), memY)]
          return #[((k, false), ← withUnfolding <| mkAppOptM ``Codata.Occ₂.MemX
              #[none, none, none, none, X, TT, o, x, y]),
            ((k, true), memY)]
        let oX ← xStruct o TT P.lx
        let dY ← ctx.polyNestMem P X x c fd.arg fd.nest σ₀ y (bridge := true)
        if vacuous fd then return #[((k, true), dY)]
        return #[((k, false), ← memOf (← isoOf oX .plain) y), ((k, true), dY)]
      -- At several indices of a family: by the indexed structure, a member in `Y` with its index.
      if ctx.isBlock then
        throwSeveralTypes a
      let o := ctx.mixOccAt fd L σ
      let YF ← ctx.polyTFam P P.Hs X
      let memY ← withLocalDeclD (freeName c [`t]) (← mkAppM ``Sigma #[YF]) fun t => do
        let mY ← withUnfolding <| mkAppOptM ``Codata.IOcc₂.MemY
          #[none, none, none, none, none, none, X, YF, o, t, y]
        mkExistsOver #[t]
          (mkAnd mY (← ctx.polyMemAt P X x (← mkAppM ``Sigma.fst #[t]) (← mkAppM ``Sigma.snd #[t])))
      return #[((k, false), ← withUnfolding <| mkAppOptM ``Codata.IOcc₂.MemX
          #[none, none, none, none, none, none, X, YF, o, x, y]),
        ((k, true), memY)]
    match a.kind with
    | .data => return #[]
    | .plain _ =>
      let (m, idx) ← ctx.polyRecType (← inferType y)
      return #[((k, false), ← memOf (← ctx.polyIsoOf P m idx) y)]
    | .fn n => withReducible <| forallBoundedTelescope (← inferType y) n fun zs body => do
      let (m, idx) ← ctx.polyRecType body
      return #[((k, false), ← mkExistsOver zs (← memOf (← ctx.polyIsoOf P m idx) (mkAppN y zs)))]
    | .nest n => return #[((k, false), ← ctx.polyNestMem P X x c a n σ₀ y)]
  let n := ds.size
  let D := if n == 0 then Lean.mkConst ``False
    else ds.pop.foldr (init := ds.back!.2) fun (_, d) acc => mkOr d acc
  let dIdx (k : Nat × Bool) : Nat := (ds.findIdx? (·.1 == k)).getD 0
  let Tc ← ctx.constWith (ctx.tCtor cr) []
  let capp := mkAppN Tc (ctx.polyParams P P.Hs X ++ reals)
  let lhs ← memOf (← ctx.polyIsoOf P cr.owner (cr.uidx.map σ)) capp
  -- `Mem x (Tₘ.c ys) ↔ (∃ q, v q = x) ∨ ∃ b r, …`, for the layer `⟨s, v, k⟩` of `F.c ys`.
  let d ← ctx.polyCtorData P X cr reals σ (inv := false)
  let lay ← whnf (d.toL.beta #[d.fc])
  let pr ← whnf lay.appArg!
  let (s, v, k) := (lay.appFn!.appArg!, pr.appFn!.appArg!, pr.appArg!)
  let (_, hD) ← d.dEq capp
  let pf₁ ← withUnfolding <| match d.i? with
    | some i => mkAppOptM ``Codata.IPolyFix.exists_val_iff
        #[none, none, none, none, none, none, d.M, i, capp, s, v, k, hD, x]
    | none => mkAppOptM ``Codata.PolyFix.exists_val_iff
        #[none, none, none, none, none, none, none, d.M, capp, s, v, k, hD, x]
  let some (_, AB) := (← inferType pf₁).iff? | throwError "internal error: not an equivalence"
  -- The positions of the layer: those of the fields, of the recursive arguments.
  let hole ← if ctx.idxed then ctx.packFam TX else pure TX
  let nestToC (n : Nest) (y : Expr) : TermElabM Expr :=
    ctx.occFn `toC (P.subX P.Hs X (ctx.nestAt n L σ₀)) hole #[y]
  let YFi ← if ctx.idxed then ctx.polyTFam P P.Hs X else pure TX
  let vacs ← (P.mixAt mi).filterMapM fun fd => do
    return (← vacuousX fd.k).map fun (d, h) => (fd.k, d, h)
  let mp ← proveHere (← mkArrow AB D) fun g => do
    let (h, g) ← g.intro1
    let #[gl, gr] ← g.cases h | throwError "internal error: cases on a disjunction"
    -- A content of the layer: of a field.
    let #[sg] ← gl.mvarId.cases gl.fields[0]!.fvarId! | throwError "internal error: cases on `∃`"
    let (_, g) ← sg.mvarId.revert #[sg.fields[1]!.fvarId!]
    for sg in ← casesPos g sg.fields[0]!.fvarId! do
      let (hq, g) ← sg.mvarId.intro1
      g.withContext do
      let some fk := (P.fields[mi]!.map (·.k) ++ (P.mixAt mi).map (·.k)).find? fun k =>
          sg.ctorName == some (ctx.polyPos "P" c c.args[k]!)
        | throwError "internal error: unexpected position {sg.ctorName}"
      let D' ← instantiateMVars (← g.getType)
      if let some (_, dX, notX) := vacs.find? (·.1 == fk) then
        let (dX, notX) := (sg.subst.apply dX, sg.subst.apply notX)
        g.assign (← mkAbsurd D' (← exIntro dX sg.fields.back! (mkFVar hq)) notX)
      else
        let j := dIdx (fk, false)
        g.assign (orIntro D' n j (← exIntro (orAt D' n j) sg.fields.back! (mkFVar hq)))
    -- A content of a child.
    let #[sg] ← gr.mvarId.cases gr.fields[0]!.fvarId! | throwError "internal error: cases on `∃`"
    let (_, g) ← sg.mvarId.revert #[sg.fields[1]!.fvarId!]
    for sg in ← casesPos g sg.fields[0]!.fvarId! do
      let (hb, g) ← sg.mvarId.intro1
      g.withContext do
      let some (_, ki) := c.args.zipIdx.find? fun (a, k) =>
          (!a.kind.isData || (mixOf k).isSome) && sg.ctorName == some (ctx.polyPos "B" c a)
        | throwError "internal error: unexpected position {sg.ctorName}"
      let D' ← instantiateMVars (← g.getType)
      let mix? := mixOf ki
      let j := dIdx (ki, mix?.isSome)
      let dj := orAt D' n j
      let hb := mkFVar hb
      -- The kind of the argument: an argument with a structure in two variables is nested here.
      let kind := match mix? with
        | some fd => ArgKind.nest fd.nest
        | none => c.args[ki]!.kind
      let pf ← match kind with
        | .nest nst =>
          let q := sg.fields.back!
          let (tc, t₀) ← match mix? with
            | some fd => do
              let o := ctx.mixOccAt fd L σ
              let tc := sg.subst.apply (← toC₂ o X YFi ys[ki]!)
              let t₀ := mkApp (← mkAppM ``Prod.snd #[← mkAppM ``Sigma.snd #[tc]]) q
              if !ctx.idxed || fd.flat?.isSome then pure (tc, t₀) else
              -- At several indices, the member with its index.
              let some pidx := fd.pidx? | throwError "internal error: no index of a position"
              let j₀ := (mkApp2 (sg.subst.apply (σ pidx)) (← mkAppM ``Sigma.fst #[tc]) q).headBeta
              pure (tc, ← mkAppOptM ``Sigma.mk #[P.I, YFi, j₀, t₀])
            | none => do
              let tc := sg.subst.apply (← nestToC nst ys[ki]!)
              pure (tc, mkApp (← mkAppM ``Sigma.snd #[tc]) q)
          -- `⟨t₀, ⟨q, rfl⟩, hb⟩` for `∃ t, Mem G t y ∧ …`.
          let member (ty : Expr) : MetaM Expr := do
            let .app (.app (.const ``Exists _) _) pfun ← whnfD ty
              | throwError "internal error: not an existential{indentExpr ty}"
            let body := (mkApp pfun t₀).headBeta
            let memTy := body.appFn!.appArg!
            let .app (.app (.const ``Exists _) _) mfun ← whnfD memTy
              | throwError "internal error: not a membership{indentExpr memTy}"
            let some (_, _, r) := (mkApp mfun q).headBeta.eq?
              | throwError "internal error: not a membership{indentExpr memTy}"
            let mem ← exIntro memTy q (← mkEqRefl r)
            exIntro ty t₀ (mkApp4 (mkConst ``And.intro) memTy body.appArg! mem hb)
          let nm ← ctx.nestMem c.args[ki]! nst σ₀ (bridge := false)
          if mix?.isSome || nm.idx?.isSome then member dj
          else
            -- First the index of the position.
            let some pidx := nst.pidx? | throwError "internal error: no index of a position"
            let sub (e : Expr) := sg.subst.apply (P.subX P.Hs X (substLevel ctx.uT L (σ₀ e)))
            let p₀ := (mkApp2 (sub pidx) (← mkAppM ``Sigma.fst #[tc]) q).headBeta
            let .app (.app (.const ``Exists _) _) pfun ← whnfD dj
              | throwError "internal error: not an existential{indentExpr dj}"
            exIntro dj p₀ (← member (mkApp pfun p₀).headBeta)
        | .fn m => exIntros dj (sg.fields.extract (sg.fields.size - m) sg.fields.size) hb
        | _ => pure hb
      g.assign (orIntro D' n j pf)
  let mpr ← proveHere (← mkArrow D AB) fun g => do
    let (h, g) ← g.intro1
    for ((g, h), j) in (← splitOr g h n).zipIdx do
      g.withContext do
      let (ki, isY) := ds[j]!.1
      let a := c.args[ki]!
      let byB (g : MVarId) (args : Array Expr) (h : Expr) : MetaM Unit := g.withContext do
        let AB' ← instantiateMVars (← g.getType)
        let B := AB'.appArg!
        let b ← mkCtorAt (ctx.polyPos "B" c a) (← whnfD B).appFn!.appArg! args
        g.assign (mkApp3 (mkConst ``Or.inr) AB'.appFn!.appArg! B (← exIntro B b h))
      -- An argument with a structure in two variables: a field for its members in `X`, nested
      -- for the members of its occurrences.
      let kind := match mixOf ki, isY with
        | some fd, true => ArgKind.nest fd.nest
        | _, _ => a.kind
      match kind with
      | .data =>
        -- A field at a parameter position: a content of the layer.
        let g ← g.replaceLocalDeclDefEq h (← whnfD (← h.getType))
        let #[sg] ← g.cases h | throwError "internal error: cases on a membership"
        sg.mvarId.withContext do
        let AB' ← instantiateMVars (← sg.mvarId.getType)
        let A := AB'.appFn!.appArg!
        let q ← mkCtorAt (ctx.polyPos "P" c a) (← whnfD A).appFn!.appArg! #[sg.fields[0]!]
        sg.mvarId.assign (mkApp3 (mkConst ``Or.inl) A AB'.appArg! (← exIntro A q sg.fields[1]!))
      | .plain _ => byB g #[] (mkFVar h)
      | .fn m =>
        let mut g₁ := g
        let mut h₁ := h
        let mut zs := #[]
        for _ in [0:m] do
          let #[sg] ← g₁.cases h₁ | throwError "internal error: cases on `∃`"
          zs := zs.map sg.subst.apply |>.push sg.fields[0]!
          g₁ := sg.mvarId
          h₁ := sg.fields[1]!.fvarId!
        byB g₁ zs (mkFVar h₁)
      | .nest nst =>
        let several := (mixOf ki).isNone && (← ctx.nestMem a nst σ₀ (bridge := false)).idx?.isNone
        let mut g₁ := g
        let mut h₁ := h
        for _ in [0:if several then 2 else 1] do
          let #[sg] ← g₁.cases h₁ | throwError "internal error: cases on `∃`"
          g₁ := sg.mvarId
          h₁ := sg.fields[1]!.fvarId!
          -- With indices, a member in `Y` of a structure in two variables is a dependent pair of
          -- an index and a member there: its components.
          if ctx.idxed && (mixOf ki).any (·.flat?.isNone) then
            let #[sg'] ← g₁.cases sg.fields[0]!.fvarId!
              | throwError "internal error: cases on a member"
            g₁ := sg'.mvarId
            h₁ := (sg'.subst.apply (mkFVar h₁)).fvarId!
        let #[sg] ← g₁.cases h₁ | throwError "internal error: cases on `∧`"
        let (hm, hx) := (sg.fields[0]!.fvarId!, sg.fields[1]!.fvarId!)
        let g₂ ← sg.mvarId.withContext do
          sg.mvarId.replaceLocalDeclDefEq hm (← whnfD (← hm.getType))
        let #[sg] ← g₂.cases hm | throwError "internal error: cases on a membership"
        let hx := sg.subst.apply (mkFVar hx)
        let q := sg.fields[0]!
        let #[sg'] ← sg.mvarId.cases sg.fields[1]!.fvarId!
          | throwError "internal error: cases on the equation of a member"
        byB sg'.mvarId #[sg'.subst.apply q] (sg'.subst.apply hx)
  let pf₂ ← mkAppM ``Iff.intro #[mp, mpr]
  let pf ← mkAppM ``Iff.trans #[pf₁, pf₂]
  -- The statement is the proof's up to unfolding, which the kernel checks.
  let stmt := mkIff (mkAppN lhs.getAppFn (lhs.getAppArgs.modify 0 DiscrTree.mkNoindexAnnotation)) D
  let xs := P.consts ++ P.Hs ++ P.SR ++ P.insts ++ #[X, x] ++ locals
  let (type, value) ← withBinderInfo (P.consts ++ P.Hs ++ P.SR) .implicit do
    return (← mkForallFVars xs stmt, ← mkLambdaFVars xs pf)
  let n := ctx.tyName c.owner ++ `Poly ++ Name.mkSimple ("mem_" ++ c.name.toString)
  addThm n (← ctx.levelParamsOf P.fresh #[type]) type value ctx.types[c.owner]!.ref
  addSimp n

/-- The simp lemmas of the instances, `Tₘ.Poly.map_c` and `Tₘ.Poly.mem_c` for every constructor.
A failure is a warning: these are rolled back, and the instances stay. -/
def genPolySimp (P : Poly) : TermElabM Unit := do
  let s ← saveState
  tryCatchRuntimeEx
    (for mi in [0:P.vc.size] do
      -- Each with its own heartbeat budget, as the parts of the instances.
      let c := P.vc[mi]!.ctor
      let rule (s : String) : MessageData :=
        m!"`{ctx.tyName c.owner ++ `Poly ++ Name.mkSimple (s ++ c.name.toString)}`"
      withCurrHeartbeats <| stepPhase (rule "map_") <| ctx.genPolyMapRule P mi
      withCurrHeartbeats <| stepPhase (rule "mem_") <| ctx.genPolyMemRule P mi)
    fun e => do
      s.restore (restoreInfo := true)
      let ns ← getCurrNamespace
      let shorts := ctx.types.map fun t =>
        m!"`{(privateToUserName t.name).replacePrefix ns .anonymous}`"
      logWarning m!"no simp lemmas were generated for the instances of \
        {MessageData.joinSep shorts.toList ", "}; the instances are not affected.\n\
        {e.toMessageData}"

end Ctx

end Codata.Gen
