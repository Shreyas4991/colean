import Colean.Gen.Derive.Pres

/-!
# Generators on `Expr`, step 5: the layer

`T.Poly.toL` and `T.Poly.ofL` between `T.F (H X) Y` and the layer of the presentation, and their
laws `T.Poly.ofL_toL`, `T.Poly.toL_ofL`, `T.Poly.ofL_map`, without and with indices: the
declarations of the layer take the index of the presentation, given as `is`, `#[i]` or `#[]`.
-/

open Lean Meta Elab Term

namespace Codata.Gen

namespace Ctx

variable (ctx : Ctx)

/-! ### The layer: `toL`, `ofL` and their laws -/

/-- `T.F (H X) Y`, at the universe `w` of `Y`. -/
def polyF (P : Poly) (X Y : Expr) (w : Level) : MetaM Expr := do
  return mkAppN (← ctx.constWith ctx.F [w]) (ctx.polyParams P P.Hs X |>.push Y)

/-- `Lay (T.Poly.P psB) (T.Poly.B psB) X Y`. -/
def polyLay (P : Poly) (X Y : Expr) : MetaM Expr := do
  mkAppOptM ``Codata.Lay #[none, ← ctx.polyP P, ← ctx.polyB P, X, Y]

/-- With indices, the type of the family `Y` that `T.F (H X)` takes: `∀ j₁ j₂, Type w`, or
`Blk.Ix (H X) → Type w`. -/
def polyYTy (P : Poly) (Hs : Array Expr) (X : Expr) (w : Level) : TermElabM Expr := do
  return P.subX Hs X (← ctx.famType w)

/-- The family of the children of a layer, on the index of the presentation, from the family `Y`
that `T.F` takes: `fun j => Y (ι j)`, curried; `Y` itself for one index. -/
def polyLayFam (P : Poly) (Hs : Array Expr) (X Y : Expr) : TermElabM Expr := do
  if !ctx.isBlock && ctx.k == 1 then return Y
  lam `j P.I fun j => do return mkAppN Y (← ctx.projs (← ctx.polyIota P Hs X j))

/-- `ILay (T.Poly.sig psB) (T.Poly.P psB) X (fun j => Y (ι j)) i`. -/
def polyILay (P : Poly) (X Y i : Expr) : TermElabM Expr := do
  mkAppOptM ``Codata.ILay
    #[← ctx.polySig P, ← ctx.polyP P, X, ← ctx.polyLayFam P P.Hs X Y, i]

/-- `T.F (H X) Y (ι i)` at the index `i` of the presentation, at the universe `w` of `Y`. -/
def polyFI (P : Poly) (X Y i : Expr) (w : Level) : TermElabM Expr := do
  return mkAppN (← ctx.polyF P X Y w) (← ctx.projs (← ctx.polyIota P P.Hs X i))

/-- `T.Poly.idx psB i s b`, the index of the child at `b`. -/
def polyIdxAt (P : Poly) (i s b : Expr) : MetaM Expr := do
  return mkAppN (← polyConst (ctx.polyName "idx")) (P.psB ++ #[i, s, b])

/-- `(b : T.Poly.B psB i s) → Y (ι (T.Poly.idx b))`, the children of a layer at `i` and `s`. -/
def polyKidsTy (P : Poly) (X Y i s : Expr) : TermElabM Expr := do
  let layY ← ctx.polyLayFam P P.Hs X Y
  withLocalDeclD `b (mkApp2 (← ctx.polyB P) i s) fun b => do
    mkForallFVars #[b] (mkApp layY (← ctx.polyIdxAt P i s b)).headBeta

/-! The layer without and with indices: the declarations of the layer take the index `i` of the
presentation with indices, given as `is`, `#[i]` or `#[]`. -/

/-- Run `k` on `#[i]`, an implicit local variable `i` for the index of the presentation, or on `#[]`
without indices. -/
def withPolyIdx (P : Poly) (k : Array Expr → TermElabM α) : TermElabM α :=
  if ctx.idxed then withLocalDecl `i .implicit P.I fun i => k #[i] else k #[]

/-- The type of `Y` in `T.F (H X) Y`: `Type w`, with indices a family (`polyYTy`). -/
def polyYType (P : Poly) (X : Expr) (w : Level) : TermElabM Expr :=
  if ctx.idxed then ctx.polyYTy P P.Hs X w else pure (mkSort w.succ)

/-- `T.F (H X) Y`, with indices at the index `is = #[i]` of the presentation (`polyFI`). -/
def polyFAt (P : Poly) (X Y : Expr) (is : Array Expr) (w : Level) : TermElabM Expr :=
  match is[0]? with
  | some i => ctx.polyFI P X Y i w
  | none => ctx.polyF P X Y w

/-- The layer `Lay P B X Y`, with indices at the index `is = #[i]` (`polyILay`). -/
def polyLayAt (P : Poly) (X Y : Expr) (is : Array Expr) : TermElabM Expr :=
  match is[0]? with
  | some i => ctx.polyILay P X Y i
  | none => ctx.polyLay P X Y

/-- The contents of a layer at the shape `s`: `P s → X`, with indices `P i s → X`. -/
def polyContentsAt (P : Poly) (X : Expr) (is : Array Expr) (s : Expr) : TermElabM Expr := do
  mkArrow (mkAppN (← ctx.polyP P) (is.push s)) X

/-- The children of a layer at the shape `s`: `B s → Y`, with indices `polyKidsTy`. -/
def polyKidsAt (P : Poly) (X Y : Expr) (is : Array Expr) (s : Expr) : TermElabM Expr := do
  match is[0]? with
  | some i => ctx.polyKidsTy P X Y i s
  | none => mkArrow (mkApp (← ctx.polyB P) s) Y

/-- `Occ.ofC o ⟨sh, fun q => snd q⟩` for a plain structure, the structure of a field at a
parameter position, also when the type has indices. -/
def mkOfCPlain (o hole sh : Expr) (snd : Expr → TermElabM Expr) : TermElabM Expr :=
  ({ ctx with idx := #[] } : Ctx).mkOfC o hole sh snd

/-- `T.Poly.toL premises X Y a` (`ofL`, …): a declaration of this step over the premises, at
the universes `y` of `Y` (and `y'`) given by `σ`. -/
def polyAt (P : Poly) (s : String) (σ : List (Name × Level)) (args : Array Expr) : MetaM Expr := do
  return mkAppN (← polyConst (ctx.polyName s) σ) (P.premises ++ args)

/-- The substitution of the arguments of `c` by `ys`, and of the holes by `Hᵢ X`. -/
def polySubst (P : Poly) (c : Ctor) (ys : Array Expr) (X : Expr) (e : Expr) : Expr :=
  (e.replaceFVars c.fvars ys).replaceFVars P.holes (P.Hs.map (mkApp · X))

/-- The structure in two variables of `f`, its occurrences at `lvl`, under the substitution `σ`.
-/
def mixOccAt (f : MixField) (lvl : Level) (σ : Expr → Expr) : Expr :=
  substLevel ctx.uT lvl (σ f.occ)

/-- `Occ₂.toC o y`, at `X` and `Y`; for an indexed structure (`IOcc₂`) `IOcc₂.toC o y`, at `X`
and the family `Y` over the index of the presentation. -/
def toC₂ (o X Y y : Expr) : MetaM Expr := do
  if (← whnfR (← inferType o)).isAppOf ``Codata.IOcc₂ then
    return ← mkAppOptM ``Codata.IOcc₂.toC #[none, none, none, none, none, none, o, X, Y, y]
  mkAppOptM ``Codata.Occ₂.toC #[none, none, none, none, o, X, Y, y]

/-- `Occ₂.ofC o ⟨sh, fun q => c q, fun q => d q⟩`, at `X` and `Y`; for an indexed structure
`IOcc₂.ofC`, at `X` and the family `Y`. -/
def mkOfC₂ (o X Y sh : Expr) (c d : Expr → TermElabM Expr) : TermElabM Expr := do
  let f ← if (← whnfR (← inferType o)).isAppOf ``Codata.IOcc₂ then
      mkAppOptM ``Codata.IOcc₂.ofC #[none, none, none, none, none, none, o, X, Y]
    else mkAppOptM ``Codata.Occ₂.ofC #[none, none, none, none, o, X, Y]
  let D ← whnf (← whnf (← inferType f)).bindingDomain!
  unless D.isAppOfArity ``Sigma 2 do
    throwError "internal error: expected a layer, got{indentExpr D}"
  let (α, β) := (D.appFn!.appArg!, D.appArg!)
  let pr ← whnf (mkApp β sh).headBeta
  let (A, B) := (pr.appFn!.appArg!, pr.appArg!)
  let fn (T : Expr) (k : Expr → TermElabM Expr) : TermElabM Expr := do
    withLocalDeclD `q (← whnf T).bindingDomain!.headBeta fun q => do mkLambdaFVars #[q] (← k q)
  let p ← mkAppOptM ``Prod.mk #[A, B, ← fn A c, ← fn B d]
  return mkApp f (mkApp4 (.const ``Sigma.mk D.getAppFn.constLevels!) α β sh p)

/-- The layer of `F.c ys` (`toL`): `(fun z… => ⟨S.c data z.1…, positions, children⟩) (toC o x)…`.
-/
def polyLayer (P : Poly) (m : Nat) (X Y : Expr) (ys : Array Expr) : TermElabM Expr := do
  let c := P.vc[m]!.ctor
  let fs := P.fields[m]!
  let σ := polySubst P c ys X
  let toC (o hole y : Expr) : MetaM Expr :=
    mkAppOptM ``Codata.Occ.toC #[none, none, none, o, hole, y]
  -- With indices, the structure of a nested argument is indexed, at `Y` on the packed index.
  let hole ← if ctx.idxed then do pure (P.subX P.Hs X (← ctx.packFam Y)) else pure Y
  let ms := P.mixAt m
  -- The family of a structure in two variables: with indices, on the index of the presentation.
  let Yfam ← if ctx.idxed then ctx.polyLayFam P P.Hs X Y else pure Y
  let toCs := (← c.nests.mapM fun (a, n) => do
      let some k := c.args.findIdx? (·.fvar == a.fvar) | unreachable!
      ctx.occFn `toC (ctx.nestAt n P.ly σ) hole #[ys[k]!]) ++
    (← fs.mapM fun f => toC (σ f.occ) X ys[f.k]!) ++
    (← ms.mapM fun f => toC₂ (ctx.mixOccAt f P.ly σ) X Yfam ys[f.k]!)
  let names := c.nests.map (·.1.name) ++ fs.map (c.args[·.k]!.name) ++ ms.map (c.args[·.k]!.name)
  withLocalsN toCs.size (fun j => return (names[j]!.appendBefore "z_", .default,
      ← inferType toCs[j]!)) fun zs => do
  let plain := (c.args.zip ys).filterMap fun (a, y) =>
    if a.kind.isData && !fs.any (c.args[·.k]!.fvar == a.fvar) &&
      !ms.any (c.args[·.k]!.fvar == a.fvar) then some y else none
  -- The contents of the `j`-th argument with a structure in two variables: `fst` in `X`.
  let mixPart (sg : CasesSubgoal) (j : Nat) (fst : Bool) : TermElabM Expr := do
    let w ← mkAppM ``Sigma.snd #[sg.subst.apply zs[c.nests.size + fs.size + j]!]
    return mkApp (← mkAppM (if fst then ``Prod.fst else ``Prod.snd) #[w]) sg.fields.back!
  let shape ← ctx.polySCtor P m (plain ++ (← zs.mapM fun z => mkAppM ``Sigma.fst #[z]))
  -- With indices, the index of the layer (translated before the substitution, which changes the
  -- parameters of the block's index).
  let i? ← if ctx.idxed then some <$> σ <$> ctx.polyIdx P c.idx else pure none
  -- The positions and the children, by cases (in general position with indices).
  let byCases (ty : Expr) (val : Name → CasesSubgoal → TermElabM Expr) : TermElabM Expr := do
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (b, g') ← g.mvarId!.intro1
    for sg in ← if ctx.idxed then casesPos g' b else g'.cases b do
      let some n := sg.ctorName | throwError "internal error: no constructor"
      let v ← val n sg
      sg.mvarId.withContext do
        unless ← isDefEq (← sg.mvarId.getType) (← inferType v) do
          throwError "internal error: ill-typed position{indentExpr v}"
        sg.mvarId.assign v
    instantiateMVars g
  let pf ← byCases (← ctx.polyContentsAt P X i?.toArray shape) fun n sg => do
    if let some j := ms.findIdx? fun f => n == ctx.polyPos "P" c c.args[f.k]! then
      return ← mixPart sg j true
    let some j := fs.findIdx? fun f => n == ctx.polyPos "P" c c.args[f.k]!
      | throwError "internal error: unexpected position {n}"
    return mkApp (← mkAppM ``Sigma.snd #[sg.subst.apply zs[c.nests.size + j]!]) sg.fields.back!
  let bf ← byCases (← ctx.polyKidsAt P X Y i?.toArray shape) fun n sg => do
    if let some j := ms.findIdx? fun f => n == ctx.polyPos "B" c c.args[f.k]! then
      return ← mixPart sg j false
    let some k := c.args.findIdx? fun a => !a.kind.isData && n == ctx.polyPos "B" c a
      | throwError "internal error: unexpected position {n}"
    let a := c.args[k]!
    match a.kind with
    | .nest _ =>
      let some j := c.nests.findIdx? (·.1.fvar == a.fvar) | unreachable!
      let v := mkApp (← mkAppM ``Sigma.snd #[sg.subst.apply zs[j]!]) sg.fields.back!
      -- In a block, the child's index must be the block's index of the presentation's.
      if ctx.isBlock then
        let ok ← sg.mvarId.withContext do isDefEq (← sg.mvarId.getType) (← inferType v)
        unless ok do
          throwLimit m!"the positions of the nested argument `{a.name}` of `{c.name}` are at a \
            type of the block only after cases on them, as through a product or a sum inside a \
            named type constructor, which is not supported for the types of a block"
      return v
    | .fn n => return mkAppN (sg.subst.apply ys[k]!) (sg.fields.extract (sg.fields.size - n))
    | _ => return sg.subst.apply ys[k]!
  let lay ← match i? with
    | some i =>
      let layTy ← whnfR (← ctx.polyILay P X Y i)
      mkAppOptM ``Sigma.mk
        #[layTy.appFn!.appArg!, layTy.appArg!, shape, ← mkAppM ``Prod.mk #[pf, bf]]
    | none =>
      let β ← lam `s (← ctx.polyS P) fun s => do
        mkAppM ``Prod
          #[← mkArrow (mkApp (← ctx.polyP P) s) X, ← mkArrow (mkApp (← ctx.polyB P) s) Y]
      mkAppOptM ``Sigma.mk #[← ctx.polyS P, β, shape, ← mkAppM ``Prod.mk #[pf, bf]]
  return mkAppN (← mkLambdaFVars zs lay) toCs

/-- The value of an argument with template `t` and type `D` (of `F.c` or `T.c`, read through
`whnfOcc`) from the values of the parts on the way through it, `valOf vi D'` for the `vi`-th
argument of the presentation, at its type `D'`: pairs and injections. Returns the next `vi` and
the next position in the alternatives `choices`. -/
partial def buildArg (choices : Array Bool) (valOf : Nat → Expr → TermElabM Expr) :
    Tpl → Expr → Nat → Nat → TermElabM (Expr × Nat × Nat)
  | .part _, D, vi, ci => do return (← valOf vi D, vi + 1, ci)
  | .prod l r, D, vi, ci => do
    let D ← whnfOcc D
    let (A, B) := (D.appFn!.appArg!, D.appArg!)
    let (x, vi, ci) ← buildArg choices valOf l A vi ci
    let (y, vi, ci) ← buildArg choices valOf r B vi ci
    return (← mkAppOptM ``Prod.mk #[A, B, x, y], vi, ci)
  | .sum l r _ _, D, vi, ci => do
    let D ← whnfOcc D
    let (A, B) := (D.appFn!.appArg!, D.appArg!)
    if choices[ci]! then
      let (x, vi, ci) ← buildArg choices valOf l A vi (ci + 1)
      return (← mkAppOptM ``Sum.inl #[A, B, x], vi, ci)
    else
      let (x, vi, ci) ← buildArg choices valOf r B vi (ci + 1)
      return (← mkAppOptM ``Sum.inr #[A, B, x], vi, ci)

/-- The constructor `fn`, a function of the arguments of the real constructor of `v`, applied to
the values of the arguments of `v` (`valOf vi D`, at the type `D` of the part): each argument
built from its parts (`buildArg`). -/
def applyVCtor (v : VCtor) (fn : Expr) (valOf : Nat → Expr → TermElabM Expr) :
    TermElabM Expr := do
  let mut fn := fn
  let mut ty ← inferType fn
  let mut vi := 0
  let mut ci := 0
  for t in v.tpls do
    ty ← whnf ty
    let (val, vi', ci') ← buildArg v.choices valOf t ty.bindingDomain! vi ci
    vi := vi'
    ci := ci'
    fn := mkApp fn val
    ty := ty.bindingBody!.instantiate1 val
  return fn

/-- `F.c (H X) Y args` from the shape arguments `sargs` of `S.c` and the contents `v`, `k` of a
layer (`ofL`): a field at a parameter position is `Occ.ofC o ⟨x_s, fun q => v (P.c_x q)⟩`, a
recursive argument `k (B.c_y)`, under its telescope or through its structure, an argument with a
structure in two variables `Occ₂.ofC o ⟨p_s, fun q => v (P.c_p q), fun q => k (B.c_p q)⟩`; a
split argument the pair or injection of its parts. -/
def polyOfLBody (P : Poly) (m : Nat) (X Y v k : Expr) (sargs : Array Expr) :
    TermElabM Expr := do
  let vc := P.vc[m]!
  let c := vc.ctor
  let fs := P.fields[m]!
  let plainArgs := polyPlain P m
  let np := plainArgs.size
  let shs := sargs.extract np sargs.size
  let σd (e : Expr) : Expr :=
    (e.replaceFVars (plainArgs.map (·.fvar)) (sargs.extract 0 np)).replaceFVars P.holes
      (P.Hs.map (mkApp · X))
  let posApp (s : String) (a : ArgInfo) (extra : Array Expr) : MetaM Expr := do
    return mkAppN (← polyConst (ctx.polyPos s c a)) (P.psB ++ sargs ++ extra)
  -- The occurrences of the nested structures: `Y`, or with indices `Y` on the packed index; of
  -- the structures in two variables `Y`, or with indices on the index of the presentation.
  let hole ← if ctx.idxed then pure (P.subX P.Hs X (← ctx.packFam Y)) else pure Y
  let Yfam ← if ctx.idxed then ctx.polyLayFam P P.Hs X Y else pure Y
  let valOf (i : Nat) (D : Expr) : TermElabM Expr := do
    let a := c.args[i]!
    match a.kind with
    | .data =>
      if let some j := fs.findIdx? (·.k == i) then
        ctx.mkOfCPlain (σd fs[j]!.occ) X shs[c.nests.size + j]! fun q => do
          return mkApp v (← posApp "P" a #[q])
      else if let some j := (P.mixAt m).findIdx? (·.k == i) then
        mkOfC₂ (ctx.mixOccAt (P.mixAt m)[j]! P.ly σd) X Yfam shs[c.nests.size + fs.size + j]!
          (fun q => do return mkApp v (← posApp "P" a #[q]))
          (fun q => do return mkApp k (← posApp "B" a #[q]))
      else
        let some di := plainArgs.findIdx? (·.fvar == a.fvar) | unreachable!
        pure sargs[di]!
    | .plain _ => pure (mkApp k (← posApp "B" a #[]))
    | .fn n => withTele n D fun zs _ => do
      mkLambdaFVars zs (mkApp k (← posApp "B" a zs))
    | .nest n =>
      let some j := c.nests.findIdx? (·.1.fvar == a.fvar) | unreachable!
      ctx.mkOfC (substLevel ctx.uT P.ly (σd n.occ)) hole shs[j]! fun q => do
        return mkApp k (← posApp "B" a #[q])
  let cr := ctx.ctors[vc.real]!
  applyVCtor vc (mkAppN (← ctx.constWith (ctx.fCtor cr) [P.ly])
    (ctx.polyParams P P.Hs X |>.push Y)) valOf

/-- The term `k vi vs` at the constructor `vi` of the presentation of the `mr`-th constructor
with arguments `ys`, `vs` its arguments: through a product the projections, through a sum
`Sum.casesOn`, at the type of the term, which must not depend on the alternative. -/
partial def polyDispatch (P : Poly) (mr : Nat) (ys : Array Expr)
    (k : Nat → Array Expr → TermElabM Expr) : TermElabM Expr := do
  let some v := P.vc.find? (·.real == mr) | throwError "internal error: no constructor {mr}"
  let rec go : List (Tpl × Expr) → Array Bool → Array Expr → TermElabM Expr
    | [], cs, vs => do
      let some vi := P.vc.findIdx? fun v => v.real == mr && v.choices == cs
        | throwError "internal error: no constructor of the presentation"
      k vi vs
    | (.part _, y) :: rest, cs, vs => go rest cs (vs.push y)
    | (.prod l r, y) :: rest, cs, vs => do
      go ((l, ← mkAppM ``Prod.fst #[y]) :: (r, ← mkAppM ``Prod.snd #[y]) :: rest) cs vs
    | (.sum l r _ _, y) :: rest, cs, vs => do
      let D ← whnfOcc (← inferType y)
      let (A, B) := (D.appFn!.appArg!, D.appArg!)
      let lb ← withLocalDeclD `a A fun a => do
        mkLambdaFVars #[a] (← go ((l, a) :: rest) (cs.push true) vs)
      let rb ← withLocalDeclD `b B fun b => do
        mkLambdaFVars #[b] (← go ((r, b) :: rest) (cs.push false) vs)
      let mty ← withLocalDeclD `a A fun a => do inferType (mkApp lb a).headBeta
      let motive ← withLocalDeclD `t D fun t => mkLambdaFVars #[t] mty
      mkAppOptM ``Sum.casesOn #[A, B, motive, y, lb, rb]
  go (v.tpls.toList.zip ys.toList) #[] #[]

/-- Split the arguments `ys` of the `mr`-th constructor, in the goal `g`, along their templates:
`cases` on the local variables of the products and sums. The goals, each with its constructor of
the presentation and the values of its arguments. -/
partial def polyDestructure (P : Poly) (mr : Nat) (g : MVarId) (ys : Array Expr) :
    MetaM (Array (MVarId × Nat × Array Expr)) := do
  let some v := P.vc.find? (·.real == mr) | throwError "internal error: no constructor {mr}"
  let rec go : MVarId → List (Tpl × Expr) → Array Bool → Array Expr →
      MetaM (Array (MVarId × Nat × Array Expr))
    | g, [], cs, vs => do
      let some vi := P.vc.findIdx? fun v => v.real == mr && v.choices == cs
        | throwError "internal error: no constructor of the presentation"
      return #[(g, vi, vs)]
    | g, (.part _, y) :: rest, cs, vs => go g rest cs (vs.push y)
    | g, (t, y) :: rest, cs, vs => do
      let sgs ← g.cases y.fvarId!
      let sub (sg : CasesSubgoal) (e : Expr) : Expr := sg.subst.apply e
      match t, sgs with
      | .prod l r, #[sg] =>
        go sg.mvarId ((l, sg.fields[0]!) :: (r, sg.fields[1]!) ::
          rest.map fun (t, e) => (t, sub sg e)) cs (vs.map (sub sg))
      | .sum l r _ _, #[sl, sr] =>
        return (← go sl.mvarId ((l, sl.fields[0]!) :: rest.map fun (t, e) => (t, sub sl e))
            (cs.push true) (vs.map (sub sl))) ++
          (← go sr.mvarId ((r, sr.fields[0]!) :: rest.map fun (t, e) => (t, sub sr e))
            (cs.push false) (vs.map (sub sr)))
      | _, _ => throwError "internal error: cases on a split argument"
  go g (v.tpls.toList.zip ys.toList) #[] #[]

/-- The type `T.F (H X) Y idx…` of `a` once the index of the presentation is split into its
components: the indices reduced, `⟨i₁, i₂⟩.1` to `i₁`, in a block `ι (Blk.Poly.Ix.Tₘ idx)` to
`Blk.Ix.Tₘ idx`, so that cases on `a` see them. -/
def polyWhnfIdx (ty : Expr) : MetaM Expr := do
  let np := ctx.params.size + 1
  let args ← ty.getAppArgs.mapIdxM fun k e => if k < np then pure e else whnf e
  return mkAppN ty.getAppFn args

/-- `toL` in a block, on the goal `g : ILay … i` with `a : Blk.F (H X) Y (ι i)`: by cases on the
index `i`, then on `a`, whose index `ι i` is then `Blk.Ix.Tₘ idx`, which drops the constructors of
the other types and solves the equations of the indices (the `idx` are variables). -/
def polyToLBlock (P : Poly) (X Y : Expr) (g : MVarId) (i : FVarId) : TermElabM Unit := do
  for sg in ← g.cases i do
    sg.mvarId.withContext do
    let some a := (← getLCtx).lastDecl | throwError "internal error: no layer to destructure"
    let g ← sg.mvarId.replaceLocalDeclDefEq a.fvarId (← ctx.polyWhnfIdx (← instantiateMVars a.type))
    for sg in ← g.cases a.fvarId do
      sg.mvarId.withContext do
      let some m := ctx.ctors.findIdx? fun c => sg.ctorName == some (ctx.fCtor c)
        | throwError "internal error: unexpected case {sg.ctorName}"
      let v ← polyDispatch P m sg.fields fun vi vs => ctx.polyLayer P vi X Y vs
      unless ← isDefEq (← sg.mvarId.getType) (← inferType v) do
        throwError "internal error: ill-typed layer{indentExpr v}"
      sg.mvarId.assign v

/-- `T.Poly.toL` and `T.Poly.ofL`, between `T.F (H X) Y` and the layer `Lay P B X Y`; with indices
at an index `i` of the presentation, between `T.F (H X) Y (ι i)` and the layer at `i`. `toL` is by
cases on `F` (in a block `polyToLBlock`), `ofL` by cases on the shape. -/
def genPolyLayer (P : Poly) : TermElabM Unit := do
  withLocalDecl `X .implicit (mkSort P.lx.succ) fun X => do
  withLocalDecl `Y .implicit (← ctx.polyYType P X P.ly) fun Y => do
  ctx.withPolyIdx P fun is => do
  let FXY ← ctx.polyFAt P X Y is P.ly
  let lay ← ctx.polyLayAt P X Y is
  -- `toL`
  withLocalDeclD `a FXY fun a => do
    let value ← if ctx.isBlock then do
        let g ← mkFreshExprSyntheticOpaqueMVar lay
        ctx.polyToLBlock P X Y g.mvarId! is[0]!.fvarId!
        instantiateMVars g
      else do
        let np := ctx.params.size + 1
        mkCasesOnApp ctx.F (← ctx.levelsWith ctx.F [P.ly]) FXY.getAppArgs a (← getLevel lay)
          (fun js _ => do
            if !ctx.idxed then return lay
            ctx.polyILay P X Y (← ctx.pack (← fullIdx ctx.F np FXY.getAppArgs js)))
          fun cname xs => do
            let some m := ctx.ctors.findIdx? (ctx.fCtor · == cname)
              | throwError "internal error: unexpected constructor {cname}"
            polyDispatch P m (← ctorArgsOf ctx.F np FXY.getAppArgs xs ctx.ctors[m]!.args.size)
              fun vi vs => ctx.polyLayer P vi X Y vs
    ctx.addPolyDef P "toL" (P.premises ++ #[X, Y] ++ is |>.push a) lay value
  -- `ofL`
  withLocalDeclD `z lay fun z => do
    let S ← ctx.polyS P
    let Sn := ctx.polyName "S"
    let s ← mkAppM ``Sigma.fst #[z]
    let w ← mkAppM ``Sigma.snd #[z]
    let motive (js : Array Expr) (s : Expr) : TermElabM Expr := do
      mkArrow (← ctx.polyContentsAt P X js s)
        (← mkArrow (← ctx.polyKidsAt P X Y js s) (← ctx.polyFAt P X Y js P.ly))
    let args := P.psB ++ is
    let value ← mkCasesOnApp Sn S.getAppFn.constLevels! args s (← getLevel (← motive is s))
      (fun js s => do
        if !ctx.idxed then return ← motive #[] s
        motive #[(← fullIdx Sn P.psB.size args js)[0]!] s)
      fun cname xs => do
        let some m := P.vc.findIdx? (Sn ++ ·.ctor.fname == cname)
          | throwError "internal error: unexpected constructor {cname}"
        let nsh := P.vc[m]!.ctor.nests.size + P.fields[m]!.size + (P.mixAt m).size
        let sargs ← ctorArgsOf Sn P.psB.size args xs ((polyPlain P m).size + nsh)
        let shape := mkAppN (← polyConst cname) (P.psB ++ sargs)
        let js ← if ctx.idxed then do pure #[(← whnf (← inferType shape)).appArg!] else pure #[]
        lam `v (← ctx.polyContentsAt P X js shape) fun v => do
          lam `k (← ctx.polyKidsAt P X Y js shape) fun k => ctx.polyOfLBody P m X Y v k sargs
    let value := mkApp2 value (← mkAppM ``Prod.fst #[w]) (← mkAppM ``Prod.snd #[w])
    ctx.addPolyDef P "ofL" (P.premises ++ #[X, Y] ++ is |>.push z) FXY value

/-- Destructure a layer `z = ⟨s, v, k⟩` and run `k` on each case of the shape, with its
constructor. -/
def polyCasesLay (P : Poly) (g : MVarId) (z : Expr) (k : Nat → MVarId → TermElabM Unit)
    (i? : Option Expr := none) : TermElabM Unit := do
  let #[sg] ← g.cases z.fvarId! | throwError "internal error: cases on a layer"
  let #[sg'] ← sg.mvarId.cases sg.fields[1]!.fvarId! | throwError "internal error: cases on a pair"
  let s := sg'.subst.apply sg.fields[0]!
  -- With indices, the shape is at the variable `i`, which the cases instantiate.
  let S ← match i? with
    | some i => pure (mkApp (← ctx.polyS P) (sg'.subst.apply (sg.subst.apply i)))
    | none => ctx.polyS P
  let g ← sg'.mvarId.withContext do sg'.mvarId.replaceLocalDeclDefEq s.fvarId! S
  for sg in ← g.cases s.fvarId! do
    let some m := P.vc.findIdx? fun v => sg.ctorName == some (ctx.polyName "S" ++ v.ctor.fname)
      | throwError "internal error: unexpected shape {sg.ctorName}"
    k m sg.mvarId

/-- Split the index `i` of the presentation into its components by cases, for cases on
`a : T.F (H X) Y (ι i)`: nothing for one index, the dependent pairs for several, in a block the
type and its indices. Returns the goals with `a`, its type at the components (`polyWhnfIdx`). -/
def polyCasesIdx (g : MVarId) (i a : FVarId) : MetaM (Array (MVarId × FVarId)) := do
  if !ctx.isBlock && ctx.k == 1 then return #[(g, a)]
  let rec split (g : MVarId) (i : FVarId) : Nat → MetaM (Array MVarId)
    | n + 1 => do
      let sgs ← g.cases i
      if ctx.isBlock || n ≤ 1 then return sgs.map (·.mvarId)
      sgs.flatMapM fun sg => split sg.mvarId sg.fields.back!.fvarId! n
    | 0 => return #[g]
  (← split g i ctx.k).mapM fun g => g.withContext do
    let some a := (← getLCtx).lastDecl | throwError "internal error: no layer to destructure"
    let g ← g.replaceLocalDeclDefEq a.fvarId (← ctx.polyWhnfIdx (← instantiateMVars a.type))
    return (g, a.fvarId)

/-- `IOcc.map o o' g y` pushed through the products and sums of `o` at a pair or an injection
`y`, down to the maps of their components: definitionally equal, without `simp` lemmas for these
maps. Other terms are kept. -/
partial def pushIMap (e : Expr) : MetaM Expr := do
  unless e.isAppOf ``Codata.IOcc.map do return e
  let ex ← explicitArgs e
  let #[o, o', g, y] := ex | return e
  let y ← whnfR y
  let comps (o : Expr) : MetaM (Expr × Expr) := do
    let ex ← explicitArgs o
    return (ex[0]!, ex[1]!)
  let types : MetaM (Expr × Expr) := do
    let ty ← whnfOcc (← inferType e)
    return (ty.appFn!.appArg!, ty.appArg!)
  let head := o.getAppFn.constName?.getD .anonymous
  if head == ``Codata.IOcc.prod && y.isAppOfArity ``Prod.mk 4 then
    let (A, B) ← types
    let ((o₁, o₂), (o₁', o₂')) := (← comps o, ← comps o')
    let x₁ ← pushIMap (← mkAppM ``Codata.IOcc.map #[o₁, o₁', g, y.appFn!.appArg!])
    let x₂ ← pushIMap (← mkAppM ``Codata.IOcc.map #[o₂, o₂', g, y.appArg!])
    return ← mkAppOptM ``Prod.mk #[A, B, x₁, x₂]
  if head == ``Codata.IOcc.sum && (y.isAppOfArity ``Sum.inl 3 || y.isAppOfArity ``Sum.inr 3) then
    let (A, B) ← types
    let ((o₁, o₂), (o₁', o₂')) := (← comps o, ← comps o')
    if y.isAppOfArity ``Sum.inl 3 then
      let x ← pushIMap (← mkAppM ``Codata.IOcc.map #[o₁, o₁', g, y.appArg!])
      return ← mkAppOptM ``Sum.inl #[A, B, x]
    if y.isAppOfArity ``Sum.inr 3 then
      let x ← pushIMap (← mkAppM ``Codata.IOcc.map #[o₂, o₂', g, y.appArg!])
      return ← mkAppOptM ``Sum.inr #[A, B, x]
  return e

/-- A proof of `∀ {Y Y'} g y, IOcc.map oA oA' g y = Occ.map oY oY' (g i) y` in the goal `g`, under
the binder of a point first for a combinator under a binder: the map of an indexed structure
whose positions are all at the index `i` is the map at `i` of the plain structure of the same form
(the hypothesis of `IOcc₂.AgreeY.ofOcc₂`). By definition without a sum; across one only after
cases on the value, so through the lemma of each combinator (`IOcc.map_flat_sum`, …), whose
arguments are the components of the two structures. -/
partial def proveMapFlat (g : MVarId) : MetaM Unit := do
  let ty ← instantiateMVars (← g.getType)
  let (n, isEq) ← forallTelescopeReducing ty fun xs b => return (xs.size, b.isEq)
  unless isEq do throwError "internal error: not a map at one index{indentExpr ty}"
  -- Under the binder of a point: at that point.
  if n > 4 then
    let (_, g) ← g.intro1
    return ← proveMapFlat g
  let (oA, oA', oY, oY', i) ← forallTelescopeReducing ty fun _ b => do
    let some (_, lhs, rhs) := b.eq? | unreachable!
    let l ← explicitArgs lhs
    let r ← explicitArgs rhs
    return (l[0]!.headBeta, l[1]!.headBeta, r[0]!.headBeta, r[1]!.headBeta, r[2]!.appArg!)
  if (oA.find? (·.isConstOf ``Codata.IOcc.sum)).isNone then
    return ← withUnfolding do
      let (_, g) ← g.intros
      g.refl
  let (exA, exA', exY, exY') := (← explicitArgs oA, ← explicitArgs oA', ← explicitArgs oY,
    ← explicitArgs oY')
  let (thm, args) ← match oA.getAppFn.constName? with
    | some ``Codata.IOcc.prod => pure (``Codata.IOcc.map_flat_prod,
        #[exY[0]!, exY'[0]!, exY[1]!, exY'[1]!, exA[0]!, exA'[0]!, exA[1]!, exA'[1]!])
    | some ``Codata.IOcc.sum => pure (``Codata.IOcc.map_flat_sum,
        #[exY[0]!, exY'[0]!, exY[1]!, exY'[1]!, exA[0]!, exA'[0]!, exA[1]!, exA'[1]!])
    | some ``Codata.IOcc.pi =>
      pure (``Codata.IOcc.map_flat_pi, #[exY[1]!, exY'[1]!, exA[1]!, exA'[1]!])
    | some ``Codata.IOcc.piP =>
      pure (``Codata.IOcc.map_flat_piP, #[exY[1]!, exY'[1]!, exA[1]!, exA'[1]!])
    | some ``Codata.IOcc.sigma =>
      pure (``Codata.IOcc.map_flat_sigma, #[exY[1]!, exY'[1]!, exA[1]!, exA'[1]!])
    | some ``Codata.IOcc.compC => pure (``Codata.IOcc.map_flat_compC,
        #[exA[0]!, exA'[0]!, exY[1]!, exY'[1]!, exA[1]!, exA'[1]!])
    | _ => throwError "internal error: no map at one index through{indentExpr oA}"
  -- The lemma up to its family `Y`: its explicit arguments the index, the structures, then the
  -- hypotheses of the components, proved the same way.
  let f ← mkConstWithFreshMVarLevels thm
  let fTy ← inferType f
  let k ← forallTelescope fTy fun ys _ => do
    let some k ← ys.findIdxM? fun y => return (← y.fvarId!.getUserName) == `Y
      | throwError "internal error: no family in `{thm}`"
    return k
  let (xs, bis, _) ← forallMetaBoundedTelescope fTy k
  let explicit := (xs.zip bis).filterMap fun (x, bi) => if bi.isExplicit then some x else none
  withUnfolding do
    for x in explicit, a in #[i] ++ args do
      unless ← isDefEq x a do
        throwError "internal error: ill-typed argument of `{thm}`{indentExpr a}"
    let pf ← instantiateMVars (mkAppN f xs)
    unless ← isDefEq (← inferType pf) ty do
      throwError "internal error: `{thm}` does not prove{indentExpr ty}"
    for h in explicit.extract (1 + args.size) explicit.size do
      proveMapFlat h.mvarId!
    g.assign (← instantiateMVars pf)

/-- A proof of `Occ₂.AgreeY o o' X oY oY'`, or with indices `IOcc₂.AgreeY o o' X ι oY oY'`, in the
goal `g`, by the lemma of each combinator of `o`; with indices a part in `Y` alone is an occurrence
or a plain leaf at an index, and the plain structure at one index (`IOcc₂.ofOcc₂`) agrees by the
plain agreement and the map at that index (`proveMapFlat`). -/
partial def proveAgreeY (g : MVarId) : MetaM Unit := do
  let ex ← explicitArgs (← instantiateMVars (← g.getType))
  let some o := ex[0]? | throwError "internal error: not an agreement{indentExpr (← g.getType)}"
  if o.isAppOf ``Codata.IOcc₂.ofOcc₂ then
    for g in ← g.apply (← mkConstWithFreshMVarLevels ``Codata.IOcc₂.AgreeY.ofOcc₂) do
      if ← g.isAssigned then continue
      if (← whnfR (← instantiateMVars (← g.getType))).isAppOf ``Codata.Occ₂.AgreeY then
        proveAgreeY g
      else proveMapFlat g
    return
  -- The lemma of the combinator, `Occ₂.AgreeY.c` for `Occ₂.c` (`IOcc₂` alike), with a binder for
  -- those under one.
  let n ← match o.getAppFn.constName? with
    | some ``Codata.IOcc₂.ofY =>
      pure <| match o.appArg!.getAppFn.constName? with
        | some ``Codata.IOcc.hole => ``Codata.IOcc₂.AgreeY.hole
        | some ``Codata.IOcc.ofOcc => ``Codata.IOcc₂.AgreeY.ofOcc
        | _ => ``Codata.IOcc₂.AgreeY.reidx
    | some (.str ns c) =>
      unless (ns == ``Codata.Occ₂ || ns == ``Codata.IOcc₂) &&
          #["ofY", "ofX", "const", "prod", "sum", "comp", "pi", "piP", "sigma"].contains c do
        throwError "internal error: no agreement for the structure{indentExpr o}"
      pure (ns ++ `AgreeY ++ .mkSimple c)
    | _ => throwError "internal error: no agreement for the structure{indentExpr o}"
  let binder := match n with
    | .str _ c => c == "pi" || c == "piP" || c == "sigma"
    | _ => false
  for g in ← g.apply (← mkConstWithFreshMVarLevels n) do
    if ← g.isAssigned then continue
    if binder then proveAgreeY (← g.intro1).2 else proveAgreeY g

/-- Rewrite in the goal `g` every map of the command's functor on an argument with a structure in
two variables, `Occ.map oY oY' f (Occ₂.ofC o z)`, by `Occ₂.AgreeY.map_ofC`; with indices, given
`ι`, `IOcc.map oY oY' f (IOcc₂.ofC o z)` by `IOcc₂.AgreeY.map_ofC`, the index of the presentation
read in the family's along `ι`. The structure `o'` is at the universe `ly'` of the other side, `o`
at `ly`. -/
partial def agreeRewrite (P : Poly) (ι? : Option Expr) (g : MVarId) : MetaM MVarId :=
    g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let isMap (e : Expr) : Bool := match ι? with
    | some _ => e.isAppOfArity ``Codata.IOcc.map 12 && e.appArg!.isAppOfArity ``Codata.IOcc₂.ofC 10
    | none => e.isAppOfArity ``Codata.Occ.map 10 && e.appArg!.isAppOfArity ``Codata.Occ₂.ofC 8
  let some e := tgt.find? isMap | return g
  let ex ← explicitArgs e
  let xa := e.appArg!.getAppArgs
  let (o, X) := if ι?.isSome then (xa[6]!, xa[7]!) else (xa[4]!, xa[5]!)
  let o' := o.instantiateLevelParams [P.fresh[2]!] [P.ly']
  let (agree, mapOfC, args) := match ι? with
    | some ι =>
      (``Codata.IOcc₂.AgreeY, ``Codata.IOcc₂.AgreeY.map_ofC, #[o, o', X, ι, ex[0]!, ex[1]!])
    | none => (``Codata.Occ₂.AgreeY, ``Codata.Occ₂.AgreeY.map_ofC, #[o, o', X, ex[0]!, ex[1]!])
  let h ← mkFreshExprMVar (← mkAppM agree args)
  proveAgreeY h.mvarId!
  let r ← g.rewrite tgt (← mkAppM mapOfC #[← instantiateMVars h])
  agreeRewrite P ι? (← g.replaceTargetEq r.eNew r.eqProof)

/-- `T.Poly.ofL_toL`, `T.Poly.toL_ofL`, `T.Poly.ofL_map`; with indices at an index `i` of the
presentation, `cases` on `a` after `polyCasesIdx`, the positions by `casesPos`, and the indexed
structures of the nested arguments. -/
def genPolyLaws (P : Poly) : TermElabM Unit := do
  let hasLayer (m : Nat) : Bool :=
    P.vc[m]!.ctor.hasNest || !P.fields[m]!.isEmpty || !(P.mixAt m).isEmpty
  withLocalDecl `X .implicit (mkSort P.lx.succ) fun X => do
  withLocalDecl `Y .implicit (← ctx.polyYType P X P.ly) fun Y => do
  ctx.withPolyIdx P fun is => do
  let FXY ← ctx.polyFAt P X Y is P.ly
  let lay ← ctx.polyLayAt P X Y is
  let toL (a : Expr) := ctx.polyAt P "toL" [] (#[X, Y] ++ is |>.push a)
  let ofL (z : Expr) := ctx.polyAt P "ofL" [] (#[X, Y] ++ is |>.push z)
  -- The occurrences of the nested structures: `Y`, with indices `Y` on the packed index; of the
  -- structures in two variables `Y`, with indices on the index of the presentation.
  let hole ← if ctx.idxed then do pure (P.subX P.Hs X (← ctx.packFam Y)) else pure Y
  let Yfam ← if ctx.idxed then ctx.polyLayFam P P.Hs X Y else pure Y
  -- `ofL_toL`: `ofL (toL (F.c ys))` unfolds to `F.c ys'` with `ofC o ⟨(toC o x).1, …⟩` for a
  -- field or a nested argument `x`, which `ofC_toC'` rewrites.
  withLocalDeclD `a FXY fun a => do
    let pf ← proveHere (← mkEq (← ofL (← toL a)) a) fun g => do
      let gas ← if ctx.idxed then ctx.polyCasesIdx g is[0]!.fvarId! a.fvarId!
        else pure #[(g, a.fvarId!)]
      for (g, a) in gas do
      for sg in ← g.cases a do
        let some mr := ctx.ctors.findIdx? fun c => sg.ctorName == some (ctx.fCtor c)
          | throwError "internal error: unexpected case {sg.ctorName}"
        -- The arguments of `F.c`; with indices those `T.F` takes as parameters too.
        let ys ← if !ctx.idxed then pure sg.fields else sg.mvarId.withContext do
          let some (_, _, rhs) := (← instantiateMVars (← sg.mvarId.getType)).eq?
            | throwError "internal error: expected an equation"
          pure (rhs.getAppArgs.extract (ctx.params.size + 1) rhs.getAppNumArgs)
        for (g, m, vs) in ← polyDestructure P mr sg.mvarId ys do
        if !hasLayer m then
          g.refl
          continue
        g.withContext do
        let c := P.vc[m]!.ctor
        let some (_, _, rhs) := (← instantiateMVars (← g.getType)).eq?
          | throwError "internal error: expected an equation"
        let σ := polySubst P c vs X
        -- `ofC o ⟨(toC o y).1, fun q => (toC o y).2 q⟩`, a field by its plain structure.
        let roundTrip (cx : Ctx) (o hole y : Expr) : TermElabM Expr := do
          let t ← cx.occFn `toC o hole #[y]
          cx.mkOfC o hole (← mkAppM ``Sigma.fst #[t]) fun q => do
            return mkApp (← mkAppM ``Sigma.snd #[t]) q
        let trips ← (c.args.zip vs).zipIdx.filterMapM fun ((a, y), k) => do
          if let some f := P.fields[m]!.find? (·.k == k) then
            return some (y, ← roundTrip { ctx with idx := #[] } (σ f.occ) X y)
          if let some f := (P.mixAt m).find? (·.k == k) then
            let o := ctx.mixOccAt f P.ly σ
            let t ← toC₂ o X Yfam y
            let w ← mkAppM ``Sigma.snd #[t]
            return some (y, ← mkOfC₂ o X Yfam (← mkAppM ``Sigma.fst #[t])
              (fun q => do return mkApp (← mkAppM ``Prod.fst #[w]) q)
              (fun q => do return mkApp (← mkAppM ``Prod.snd #[w]) q))
          match a.kind with
          | .nest n => return some (y, ← roundTrip ctx (ctx.nestAt n P.ly σ) hole y)
          | _ => return none
        let lhs := rhs.replaceFVars (trips.map (·.1)) (trips.map (·.2))
        let g ← g.replaceTargetDefEq (← mkEq lhs rhs)
        withUnfolding <| simpOnly g <| if ctx.idxed then
            #[``Codata.Occ.ofC_toC', ``Codata.IOcc.ofC_toC', ``Codata.IOcc₂.ofC_toC']
          else #[``Codata.Occ.ofC_toC', ``Codata.Occ₂.ofC_toC']
    ctx.addPolyThm P "ofL_toL" (P.premises ++ #[X, Y] ++ is |>.push a) (← mkEq (← ofL (← toL a)) a)
      pf
  -- `toL_ofL`: the layers `toC o (ofC o z)` rewritten one by one, then the positions by cases.
  withLocalDeclD `z lay fun z => do
    let pf ← proveHere (← mkEq (← toL (← ofL z)) z) fun g =>
      ctx.polyCasesLay P g z (i? := is[0]?) fun m g => g.withContext do
      let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
        | throwError "internal error: expected an equation"
      let mut g ← g.replaceTargetDefEq (← mkEq (← whnf lhs) rhs)
      let (nestThm, mixThm) := if ctx.idxed then (``Codata.IOcc.toC_ofC, ``Codata.IOcc₂.toC_ofC)
        else (``Codata.Occ.toC_ofC, ``Codata.Occ₂.toC_ofC)
      let thms := (P.vc[m]!.ctor.nests.map fun _ => nestThm) ++
        (P.fields[m]!.map fun _ => ``Codata.Occ.toC_ofC) ++ (P.mixAt m).map fun _ => mixThm
      for thm in thms do
        let r ← g.rewrite (← g.getType) (← mkConstWithFreshMVarLevels thm)
        g ← g.replaceTargetEq r.eNew r.eqProof
      let shape := (← whnf rhs).appFn!.appArg!
      let js ← if ctx.idxed then do pure #[(← whnf (← inferType shape)).appArg!] else pure #[]
      let gs ← Tactic.run g do
        Tactic.evalTactic (← `(tactic|
          refine congrArg (Sigma.mk _) (Prod.ext (funext fun p => ?_) (funext fun b => ?_))))
      for (g', fam) in gs.zip [← ctx.polyP P, ← ctx.polyB P] do
        g'.withContext do
        let p := (← getLCtx).lastDecl.get!.toExpr
        let g' ← g'.replaceLocalDeclDefEq p.fvarId! (mkAppN fam (js.push shape))
        let sgs ← if ctx.idxed then casesPos g' p.fvarId! else g'.cases p.fvarId!
        for sg in sgs do sg.mvarId.refl
    ctx.addPolyThm P "toL_ofL" (P.premises ++ #[X, Y] ++ is |>.push z) (← mkEq (← toL (← ofL z)) z)
      pf
  -- `ofL_map`
  withLocalDecl `Y' .implicit (← ctx.polyYType P X P.ly') fun Y' => do
  let fTy ← if ctx.idxed then do pure (P.subX P.Hs X (← ctx.famFn Y Y')) else mkArrow Y Y'
  withLocalDeclD `f fTy fun f => do
  withLocalDeclD `z lay fun z => do
    -- With indices, `ι`, the index of the presentation read in the family's.
    let (mapped, idx, ι?) ← match (is[0]? : Option Expr) with
      | some i => do
        let fι ← lam `j P.I fun j => do
          return mkAppN f (← ctx.projs (← ctx.polyIota P P.Hs X j))
        pure (← mkAppOptM ``Codata.ILay.map #[← ctx.polySig P, ← ctx.polyP P, X,
            ← ctx.polyLayFam P P.Hs X Y, ← ctx.polyLayFam P P.Hs X Y', fι, i, z],
          ← ctx.projs (← ctx.polyIota P P.Hs X i),
          some (← lam `j P.I fun j => ctx.polyIota P P.Hs X j))
      | none => do pure (← mkAppM ``Codata.Lay.map #[f, z], #[], none)
    let lhs ← ctx.polyAt P "ofL" [(P.fresh[2]!, P.ly')] (#[X, Y'] ++ is |>.push mapped)
    let rhs := mkAppN (← ctx.constWith ctx.Fmap [P.ly, P.ly'])
      (ctx.polyParams P P.Hs X ++ #[Y, Y', f] ++ idx ++ #[← ofL z])
    let stmt ← mkEq lhs rhs
    let pf ← proveHere stmt fun g => ctx.polyCasesLay P g z (i? := is[0]?) fun m g => do
      if !hasLayer m then return ← g.refl
      g.withContext do
      let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
        | throwError "internal error: expected an equation"
      if ctx.idxed then
        -- The map of a split argument pushed through its products and sums to its parts.
        let rhs ← whnf rhs
        let rhs ← if P.vc[m]!.split then
            pure (mkAppN rhs.getAppFn (← rhs.getAppArgs.mapM fun e => pushIMap e))
          else pure rhs
        let g ← g.replaceTargetDefEq (← mkEq (← whnf lhs) rhs)
        withUnfolding do
          -- An argument with a structure in two variables: its map by `IOcc₂.AgreeY.map_ofC`.
          let g ← if (P.mixAt m).isEmpty then pure g else agreeRewrite P ι? g
          if let some g ← simpOnlyStep g
              #[``Codata.ILay.map, ``Codata.Occ.map_ofC, ``Codata.IOcc.map_ofC] then
            g.refl
        return
      let g ← g.replaceTargetDefEq (← mkEq (← whnf lhs) (← whnf rhs))
      -- The map of a split argument goes through its products and sums to its parts.
      let sums := #[``Codata.Occ.map_prod, ``Codata.Occ.map_sum_inl, ``Codata.Occ.map_sum_inr]
      let split := if P.vc[m]!.split then sums ++ #[``Codata.Occ.map_const, ``Codata.Occ.map_hole,
          ``Codata.Occ.map_pi] else #[]
      withUnfolding do
        if (P.mixAt m).isEmpty then
          if let some g ← simpOnlyStep g (#[``Codata.Lay.map, ``Codata.Occ.map_ofC] ++ split) then
            g.refl
          return
        -- With an argument with a structure in two variables: first through the products and
        -- sums of a split argument, then the map of that argument by `AgreeY.map_ofC`.
        let simpOr (g : MVarId) (lemmas : Array Name) : MetaM (Option MVarId) :=
          simpOnlyStep g lemmas (failIfUnchanged := false)
        let some g ← if P.vc[m]!.split then simpOr g sums else pure (some g) | return
        let g ← agreeRewrite P ι? g
        if let some g ← simpOr g (#[``Codata.Lay.map, ``Codata.Occ.map_ofC] ++ split) then
          g.refl
    ctx.addPolyThm P "ofL_map" (P.premises ++ #[X, Y, Y', f] ++ is |>.push z) stmt pf

end Ctx

end Codata.Gen
