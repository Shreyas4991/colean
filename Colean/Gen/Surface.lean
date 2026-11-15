import Colean.Gen.Extras
import Colean.Gen.Pack

/-!
# Generators on `Expr`, step 4: the surface

*Spec.* Input: the constructor list and the declarations of steps 2–3. Output, assembled without
tactic proofs from what exists:

* the constructors `T.cᵢ := T.ctor (T.F.cᵢ …)`, with the default values and tactics of their
  arguments and the declaration ranges of their own syntax, as in `inductive`, and the simp
  lemmas `T.dtor_cᵢ`, `T.ctor_cᵢ`, injectivity `T.cᵢ_inj` (`Codata.inj_of` at `T.F.cᵢ.injEq`)
  and disjointness `T.cᵢ_ne_cⱼ` (`Codata.ne_of`). As in `injEq`, injectivity shares between its
  two sides the arguments that occur in the result index or in the type of an argument occurring
  there, leaves the proofs out of the conjunction, relates an argument by `HEq` where the types
  of the two sides differ (`v : Fin n` with `n` not shared), and is stated when something is
  left; the other arguments are copied with their binder infos, an instance's copy implicit.
  Disjointness is stated where reducible unification finds where the result indices of the two
  constructors meet, with the arguments of one at which they meet those of the other
  (`withMeet`), and not otherwise;
* the case analysis `T.casesOn` (by cases on `F` after `dtor`, cast along `ctor_dtor`; the
  `cases` eliminator, and for `codatatype`, which has no induction, the `induction` one, so that
  `induction` does not unfold the type to its encoding), `T.casesOnAux`, `T.casesOn_ctor` and the
  simp lemmas `T.casesOn_cᵢ`;
* for `datatype`, the computation rules `T.rec_cᵢ` and `T.fold_cᵢ` (simp lemmas), the hypothesis of
  a nested argument given as `fun t _ => T.rec … t` on its members; in a block the rules of the
  block-level recursor and fold are `Blk.rec_cᵢ`, `Blk.fold_cᵢ`, with the block-level names of
  the constructors, and so are those of the block-level `dtor` and `ctor`, `Blk.dtor_cᵢ`,
  `Blk.ctor_cᵢ`;
* in a block, the types `Tₘ params idx := Blk params (.Tₘ idx)` (`genTypes`, before everything
  that mentions them);
* in a block, the interface of a single type for each type, with a family per type of the block
  where the block-level declarations take one family over `Blk.Ix`, as Lean's mutual recursors
  have a motive per type (`genLayers`, `genTypeLambek`, `genTypeCorecs`, `genTypeFolds`):
  `Blk.St`, packing a family per type into one on `Blk.Ix` by cases; the layer
  `Tₘ.F params S₁ … Sₖ idx`, its map `Tₘ.F.map f₁ … fₖ` with the rules `Tₘ.F.map_cᵢ`, and for
  `codatatype` its lifting `Tₘ.F.Rel R₁ … Rₖ`, the block's at the packed families (reducible, so
  patterns and dot notation find the block functor's constructors), with the laws
  `Tₘ.F.map_id`, `Tₘ.F.map_comp` and `Tₘ.F.rel_map`; the destructor `Tₘ.dtor` into the layer at
  the types and the constructor `Tₘ.ctor` out of it, with Lambek's lemma `Tₘ.dtor_ctor`,
  `Tₘ.ctor_dtor`, `Tₘ.ctor_injective` and the rules `Tₘ.dtor_cᵢ`, `Tₘ.ctor_cᵢ`; for `codatatype`,
  `Tₘ.corec c₁ … cₖ`, `Tₘ.dtor_corec`, `Tₘ.corec_eq`, `Tₘ.corec_unique`,
  `Tₘ.bisim R₁ … Rₖ H₁ … Hₖ`; for `datatype`, `Tₘ.fold a₁ … aₖ`, `Tₘ.fold_ctor`, `Tₘ.fold_eq`,
  `Tₘ.fold_unique` and the rules `Tₘ.fold_cᵢ`. All from the block-level ones, which stay; the
  contract stays the block's only. For `codatatype` also the lemmas of `T.F.Rel` of a single type
  (`Gen/Rel.lean`), per type (`genLayerRels`): one step of `Tₘ.F.Rel R₁ … Rₖ` at two
  constructors, `Tₘ.F.rel_cᵢ_cⱼ` (`simp`), `Tₘ.F.Rel.mono` from the block's, `Tₘ.F.rel_refl`;
* equality by the destructor (`genDtorLemmas`): in a block, per type, `Tₘ.dtor_injective` and
  `Tₘ.dtor_inj` (`simp`), as step 3 gives them for a single type; and for every constructor
  `T.dtor_eq_cᵢ_iff : t.dtor = F.cᵢ ys ↔ t = T.cᵢ ys` (`simp`), from `T.dtor_inj` and `T.dtor_cᵢ`;
* for `codatatype`, coinduction up to equality (`genCoinduct`), `T.coinduct R H`, with the step at
  `R x y ∨ x = y`: `T.bisim` at that relation, the step at equal values by `T.F.rel_refl`; in a
  block per type, `Tₘ.coinduct R₁ … Rₖ H₁ … Hₖ`;
* in a `datatype` block, the recursors per type `Tₘ.rec`, in the shape of Lean's mutual inductives
  (a motive per type), as `Blk.rec` at the motive made of them, and their rules `Tₘ.rec_cᵢ`,
  which are the block-level rules by unfolding; a hypothesis by `IPolyIso.Mem` is one per type
  of the argument there. They are not `induction` eliminators, having a motive per type, but
  carry the tag `colean_mutual_rec`, so that plain `induction` refuses the types as it refuses a
  mutual inductive (`MutualCmd.lean`).

The names the user wrote get their info trees, and the types and constructors their doc
comments, once everything is declared (`finishDecls`, `Gen/Command.lean`).

The constructors, their lemmas and `casesOn` are per type, with the types `Tₘ` in their
statements; in a block, `Tₘ.casesOnAux` is by `cases` on a goal metavariable, which discards the
constructors of the other types. `T.F.Rel` is part of the surface too, generated earlier
(`Gen/Rel.lean`).

In a block, the layer at the types, `Tₘ.F params (T₁ params) … (Tₖ params) idx`, is the block's
functor at `Blk.St (T₁ params) …`, a family that is the block's `Blk params` at every
constructor of `Blk.Ix` by definition, but not at a variable index. So `Tₘ.dtor` is the block's
`dtor` followed by the map by the identity `ι` between the two, and `Tₘ.ctor` the block's `ctor`
after the map by the identity `ρ` back (`atTypes`), and the proofs go from one to the other by
cases on the index: the composites of the maps by `ι` and `ρ` are the identity by `F.map_comp`,
`funext` of `rfl` by cases and `F.map_id` (`mapCancel`); `Tₘ.dtor_cᵢ` with `IOcc.map_heq_self`
at a nested argument, `Tₘ.bisim` with `Codata.rel_of_map_heq` (`Framework.lean`), both lemmas
only; `Tₘ.corec_unique` and `Tₘ.fold_unique` are the block's at the morphisms packed by cases,
their hypothesis at each type the per-type one under a map by `ρ` or `ι`. The other rules are
the block's under these maps, or follow from the per-type ones as for a single type. The
packing `Blk.St` at a constructor of `Blk.Ix` is shown as the family it packs there
(`Gen/Pack.lean`).
-/

open Lean Meta Elab Term

namespace Codata.Gen

/-- Which of the arguments `ys` of a constructor its injectivity lemma shares by the two sides,
as Lean's `mkInjectiveTheorems` does: those that occur in the result index arguments `idx`, or
in the type of a local variable occurring there. -/
def sharedArgs (ys idx : Array Expr) : MetaM (Array Bool) := do
  let lctx ← getLCtx
  return ys.map fun y => idx.any (occursOrInType lctx y)

/-- Run `k` on the local variables `ys` with a primed copy of each but those marked `shared`:
the arguments of the other side of an equation, kept or copied, and the copies. A copy has the
binder info of its original, but for an instance, which the equation determines: implicit. -/
def withPrimed (ys : Array Expr) (shared : Array Bool)
    (k : Array Expr → Array Expr → TermElabM α) : TermElabM α := do
  let rec go (i : Nat) (ys' new : Array Expr) : TermElabM α := do
    if h : i < ys.size then
      if shared[i]! then go (i + 1) (ys'.push ys[i]) new else
      let d ← ys[i].fvarId!.getDecl
      let bi := if d.binderInfo.isInstImplicit then .implicit else d.binderInfo
      withLocalDecl (d.userName.appendAfter "'") bi
          (d.type.replaceFVars (ys.extract 0 i) ys') fun y =>
        go (i + 1) (ys'.push y) (new.push y)
    else k ys' new
  go 0 #[] #[]

namespace Ctx

variable (ctx : Ctx)

/-- Run `k` where the results of the constructors `a` and `b` of a type meet: on the arguments
of `a` (as those of `T.a`), and those of `b` at which its result index unifies with that of `a`,
by reducible unification with a metavariable for each argument of `b`. The arguments left
unassigned are new local variables, primed. `k` receives the arguments of `a` and of `b`, the
new variables and the family-level index arguments of `a`. Nothing is run when the indices do
not unify. -/
def withMeet (a b : Ctor)
    (k : Array Expr → Array Expr → Array Expr → Array Expr → TermElabM α) :
    TermElabM (Option α) := do
  let tel ← ctx.withTArgs b (rename := (·.appendAfter "'")) fun zs σ => do
    mkForallFVars zs (← ctx.tyAt b.owner (b.uidx.map σ))
  let names := tel.getForallBinderNames.toArray
  ctx.withTArgs a fun ys σ => do
  let (ms, bis, tyB) ← forallMetaTelescope tel
  let idxB := tyB.getAppArgs.extract ctx.params.size tyB.getAppNumArgs
  let meet ← withReducible <| ((a.uidx.map σ).zip idxB).allM fun (i, j) => isDefEq i j
  unless meet do return none
  -- The metavariables left unassigned become local variables, in order. An argument that
  -- needs a later one is not supported.
  let rec go (i : Nat) (sub : Array (Expr × Expr)) (args new : Array Expr) :
      TermElabM (Option α) := do
    let rep (e : Expr) : MetaM (Option Expr) := do
      let e := (← instantiateMVars e).replace fun x => (sub.find? (·.1 == x)).map (·.2)
      return if e.hasExprMVar then none else some e
    if h : i < ms.size then
      let m := ms[i]
      if ← m.mvarId!.isAssigned then
        let some v ← rep m | return none
        go (i + 1) sub (args.push v) new
      else
        let some ty ← rep (← inferType m) | return none
        withLocalDecl names[i]! bis[i]! ty fun x =>
          go (i + 1) (sub.push (m, x)) (args.push x) (new.push x)
    else some <$> k ys args new (a.idx.map σ)
  go 0 #[] #[] #[]

/-! ### Blocks: the layer per type -/

/-- In a block, the type that the block index `i` is at, with its index arguments: `(k, idx)`
when `i` reduces to `Blk.Ix.Tₖ params idx`. A nested argument's positions have their index
computed from the layer, so it is reduced first. -/
def typeAt? (i : Expr) : MetaM (Option (Nat × Array Expr)) := do
  let i ← whnf i
  let some k := ctx.ixCtors.findIdx? (i.getAppFn.isConstOf ·.getAppFn.constName!)
    | return none
  return some (k, i.getAppArgs.extract ctx.params.size i.getAppNumArgs)

/-- In a block, `Blk.Ix params`, with the name and the universes of `Blk.Ix`. -/
def ixType : MetaM (Expr × Name × List Level) := do
  let ixTy ← inferType ctx.idx[0]!
  let .const ix us := ixTy.getAppFn | throwError "internal error: no block index"
  return (ixTy, ix, us)

/-- Run `k` on copies of the index binders of the `m`-th type, with their names, bound with
`bi`. -/
def withTyIdx (m : Nat) (bi : BinderInfo) (k : Array Expr → TermElabM α) : TermElabM α := do
  let idx := ctx.types[m]!.idx
  withCopies idx (← idx.mapM (·.fvarId!.getUserName)) bi k

/-- In a block, a function on its index by cases at the index `i`:
`Blk.Ix.casesOn (motive := motive) i minors`, the minor premise of the `m`-th type `minor m idx`
on copies `idx` of its index binders. -/
def ixCasesAt (motive : Expr → TermElabM Expr) (minor : Nat → Array Expr → TermElabM Expr)
    (i : Expr) : TermElabM Expr := do
  let (ixTy, ix, us) ← ctx.ixType
  let M ← lam `i ixTy motive
  let lvl ← withLocalDeclD `i ixTy fun i => do return (← getLevel (← motive i)).normalize
  let minors ← (Array.range ctx.types.size).mapM fun m => ctx.withTyIdx m .default fun uidx => do
    mkLambdaFVars uidx (← minor m uidx)
  return mkAppN (.const (mkCasesOnName ix) (lvl :: us)) (ixTy.getAppArgs ++ #[M, i] ++ minors)

/-- The block's index `Blk.Ix.Tₘ params idx` of the `m`-th type. -/
def ixAt (m : Nat) (idx : Array Expr) : Expr := mkAppN ctx.ixCtors[m]! idx

/-- `fun i => Blk.Ix.casesOn (motive := motive) i minors` (`ixCasesAt`): one function on the
block's index made of one per type. -/
def ixCases (motive : Expr → TermElabM Expr) (minor : Nat → Array Expr → TermElabM Expr) :
    TermElabM Expr := do
  lam `i (← ctx.ixType).1 fun i => ctx.ixCasesAt motive minor i

/-- Run `k` on local variables `x₁ : ty 0`, `x₂ : ty 1`, …, one per type of the block, named
`base₁`, `base₂`, … (`userName`). -/
def withPerType (base : String) (bi : BinderInfo) (ty : Nat → TermElabM Expr)
    (k : Array Expr → TermElabM α) : TermElabM α := do
  let rec go (j : Nat) (acc : Array Expr) : TermElabM α := do
    if j < ctx.types.size then
      let n ← ctx.userName (Name.mkSimple s!"{base}{Nat.toSubscriptString (j + 1)}")
      withLocalDecl n bi (← ty j) fun x => go (j + 1) (acc.push x)
    else k acc
  termination_by ctx.types.size - j
  go 0 #[]

/-- The family variable of the `j`-th type at universe `w`: `∀ idx, Type w`, or `Type w`. -/
def tyFamType (j : Nat) (w : Level) : TermElabM Expr :=
  ctx.withTyIdx j .default fun js => mkForallFVars js (mkSort w.succ)

/-- `∀ idx, X idx → Y idx`, or `X → Y`, on the indices of the `j`-th type. -/
def tyFnType (j : Nat) (X Y : Expr) : TermElabM Expr :=
  ctx.withTyIdx j .default fun js => do mkForallFVars js (← mkArrow (mkAppN X js) (mkAppN Y js))

/-- `∀ idx, X idx → Y idx → Prop`, on the indices of the `j`-th type. -/
def tyRelType (j : Nat) (X Y : Expr) : TermElabM Expr :=
  ctx.withTyIdx j .default fun js => do
    mkForallFVars js (← mkArrow (mkAppN X js) (← mkArrow (mkAppN Y js) (mkSort .zero)))

/-- The names of the declarations per type of a `codatatype` block: `Blk.St`, `Tₘ.F`, `Tₘ.F.map`,
`Tₘ.F.Rel`. -/
def stN : Name := ctx.gen "St"
def layerN (m : Nat) : Name := ctx.tyGenP m "F"
def layerMapN (m : Nat) : Name := .str (ctx.layerN m) "map"
def layerRelN (m : Nat) : Name := .str (ctx.layerN m) "Rel"

/-- `Blk.St params S₁ … Sₖ`, the families of the types packed into one family on `Blk.Ix`, at
universe `w`. -/
def stAt (w : Level) (Ss : Array Expr) : MetaM Expr := ctx.genAt ctx.stN [w] Ss

/-- `Tₘ.F params S₁ … Sₖ idx`, at universe `w`. -/
def layerAt (m : Nat) (w : Level) (Ss idx : Array Expr) : MetaM Expr :=
  ctx.genAt (ctx.layerN m) [w] (Ss ++ idx)

/-- The types of a block as families, `Tⱼ params`. -/
def tyFams : MetaM (Array Expr) :=
  (Array.range ctx.types.size).mapM fun j => do
    return mkAppN (← ctx.constWith (ctx.tyName j) []) ctx.params

/-- `fun i x => x`, on the family `X` over `Blk.Ix`. -/
def idFn (X : Expr) : TermElabM Expr := do
  lam `i (← ctx.ixType).1 fun i => lam `x (mkApp X i).headBeta pure

/-- `fun i x => g i (f i x)`, for `f` on the family `X` over `Blk.Ix`. -/
def compFn (X g f : Expr) : TermElabM Expr := do
  lam `i (← ctx.ixType).1 fun i => lam `x (mkApp X i).headBeta fun x => do
    return (mkApp2 g i (mkApp2 f i x).headBeta).headBeta

/-- `lhs = rhs` for two functions on `Blk.Ix` that agree at every constructor of `Blk.Ix` by
definition: `funext` of `Eq.refl` by cases on the index. -/
def funextCases (lhs rhs : Expr) : TermElabM Expr := do
  let h ← ctx.ixCases (fun i => mkEq (mkApp lhs i).headBeta (mkApp rhs i).headBeta)
    fun j uidx => mkEqRefl (mkApp lhs (ctx.ixAt j uidx)).headBeta
  mkAppOptM ``funext #[none, none, lhs, rhs, h]

/-- `Blk.F.map φ₁ a = Blk.F.map φ₂ a` from `h : φ₁ = φ₂`, for `a : Blk.F X idx` and
`φᵢ : ∀ i, X i → Y i`. -/
def mapCongr (wX wY : Level) (X Y h : Expr) (idx : Array Expr) (a : Expr) : TermElabM Expr := do
  let some (φTy, _, _) := (← inferType h).eq? | throwError "internal error: not an equation"
  let mapφ ← lam `φ φTy fun φ => ctx.mapAt wX wY X Y φ idx a
  mkCongrArg mapφ h

/-- `Blk.F.map g (Blk.F.map f a) = a`, for `a : Blk.F X idx`, `f : ∀ i, X i → Y i` and
`g : ∀ i, Y i → X i` at universe `w`, from `hgf : (fun i x => g i (f i x)) = fun i x => x`. -/
def mapCancel (w : Level) (X Y f g hgf : Expr) (idx : Array Expr) (a : Expr) :
    TermElabM Expr := do
  let e₁ ← mkEqSymm (← ctx.genAt ctx.Fmap_comp [w, w, w] (#[X, Y, X, g, f] ++ idx ++ #[a]))
  let e₂ ← ctx.mapCongr w w X X hgf idx a
  let e₃ ← ctx.genAt ctx.Fmap_id [w] (#[X] ++ idx ++ #[a])
  mkEqTrans e₁ (← mkEqTrans e₂ e₃)

/-- The layer per type at the types themselves: the family `Blk.St params (T₁ params) …`, the
identities `ι : ∀ i, Blk params i → Blk.St … i` and `ρ` back, by cases on `i`,
`hT : Blk params = Blk.St …`, `hι : ∀ i x, HEq (ι i x) x`, and the two composites the identity,
`hρι : (fun i x => ρ i (ι i x)) = fun i x => x` and `hιρ`. The two families agree at every
constructor of `Blk.Ix` by definition, but not at a variable, so a map by `ι` or `ρ` stands
between them. -/
structure AtTypes where
  StT : Expr
  ι : Expr
  ρ : Expr
  hT : Expr
  hι : Expr
  hρι : Expr
  hιρ : Expr

def atTypes : TermElabM AtTypes := do
  let L ← ctx.tLvl
  let T ← ctx.tFam
  let StT ← ctx.stAt L (← ctx.tyFams)
  let idAt (X Y : Expr) := ctx.ixCases (fun i => mkArrow (mkApp X i) (mkApp Y i))
    fun j uidx => do lam `x (← ctx.tyAt j uidx) pure
  let ι ← idAt T StT
  let ρ ← idAt StT T
  let hpt ← ctx.ixCases (fun i => mkEq (mkApp T i) (mkApp StT i))
    fun j uidx => do mkEqRefl (← ctx.tyAt j uidx)
  let hT ← mkAppOptM ``funext #[none, none, T, StT, hpt]
  let hι ← ctx.ixCases (fun i => do
      withLocalDeclD `x (mkApp T i) fun x => do
        mkForallFVars #[x] (← mkHEq (mkApp2 ι i x).headBeta x))
    fun j uidx => do lam `x (← ctx.tyAt j uidx) fun x => mkHEqRefl x
  let hρι ← ctx.funextCases (← ctx.compFn T ρ ι) (← ctx.idFn T)
  let hιρ ← ctx.funextCases (← ctx.compFn StT ι ρ) (← ctx.idFn StT)
  return { StT, ι, ρ, hT, hι, hρι, hιρ }

/-- The arguments of `F.c` after `Tₘ.F.map f₁ … fₖ`, for the arguments `ys` of `c` with the
occurrences at the families `Xs` (local variables, or the types `Tⱼ params`): data unchanged,
`fⱼ idx y` for a recursive argument of the `j`-th type, under its telescope for a function, and
for a nested one the map of its structure by the packed function `packF`. -/
def layerMapped (c : Ctor) (ys : Array Expr) (σ : Expr → Expr) (Xs fs : Array Expr)
    (wX wY : Level) (packF : Expr) : TermElabM (Array Expr) :=
  (c.args.zip ys).mapM fun (a, y) => do
    match a.kind with
    | .data => pure y
    | .plain idx =>
      let some (j, uidx) ← ctx.typeAt? (σ idx[0]!)
        | throwError "internal error: a recursive argument at no type of the block"
      return (mkAppN fs[j]! (uidx.push y)).headBeta
    | .fn n => withReducible <| forallBoundedTelescope (← inferType y) n fun zs body => do
      let body ← whnfOcc body
      let some j := Xs.findIdx? (·.getAppFn == body.getAppFn)
        | throwError "internal error: a function into no type of the block"
      let idx := body.getAppArgs.extract Xs[j]!.getAppNumArgs body.getAppNumArgs
      mkLambdaFVars zs (mkAppN fs[j]! (idx.push (mkAppN y zs))).headBeta
    | .nest o => mkAppM ``Codata.IOcc.map #[ctx.nestAt o wX σ, ctx.nestAt o wY σ, packF, y]

/-- The laws of the layer per type, as those of `T.F` for a single type: `Tₘ.F.map_id`,
`Tₘ.F.map_comp`, and for `codatatype` `Tₘ.F.rel_map`. Each is the block's law at the packed
functions, the packed identities or composites equal to the identity or composite of the packed
ones by cases on the index (`funextCases`). -/
def genLayerLaws : TermElabM Unit := do
  let ref (m : Nat) := ctx.types[m]!.ref
  let n := ctx.types.size
  -- `fun idx x => g idx (f idx x)` on the indices of the `j`-th type, `g ∘ f` without.
  let comp (j : Nat) (X g f : Expr) : TermElabM Expr := ctx.withTyIdx j .default fun js => do
    if js.isEmpty then mkAppM ``Function.comp #[g, f] else
    withLocalDeclD `x (mkAppN X js) fun x => do
      mkLambdaFVars (js.push x) (mkAppN g (js.push (mkAppN f (js.push x))))
  let pack (St₁ St₂ : Expr) (fs : Array Expr) : TermElabM Expr :=
    ctx.ixCases (fun i => mkArrow (mkApp St₁ i) (mkApp St₂ i))
      fun j uidx => pure (mkAppN fs[j]! uidx).headBeta
  -- `Tₘ.F.map_id`
  do
    let fresh := ctx.freshLevels 1
    let w := ctx.holeLevel (.param fresh[0]!)
    ctx.withPerType "X" .implicit (ctx.tyFamType · w) fun Xs => do
    let StX ← ctx.stAt w Xs
    let ids ← (Array.range n).mapM fun j => ctx.withTyIdx j .default fun js => do
      if js.isEmpty then mkAppOptM ``id #[Xs[j]!] else
      withLocalDeclD `x (mkAppN Xs[j]! js) fun x => mkLambdaFVars (js.push x) x
    let h ← ctx.funextCases (← pack StX StX ids) (← ctx.idFn StX)
    for m in [0:n] do
      ctx.withTyIdx m .implicit fun uidx => do
      let ixT := ctx.wrap m uidx
      withLocalDeclD `a (← ctx.layerAt m w Xs uidx) fun a => do
      let lhs ← ctx.genAt (ctx.layerMapN m) [w, w] (Xs ++ Xs ++ ids ++ uidx ++ #[a])
      let value ← mkEqTrans (← ctx.mapCongr w w StX StX h ixT a)
        (← ctx.genAt ctx.Fmap_id [w] (#[StX] ++ ixT ++ #[a]))
      let xs := ctx.params ++ Xs ++ uidx ++ #[a]
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs (← mkEq lhs a), ← mkLambdaFVars xs value)
      addThm (.str (ctx.layerN m) "map_id") (← ctx.levelParamsOf fresh #[type]) type value (ref m)
  -- `Tₘ.F.map_comp` and `Tₘ.F.rel_map`
  let fresh := ctx.freshLevels 3
  let [wX, wY, wZ] := fresh.map fun u => ctx.holeLevel (.param u) | unreachable!
  ctx.withPerType "X" .implicit (ctx.tyFamType · wX) fun Xs => do
  ctx.withPerType "Y" .implicit (ctx.tyFamType · wY) fun Ys => do
  ctx.withPerType "Z" .implicit (ctx.tyFamType · wZ) fun Zs => do
  let (StX, StY, StZ) := (← ctx.stAt wX Xs, ← ctx.stAt wY Ys, ← ctx.stAt wZ Zs)
  do
    ctx.withPerType "g" .default (fun j => ctx.tyFnType j Ys[j]! Zs[j]!) fun gs => do
    ctx.withPerType "f" .default (fun j => ctx.tyFnType j Xs[j]! Ys[j]!) fun fs => do
    let gfs ← (Array.range n).mapM fun j => comp j Xs[j]! gs[j]! fs[j]!
    let (packG, packF) := (← pack StY StZ gs, ← pack StX StY fs)
    let h ← ctx.funextCases (← pack StX StZ gfs) (← ctx.compFn StX packG packF)
    for m in [0:n] do
      ctx.withTyIdx m .implicit fun uidx => do
      let ixT := ctx.wrap m uidx
      withLocalDeclD `a (← ctx.layerAt m wX Xs uidx) fun a => do
      let lhs ← ctx.genAt (ctx.layerMapN m) [wX, wZ] (Xs ++ Zs ++ gfs ++ uidx ++ #[a])
      let rhs ← ctx.genAt (ctx.layerMapN m) [wY, wZ] (Ys ++ Zs ++ gs ++ uidx ++
        #[← ctx.genAt (ctx.layerMapN m) [wX, wY] (Xs ++ Ys ++ fs ++ uidx ++ #[a])])
      let value ← mkEqTrans (← ctx.mapCongr wX wZ StX StZ h ixT a)
        (← ctx.genAt ctx.Fmap_comp [wX, wY, wZ] (#[StX, StY, StZ, packG, packF] ++ ixT ++ #[a]))
      let xs := ctx.params ++ Xs ++ Ys ++ Zs ++ gs ++ fs ++ uidx ++ #[a]
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs (← mkEq lhs rhs), ← mkLambdaFVars xs value)
      addThm (.str (ctx.layerN m) "map_comp") (← ctx.levelParamsOf fresh #[type]) type value
        (ref m)
  unless ctx.co do return
  ctx.withPerType "R" .default (fun j => ctx.tyRelType j Ys[j]! Zs[j]!) fun Rs => do
  ctx.withPerType "f" .default (fun j => ctx.tyFnType j Xs[j]! Ys[j]!) fun fs => do
  ctx.withPerType "g" .default (fun j => ctx.tyFnType j Xs[j]! Zs[j]!) fun gs => do
  let packR ← ctx.ixCases
    (fun i => do mkArrow (mkApp StY i) (← mkArrow (mkApp StZ i) (mkSort .zero)))
    fun j uidx => pure (mkAppN Rs[j]! uidx)
  let (packF, packG) := (← pack StX StY fs, ← pack StX StZ gs)
  for m in [0:n] do
    ctx.withTyIdx m .implicit fun uidx => do
    let ixT := ctx.wrap m uidx
    withLocalDeclD `a (← ctx.layerAt m wX Xs uidx) fun a => do
    ctx.withPerType "h" .default (fun j => ctx.withTyIdx j .default fun js => do
        withLocalDeclD `x (mkAppN Xs[j]! js) fun x => do
        mkForallFVars (js.push x) (mkAppN Rs[j]! (js ++ #[mkAppN fs[j]! (js.push x),
          mkAppN gs[j]! (js.push x)]))) fun hs => do
    let packH ← ctx.ixCases (fun i => do
        withLocalDeclD `x (mkApp StX i) fun x => do
        mkForallFVars #[x] (mkApp3 packR i (mkApp2 packF i x).headBeta
          (mkApp2 packG i x).headBeta).headBeta)
      fun j uidx => pure (mkAppN hs[j]! uidx)
    let stmt ← ctx.genAt (ctx.layerRelN m) [wY, wZ] (Ys ++ Zs ++ Rs ++ uidx ++
      #[← ctx.genAt (ctx.layerMapN m) [wX, wY] (Xs ++ Ys ++ fs ++ uidx ++ #[a]),
        ← ctx.genAt (ctx.layerMapN m) [wX, wZ] (Xs ++ Zs ++ gs ++ uidx ++ #[a])])
    let value ← ctx.genAt ctx.Frel_map [wX, wY, wZ]
      (#[StX, StY, StZ, packR, packF, packG] ++ ixT ++ #[a, packH])
    let xs := ctx.params ++ Xs ++ Ys ++ Zs ++ Rs ++ fs ++ gs ++ uidx ++ #[a] ++ hs
    let (type, value) ← withBinderInfo ctx.params .implicit do
      return (← mkForallFVars xs stmt, ← mkLambdaFVars xs value)
    addThm (.str (ctx.layerN m) "rel_map") (← ctx.levelParamsOf fresh #[type]) type value (ref m)

/-- In a block, the layer per type: `Blk.St`, which packs one family per type into one on
`Blk.Ix` by cases, the layer of each type at a family per type `Tₘ.F params S₁ … Sₖ idx` (the
block's functor at the packed family, at the type's constructor of `Blk.Ix`), its map `Tₘ.F.map`
with one function per type and the rules `Tₘ.F.map_cᵢ`, and for `codatatype` its lifting to
relations `Tₘ.F.Rel` with one relation per type, all reducible; the laws `Tₘ.F.map_id`,
`Tₘ.F.map_comp` and for `codatatype` `Tₘ.F.rel_map`, the block's at the packed functions, equal to
the packed composites by cases on the index; and the destructor and the constructor per type,
`Tₘ.dtor` into the layer at the types and `Tₘ.ctor` out of it, the block's followed or preceded
by the map by the identity `ι` or `ρ` (`atTypes`). -/
def genLayers : TermElabM Unit := do
  unless ctx.isBlock do return
  let (ixTy, _, _) ← ctx.ixType
  let ref (m : Nat) := ctx.types[m]!.ref
  -- `Blk.St`
  do
    let fresh := ctx.freshLevels 1
    let w := ctx.holeLevel (.param fresh[0]!)
    ctx.withPerType "S" .default (ctx.tyFamType · w) fun Ss => do
    withLocalDeclD `i ixTy fun i => do
    let value ← ctx.ixCasesAt (fun _ => pure (mkSort w.succ))
      (fun j uidx => pure (mkAppN Ss[j]! uidx)) i
    let xs := ctx.params ++ Ss ++ #[i]
    let (type, value) ← withBinderInfo ctx.params .implicit do
      return (← mkForallFVars xs (mkSort w.succ), ← mkLambdaFVars xs value)
    addDef ctx.stN (← ctx.levelParamsOf fresh #[type, value]) type value ctx.ref (reducible := true)
    packAttr.setTag ctx.stN
  -- `Tₘ.F`
  do
    let fresh := ctx.freshLevels 1
    let w := ctx.holeLevel (.param fresh[0]!)
    ctx.withPerType "S" .default (ctx.tyFamType · w) fun Ss => do
    let St ← ctx.stAt w Ss
    for m in [0:ctx.types.size] do
      ctx.withTyIdx m .default fun uidx => do
      let body ← ctx.fAt w St (ctx.wrap m uidx)
      let xs := ctx.params ++ Ss ++ uidx
      let value ← mkLambdaFVars xs body
      let type ← mkForallFVars xs (← inferType body)
      addDef (ctx.layerN m) (← ctx.levelParamsOf fresh #[type, value]) type value (ref m)
        (reducible := true)
  -- `Tₘ.F.map`, `Tₘ.F.map_cᵢ`, `Tₘ.F.Rel`
  do
    let fresh := ctx.freshLevels 2
    let [wX, wY] := fresh.map fun u => ctx.holeLevel (.param u) | unreachable!
    ctx.withPerType "X" .implicit (ctx.tyFamType · wX) fun Xs => do
    ctx.withPerType "Y" .implicit (ctx.tyFamType · wY) fun Ys => do
    let (StX, StY) := (← ctx.stAt wX Xs, ← ctx.stAt wY Ys)
    -- `Tₘ.F.map`
    ctx.withPerType "f" .default (fun j => ctx.tyFnType j Xs[j]! Ys[j]!) fun fs => do
    let packF ← ctx.ixCases (fun i => mkArrow (mkApp StX i) (mkApp StY i))
      fun j uidx => pure (mkAppN fs[j]! uidx)
    for m in [0:ctx.types.size] do
      ctx.withTyIdx m .implicit fun uidx => do
      withLocalDeclD `a (← ctx.layerAt m wX Xs uidx) fun a => do
      let value ← ctx.mapAt wX wY StX StY packF (ctx.wrap m uidx) a
      let xs := ctx.params ++ Xs ++ Ys ++ fs ++ uidx ++ #[a]
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs (← ctx.layerAt m wY Ys uidx), ← mkLambdaFVars xs value)
      addDef (ctx.layerMapN m) (← ctx.levelParamsOf fresh #[type, value]) type value (ref m)
        (reducible := true)
    -- `Tₘ.F.map_cᵢ`, by definition.
    for c in ctx.ctors do
      ctx.withArgsAtU c (fun j idx => mkAppN Xs[j]! idx) wX (post := ctx.foldTy) fun ys σ => do
      let m := c.owner
      let lhs ← ctx.genAt (ctx.layerMapN m) [wX, wY]
        (Xs ++ Ys ++ fs ++ c.uidx.map σ ++ #[← ctx.fCtorApp c wX StX ys])
      let rhs ← ctx.fCtorApp c wY StY (← ctx.layerMapped c ys σ Xs fs wX wY packF)
      let xs := ctx.params ++ Xs ++ Ys ++ fs ++ ys
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs (← mkEq lhs rhs), ← mkLambdaFVars xs (← mkEqRefl lhs))
      let n := Name.str (ctx.layerN m) ("map_" ++ c.name.toString)
      addThm n (← ctx.levelParamsOf fresh #[type]) type value (ref m)
      addSimp n
    -- `Tₘ.F.Rel`
    unless ctx.co do return
    ctx.withPerType "R" .default (fun j => ctx.tyRelType j Xs[j]! Ys[j]!) fun Rs => do
    let packR ← ctx.ixCases
      (fun i => do mkArrow (mkApp StX i) (← mkArrow (mkApp StY i) (mkSort .zero)))
      fun j uidx => pure (mkAppN Rs[j]! uidx)
    for m in [0:ctx.types.size] do
      ctx.withTyIdx m .implicit fun uidx => do
      withLocalDeclD `a (← ctx.layerAt m wX Xs uidx) fun a => do
      withLocalDeclD `b (← ctx.layerAt m wY Ys uidx) fun b => do
      let value ← ctx.relAt wX wY StX StY packR (ctx.wrap m uidx) a b
      let xs := ctx.params ++ Xs ++ Ys ++ Rs ++ uidx ++ #[a, b]
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs (mkSort .zero), ← mkLambdaFVars xs value)
      addDef (ctx.layerRelN m) (← ctx.levelParamsOf fresh #[type, value]) type value (ref m)
        (reducible := true)
  ctx.genLayerLaws
  -- `Tₘ.dtor` and `Tₘ.ctor`
  let L ← ctx.tLvl
  let T ← ctx.tFam
  let Ts ← ctx.tyFams
  let ats ← ctx.atTypes
  for m in [0:ctx.types.size] do
    ctx.withTyIdx m .implicit fun uidx => do
    let ixT := ctx.wrap m uidx
    let (Tm, FT) := (← ctx.tyAt m uidx, ← ctx.layerAt m L Ts uidx)
    withLocalDeclD `t Tm fun t => do
      let value ← ctx.mapAt L L T ats.StT ats.ι ixT (← ctx.appAt ctx.dtor ixT #[t])
      let xs := ctx.params ++ uidx ++ #[t]
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs FT, ← mkLambdaFVars xs value)
      addDef (ctx.tyGenP m "dtor") (← ctx.levelParamsOf [] #[type, value]) type value (ref m)
    withLocalDeclD `y FT fun y => do
      let value ← ctx.appAt ctx.ctor ixT #[← ctx.mapAt L L ats.StT T ats.ρ ixT y]
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars (ctx.params ++ uidx) (← mkArrow FT Tm),
          ← mkLambdaFVars (ctx.params ++ uidx ++ #[y]) value)
      addDef (ctx.tyGenP m "ctor") (← ctx.levelParamsOf [] #[type, value]) type value (ref m)

/-- In a `codatatype` block, per type, the lemmas of `T.F.Rel` for a single type (`Gen/Rel.lean`):
the one-step lemmas of `Tₘ.F.Rel R₁ … Rₖ` (`RelStep`), `simp`, the premise at a recursive argument
at the relation of its type, at a nested one the block's at the relations packed by cases;
`Tₘ.F.Rel.mono`, the block's `T.F.Rel.mono` at the relations and the hypotheses packed by cases;
and `Tₘ.F.rel_refl`, `Tₘ.F.rel_map` at the identities, rewritten by `Tₘ.F.map_id`. -/
def genLayerRels : TermElabM Unit := do
  unless ctx.co && ctx.isBlock do return
  let n := ctx.types.size
  let free (nm : Name) : MetaM Bool := return !(← getEnv).contains nm
  -- The one-step lemmas.
  do
    let fresh := ctx.freshLevels 2
    let [wX, wY] := fresh.map fun u => ctx.holeLevel (.param u) | unreachable!
    ctx.withPerType "X" .implicit (ctx.tyFamType · wX) fun Xs => do
    ctx.withPerType "Y" .implicit (ctx.tyFamType · wY) fun Ys => do
    ctx.withPerType "R" .implicit (fun j => ctx.tyRelType j Xs[j]! Ys[j]!) fun Rs => do
    let (StX, StY) := (← ctx.stAt wX Xs, ← ctx.stAt wY Ys)
    let packR ← ctx.ixCases
      (fun i => do mkArrow (mkApp StX i) (← mkArrow (mkApp StY i) (mkSort .zero)))
      fun j uidx => pure (mkAppN Rs[j]! uidx)
    let premise (a : ArgInfo) (σ : Expr → Expr) (y y' : Expr) : TermElabM Expr := do
      match a.kind with
      | .plain idx =>
        let some (j, uidx) ← ctx.typeAt? (σ idx[0]!)
          | throwError "internal error: a recursive argument at no type of the block"
        return mkAppN Rs[j]! (uidx ++ #[y, y'])
      | .fn k => withReducible <| forallBoundedTelescope (← inferType y) k fun zs body => do
        let body ← whnfOcc body
        let some j := Xs.findIdx? (·.getAppFn == body.getAppFn)
          | throwError "internal error: a function into no type of the block"
        let idx := body.getAppArgs.extract Xs[j]!.getAppNumArgs body.getAppNumArgs
        mkForallFVars zs (mkAppN Rs[j]! (idx ++ #[mkAppN y zs, mkAppN y' zs]))
      | .nest o => mkAppM ``Codata.IOcc.Rel #[ctx.nestAt o wX σ, ctx.nestAt o wY σ, packR, y, y']
      | .data => throwError "internal error: a premise at a data argument"
    for m in [0:n] do
      ctx.genRelSteps {
        vars := Xs ++ Ys ++ Rs, repX := fun j idx => mkAppN Xs[j]! idx
        repY := fun j idx => mkAppN Ys[j]! idx, wX, wY, famX := StX, famY := StY
        rel := fun uidx a b =>
          ctx.genAt (ctx.layerRelN m) [wX, wY] (Xs ++ Ys ++ Rs ++ uidx ++ #[a, b])
        premise, idxOf := fun c σ => c.uidx.map σ
        name := fun c c' => .str (ctx.layerN m) s!"rel_{c.name}_{c'.name}"
        ctors := ctx.ctors.filter (·.owner == m), fresh, ref := ctx.types[m]!.ref
        post := ctx.foldTy }
  -- `Tₘ.F.Rel.mono`
  if (← getEnv).contains ctx.relMonoN then
    let fresh := ctx.freshLevels 2
    let [wX, wY] := fresh.map fun u => ctx.holeLevel (.param u) | unreachable!
    ctx.withPerType "X" .implicit (ctx.tyFamType · wX) fun Xs => do
    ctx.withPerType "Y" .implicit (ctx.tyFamType · wY) fun Ys => do
    ctx.withPerType "R" .implicit (fun j => ctx.tyRelType j Xs[j]! Ys[j]!) fun Rs => do
    ctx.withPerType "S" .implicit (fun j => ctx.tyRelType j Xs[j]! Ys[j]!) fun Ss => do
    ctx.withPerType "h" .default (fun j => ctx.withTyIdx j .default fun js => do
        withLocalDeclD `x (mkAppN Xs[j]! js) fun x => do
        withLocalDeclD `y (mkAppN Ys[j]! js) fun y => do
        mkForallFVars (js ++ #[x, y])
          (← mkArrow (mkAppN Rs[j]! (js ++ #[x, y])) (mkAppN Ss[j]! (js ++ #[x, y])))) fun hs => do
    let (StX, StY) := (← ctx.stAt wX Xs, ← ctx.stAt wY Ys)
    let pack (Rs : Array Expr) := ctx.ixCases
      (fun i => do mkArrow (mkApp StX i) (← mkArrow (mkApp StY i) (mkSort .zero)))
      fun j uidx => pure (mkAppN Rs[j]! uidx)
    let (packR, packS) := (← pack Rs, ← pack Ss)
    let packH ← ctx.ixCases (fun i => do
        withLocalDeclD `x (mkApp StX i) fun x => withLocalDeclD `y (mkApp StY i) fun y => do
        mkForallFVars #[x, y]
          (← mkArrow (mkApp3 packR i x y).headBeta (mkApp3 packS i x y).headBeta))
      fun j uidx => pure (mkAppN hs[j]! uidx)
    for m in [0:n] do
      let nm := .str (ctx.layerRelN m) "mono"
      unless ← free nm do continue
      ctx.withTyIdx m .implicit fun uidx => do
      withLocalDecl `a .implicit (← ctx.layerAt m wX Xs uidx) fun a => do
      withLocalDecl `b .implicit (← ctx.layerAt m wY Ys uidx) fun b => do
      let rel ← ctx.genAt (ctx.layerRelN m) [wX, wY] (Xs ++ Ys ++ Rs ++ uidx ++ #[a, b])
      withLocalDeclD `hab rel fun hab => do
      let stmt ← ctx.genAt (ctx.layerRelN m) [wX, wY] (Xs ++ Ys ++ Ss ++ uidx ++ #[a, b])
      let value ← ctx.genAt ctx.relMonoN [wX, wY]
        #[StX, StY, packR, packS, packH, ctx.ixAt m uidx, a, b, hab]
      let xs := ctx.params ++ Xs ++ Ys ++ Rs ++ Ss ++ hs ++ uidx ++ #[a, b, hab]
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs stmt, ← mkLambdaFVars xs value)
      addThm nm (← ctx.levelParamsOf fresh #[type]) type value ctx.types[m]!.ref
  -- `Tₘ.F.rel_refl`
  let fresh := ctx.freshLevels 1
  let w := ctx.holeLevel (.param fresh[0]!)
  ctx.withPerType "X" .implicit (ctx.tyFamType · w) fun Xs => do
  ctx.withPerType "R" .implicit (fun j => ctx.tyRelType j Xs[j]! Xs[j]!) fun Rs => do
  ctx.withPerType "h" .default (fun j => ctx.withTyIdx j .default fun js => do
      withLocalDeclD `x (mkAppN Xs[j]! js) fun x => do
      mkForallFVars (js.push x) (mkAppN Rs[j]! (js ++ #[x, x]))) fun hs => do
  let ids ← (Array.range n).mapM fun j => ctx.withTyIdx j .default fun js => do
    if js.isEmpty then mkAppOptM ``id #[Xs[j]!] else
    withLocalDeclD `x (mkAppN Xs[j]! js) fun x => mkLambdaFVars (js.push x) x
  for m in [0:n] do
    let nm := .str (ctx.layerN m) "rel_refl"
    unless ← free nm do continue
    ctx.withTyIdx m .implicit fun uidx => do
    withLocalDeclD `a (← ctx.layerAt m w Xs uidx) fun a => do
    let relAt (b : Expr) := ctx.genAt (ctx.layerRelN m) [w, w] (Xs ++ Xs ++ Rs ++ uidx ++ #[b, b])
    let relMap ← ctx.genAt (.str (ctx.layerN m) "rel_map") [w, w, w]
      (Xs ++ Xs ++ Xs ++ Rs ++ ids ++ ids ++ uidx ++ #[a] ++ hs)
    let mapId ← ctx.genAt (.str (ctx.layerN m) "map_id") [w] (Xs ++ uidx ++ #[a])
    let relSelf ← lam `b (← ctx.layerAt m w Xs uidx) fun b => relAt b
    let value ← mkAppM ``Eq.mp #[← mkCongrArg relSelf mapId, relMap]
    let xs := ctx.params ++ Xs ++ Rs ++ hs ++ uidx ++ #[a]
    let (type, value) ← withBinderInfo ctx.params .implicit do
      return (← mkForallFVars xs (← relAt a), ← mkLambdaFVars xs value)
    addThm nm (← ctx.levelParamsOf fresh #[type]) type value ctx.types[m]!.ref

/-! ### The constructors -/

/-- The rules of the family's `dtor` and `ctor` for `c`: `T.dtor_cᵢ`, `T.ctor_cᵢ`, or in a block
`Blk.dtor_cᵢ`, `Blk.ctor_cᵢ` with the block-level name of `c` (`Even_Odd.dtor_Even_succ`), since
`Tₘ.dtor_cᵢ`, `Tₘ.ctor_cᵢ` are the rules of the destructor and the constructor per type. -/
def dtorRuleN (c : Ctor) : Name :=
  if ctx.isBlock then ctx.gen ("dtor_" ++ c.fname.toString) else ctx.tName' c "dtor_" ""
def ctorRuleN (c : Ctor) : Name :=
  if ctx.isBlock then ctx.gen ("ctor_" ++ c.fname.toString) else ctx.tName' c "ctor_" ""

/-- In a block, Lambek's lemma per type, as step 3 states it for a single type, and the rules of
the destructor and the constructor per type:

* `Tₘ.dtor_ctor`, `Tₘ.ctor_dtor`: the block's under the maps by `ι` and `ρ` (`atTypes`), whose
  composites are the identity by cases on the index (`mapCancel`); `Tₘ.ctor_injective` from
  `Tₘ.dtor_ctor`;
* `Tₘ.dtor_cᵢ : (Tₘ.cᵢ ys).dtor = F.cᵢ ys`, at the layer at the types. `Tₘ.dtor` is the block's
  `dtor` followed by the map by `ι`, which leaves a recursive argument as it is by definition and
  a nested one by `IOcc.map_heq_self`: the proof is `Blk.dtor_ctor` under the map, then these
  equations, argument by argument;
* `Tₘ.ctor_cᵢ : Tₘ.ctor (F.cᵢ ys) = Tₘ.cᵢ ys`, from `Tₘ.dtor_cᵢ` and `Tₘ.ctor_dtor`. -/
def genTypeLambek : TermElabM Unit := do
  unless ctx.isBlock do return
  let L ← ctx.tLvl
  let T ← ctx.tFam
  let Ts ← ctx.tyFams
  let ats ← ctx.atTypes
  let ctorAt (m : Nat) (uidx : Array Expr) (y : Expr) :=
    ctx.genAt (ctx.tyGenP m "ctor") [] (uidx.push y)
  let dtorAt (m : Nat) (uidx : Array Expr) (t : Expr) :=
    ctx.genAt (ctx.tyGenP m "dtor") [] (uidx.push t)
  -- `Tₘ.dtor_ctor`, `Tₘ.ctor_dtor`, `Tₘ.ctor_injective`
  for m in [0:ctx.types.size] do
    ctx.withTyIdx m .implicit fun uidx => do
    let ixT := ctx.wrap m uidx
    let (Tm, FT) := (← ctx.tyAt m uidx, ← ctx.layerAt m L Ts uidx)
    let thm (s : String) (xs : Array Expr) (stmt value : Expr) : TermElabM Unit := do
      let xs := ctx.params ++ uidx ++ xs
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs stmt, ← mkLambdaFVars xs value)
      addThm (ctx.tyGenP m s) (← ctx.levelParamsOf [] #[type]) type value ctx.types[m]!.ref
    -- `map ι (dtor (ctor (map ρ y))) = map ι (map ρ y) = y`
    withLocalDeclD `y FT fun y => do
      let mapι ← lam `z (← ctx.fAt L T ixT) fun z => ctx.mapAt L L T ats.StT ats.ι ixT z
      let e₁ ← mkCongrArg mapι
        (← ctx.appAt ctx.dtor_ctor ixT #[← ctx.mapAt L L ats.StT T ats.ρ ixT y])
      let e₂ ← ctx.mapCancel L ats.StT T ats.ρ ats.ι ats.hιρ ixT y
      thm "dtor_ctor" #[y] (← mkEq (← dtorAt m uidx (← ctorAt m uidx y)) y) (← mkEqTrans e₁ e₂)
      addSimp (ctx.tyGenP m "dtor_ctor")
    -- `ctor (map ρ (map ι (dtor t))) = ctor (dtor t) = t`
    withLocalDeclD `t Tm fun t => do
      let ctorB ← lam `z (← ctx.fAt L T ixT) fun z => ctx.appAt ctx.ctor ixT #[z]
      let e₁ ← mkCongrArg ctorB
        (← ctx.mapCancel L T ats.StT ats.ι ats.ρ ats.hρι ixT (← ctx.appAt ctx.dtor ixT #[t]))
      let e₂ ← ctx.appAt ctx.ctor_dtor ixT #[t]
      thm "ctor_dtor" #[t] (← mkEq (← ctorAt m uidx (← dtorAt m uidx t)) t) (← mkEqTrans e₁ e₂)
    -- `Function.LeftInverse.injective`
    let ctorF ← ctx.genAt (ctx.tyGenP m "ctor") [] uidx
    let dtorF ← ctx.genAt (ctx.tyGenP m "dtor") [] uidx
    let inv ← lam `y FT fun y => ctx.genAt (ctx.tyGenP m "dtor_ctor") [] (uidx.push y)
    thm "ctor_injective" #[] (← mkAppM ``Function.Injective #[ctorF])
      (← mkAppOptM ``Function.LeftInverse.injective #[none, none, dtorF, ctorF, inv])
  -- `Tₘ.dtor_cᵢ`, `Tₘ.ctor_cᵢ`
  for c in ctx.ctors do
    ctx.withTArgs c fun ys σ => do
    let m := c.owner
    let ixT := c.idx.map σ
    let uidx := c.uidx.map σ
    let fapp ← ctx.fCtorApp c L T ys
    let capp ← ctx.tCtorApp c ys
    let fT ← ctx.fCtorApp c L ats.StT ys
    let thm (n : Name) (stmt value : Expr) : TermElabM Unit := do
      let xs := ctx.params ++ ys
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs stmt, ← mkLambdaFVars xs value)
      addThm n (← ctx.levelParamsOf [] #[type]) type value ctx.types[m]!.ref
      addSimp n
    -- `map ι (dtor (ctor (F.c ys))) = map ι (F.c ys)`
    let mapι ← lam `z (← ctx.fAt L T ixT) fun z => ctx.mapAt L L T ats.StT ats.ι ixT z
    let h₁ ← mkCongrArg mapι (← ctx.appAt ctx.dtor_ctor ixT #[fapp])
    -- `map ι (F.c ys)` is `F.c ys'` by definition, with `ys'` the nested arguments mapped by `ι`:
    -- `F.c ys' = F.c ys`, argument by argument.
    let mut h₂ ← mkEqRefl (← ctx.fCtorApp c L ats.StT #[])
    for a in c.args, y in ys do
      match a.kind with
      | .nest n =>
        let o := ctx.nestAt n L σ
        let heq ← mkAppM ``Codata.IOcc.map_heq_self #[o, ats.hT, ats.ι, ats.hι, y]
        h₂ ← mkCongr h₂ (← mkAppM ``eq_of_heq #[heq])
      | _ => h₂ ← mkCongrFun h₂ y
    thm (ctx.tName' c "dtor_" "") (← mkEq (← dtorAt m uidx capp) fT) (← mkEqTrans h₁ h₂)
    -- `ctor (F.c ys) = ctor (cᵢ ys).dtor = cᵢ ys`
    let ctorF ← lam `z (← ctx.layerAt m L Ts uidx) fun z => ctorAt m uidx z
    let dtor_c ← ctx.genAt (ctx.tName' c "dtor_" "") [] ys
    let e₁ ← mkCongrArg ctorF (← mkEqSymm dtor_c)
    let e₂ ← ctx.genAt (ctx.tyGenP m "ctor_dtor") [] (uidx.push capp)
    thm (ctx.tName' c "ctor_" "") (← mkEq (← ctorAt m uidx fT) capp) (← mkEqTrans e₁ e₂)

/-- `T.cᵢ`, `T.dtor_cᵢ`, `T.ctor_cᵢ`, `T.cᵢ_inj`, `T.cᵢ_ne_cⱼ`; in a block, the rules of the
block's `dtor` and `ctor` are `Blk.dtor_cᵢ`, `Blk.ctor_cᵢ`, and `Tₘ.dtor_cᵢ`, `Tₘ.ctor_cᵢ` those
of the destructor and the constructor per type (`genTypeLambek`). -/
def genCtors : TermElabM Unit := do
  let L ← ctx.tLvl
  let T ← ctx.tFam
  let thm (c : Ctor) (n : Name) (xs : Array Expr) (stmt value : Expr) : TermElabM Unit := do
    let (type, value) ← withBinderInfo ctx.params .implicit do
      return (← mkForallFVars (ctx.params ++ xs) stmt, ← mkLambdaFVars (ctx.params ++ xs) value)
    addThm n (← ctx.levelParamsOf [] #[type]) type value ctx.types[c.owner]!.ref
    addSimp n
  for c in ctx.ctors do
    -- The constructor, with the default values and tactics of its arguments, and the range of its
    -- own syntax, as in `inductive`.
    ctx.withTArgs c (annotated := true) fun ys σ => do
      let idx := c.idx.map σ
      let fapp ← ctx.fCtorApp c L T ys
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars (ctx.params ++ ys) (← ctx.tyAt c.owner (c.uidx.map σ)),
          ← mkLambdaFVars (ctx.params ++ ys) (← ctx.appAt ctx.ctor idx #[fapp]))
      addRangesUser (ctx.tCtor c) c.ref c.nameRef
      addDef (ctx.tCtor c) (← ctx.levelParamsOf [] #[type, value]) type value c.ref
    ctx.withTArgs c fun ys σ => do
    let idx := c.idx.map σ
    let fapp ← ctx.fCtorApp c L T ys
    let capp ← ctx.tCtorApp c ys
    thm c (ctx.dtorRuleN c) ys (← mkEq (← ctx.appAt ctx.dtor idx #[capp]) fapp)
      (← ctx.appAt ctx.dtor_ctor idx #[fapp])
    thm c (ctx.ctorRuleN c) ys (← mkEq (← ctx.appAt ctx.ctor idx #[fapp]) capp)
      (← mkEqRefl capp)
  -- Injectivity, as `T.F.c.injEq`: the arguments the result index needs are shared by the two
  -- sides (`sharedArgs`), the proofs are left out of the conjunction, an argument whose type
  -- mentions another one not shared is related by `HEq` when the two types differ, and there is
  -- no lemma if nothing is left.
  for c in ctx.ctors do
    ctx.withTArgs c fun ys σ => do
    let shared ← sharedArgs ys (c.uidx.map σ)
    if shared.all id then return
    withPrimed ys shared fun ys' new => do
    let idx := c.idx.map σ
    let eqs ← (ys.zip ys').filterMapM fun (y, y') => do
      if y == y' || (← isProof y) then return none
      return some (← mkEqHEq y y')
    if eqs.isEmpty then return
    let conj := eqs.pop.foldr (init := eqs.back!) mkAnd
    let stmt := mkIff (← mkEq (← ctx.tCtorApp c ys) (← ctx.tCtorApp c ys')) conj
    let injEq ← ctx.genAt (ctx.fCtor c ++ `injEq) [L] (#[T] ++ ys ++ new)
    let value ← mkAppOptM ``Codata.inj_of #[none, none, ← ctx.appAt ctx.ctor idx #[],
      ← ctx.appAt ctx.ctor_injective idx #[], ← ctx.fCtorApp c L T ys, ← ctx.fCtorApp c L T ys',
      none, injEq]
    thm c (ctx.tName' c "" "_inj") (ys ++ new) stmt value
  -- Disjointness, for constructors of the same type whose results meet (`withMeet`): the
  -- arguments of `c` are variables and those of `c'` are where the indices unify, or, when they
  -- do not unify so, the other way round. The variables come first, and the others are primed.
  for c in ctx.ctors do
    for c' in ctx.ctors do
      if c.name == c'.name || c.owner != c'.owner then continue
      let disj (ys ys' xs : Array Expr) (idx : Array Expr) : TermElabM Unit := do
        let stmt ← mkAppM ``Ne #[← ctx.tCtorApp c ys, ← ctx.tCtorApp c' ys']
        let (fa, fb) := (← ctx.fCtorApp c L T ys, ← ctx.fCtorApp c' L T ys')
        let hab ← lam `h (← mkEq fa fb) fun h => mkNoConfusion (mkConst ``False) h
        let value ← mkAppOptM ``Codata.ne_of #[none, none, ← ctx.appAt ctx.dtor idx #[], none,
          none, none, none,
          mkAppN (← ctx.constWith (ctx.dtorRuleN c) []) (ctx.params ++ ys),
          mkAppN (← ctx.constWith (ctx.dtorRuleN c') []) (ctx.params ++ ys'), hab]
        thm c (ctx.tyName c.owner ++ Name.mkSimple (c.name.toString ++ "_ne_" ++ c'.name.toString))
          xs stmt value
      let done ← ctx.withMeet c c' fun ys ys' new idx => disj ys ys' (ys ++ new) idx
      if done.isNone then
        discard <| ctx.withMeet c' c fun ys' ys new idx => disj ys ys' (ys' ++ new) idx

/-- Equality by the destructor: in a block, per type, `Tₘ.dtor_injective` (`Tₘ.ctor_dtor` as a left
inverse) and the `simp` lemma `Tₘ.dtor_inj`, as step 3 gives them for a single type; and for every
constructor the `simp` lemma `T.dtor_eq_cᵢ_iff : t.dtor = F.cᵢ ys ↔ t = T.cᵢ ys`, `T.dtor_inj` at
`T.cᵢ ys` after `T.dtor_cᵢ`, so that `simp` turns an equation of layers, from `match h : t.dtor`
say, into one of values. A lemma whose name is taken is not generated. -/
def genDtorLemmas : TermElabM Unit := do
  let free (nm : Name) : MetaM Bool := return !(← getEnv).contains nm
  -- `Tₘ.dtor_injective`, `Tₘ.dtor_inj`
  if ctx.isBlock then
    for m in [0:ctx.types.size] do
      let (nI, nE) := (ctx.tyGenP m "dtor_injective", ctx.tyGenP m "dtor_inj")
      unless (← free nI) && (← free nE) do continue
      ctx.withTyIdx m .implicit fun uidx => do
      let Tm ← ctx.tyAt m uidx
      let ctorF ← ctx.genAt (ctx.tyGenP m "ctor") [] uidx
      let dtorF ← ctx.genAt (ctx.tyGenP m "dtor") [] uidx
      let inv ← lam `t Tm fun t => ctx.genAt (ctx.tyGenP m "ctor_dtor") [] (uidx.push t)
      let value ← mkAppOptM ``Function.LeftInverse.injective #[none, none, ctorF, dtorF, inv]
      let xs := ctx.params ++ uidx
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs (← mkAppM ``Function.Injective #[dtorF]),
          ← mkLambdaFVars xs value)
      addThm nI (← ctx.levelParamsOf [] #[type]) type value ctx.types[m]!.ref
      withLocalDecl `x .implicit Tm fun x => do
      withLocalDecl `y .implicit Tm fun y => do
      let stmt := mkIff (← mkEq (mkApp dtorF x) (mkApp dtorF y)) (← mkEq x y)
      let value ← mkAppOptM ``Function.Injective.eq_iff
        #[none, none, none, ← ctx.genAt nI [] uidx, x, y]
      let xs := ctx.params ++ uidx ++ #[x, y]
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs stmt, ← mkLambdaFVars xs value)
      addThm nE (← ctx.levelParamsOf [] #[type]) type value ctx.types[m]!.ref
      addSimp nE
  -- `T.dtor_eq_cᵢ_iff`
  for c in ctx.ctors do
    let m := c.owner
    let nm := ctx.tName' c "dtor_eq_" "_iff"
    let injN := if ctx.isBlock then ctx.tyGenP m "dtor_inj" else ctx.dtor_inj
    unless (← free nm) && !(← free injN) do continue
    ctx.withTArgs c fun ys σ => do
    let uidx := c.uidx.map σ
    let capp ← ctx.tCtorApp c ys
    let dtorc ← ctx.genAt (ctx.tName' c "dtor_" "") [] ys
    let some (_, _, fapp) := (← inferType dtorc).eq?
      | throwError "internal error: `dtor_{c.name}` is not an equation"
    let used := c.args.map (·.name)
    let tn := ([`t, `x, `s, `v].find? (!used.contains ·)).getD `t₀
    withLocalDecl tn .implicit (← ctx.tyAt m uidx) fun t => do
    let (dt, inj) ← if ctx.isBlock then
        pure (← ctx.genAt (ctx.tyGenP m "dtor") [] (uidx.push t),
          ← ctx.genAt injN [] (uidx ++ #[t, capp]))
      else
        let idx := c.idx.map σ
        pure (← ctx.appAt ctx.dtor idx #[t], ← ctx.genAt injN [] (idx ++ #[t, capp]))
    let stmt := mkIff (← mkEq dt fapp) (← mkEq t capp)
    -- `(t.dtor = F.c ys) = (t.dtor = (T.c ys).dtor)`, then `dtor_inj`.
    let e ← mkCongrArg (← lam `z (← inferType fapp) fun z => mkEq dt z) (← mkEqSymm dtorc)
    let value ← mkAppM ``Iff.trans #[← mkAppM ``Iff.of_eq #[e], inj]
    let xs := ctx.params ++ ys.push t
    let (type, value) ← withBinderInfo (ctx.params ++ ys) .implicit do
      return (← mkForallFVars xs stmt, ← mkLambdaFVars xs value)
    addThm nm (← ctx.levelParamsOf [] #[type]) type value ctx.types[m]!.ref
    addSimp nm

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
  let fresh := ctx.motiveLevels
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
  let lvls (xs : Array Expr) := do ctx.elimLevelParamsOf fresh xs
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
    addDef casesN (← ctx.elimLevelParamsOf fresh #[type, value]) type value ref
    addAttrs casesN #[← `(Parser.Term.attrInstance| elab_as_elim),
      ← `(Parser.Term.attrInstance| cases_eliminator)]
    -- `codatatype` has no induction: `induction` is case analysis, not the encoding's.
    if ctx.co then addAttrs casesN #[← `(Parser.Term.attrInstance| induction_eliminator)]
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

/-! ### Blocks: the types, corecursion and folding per type -/

/-- In a block, the types: `Tₘ params idx := Blk params (.Tₘ idx)`. Declared after the family and
before anything that mentions them. -/
def genTypes : TermElabM Unit := do
  unless ctx.isBlock do return
  let L ← ctx.tLvl
  for m in [0:ctx.types.size] do
    let t := ctx.types[m]!
    let xs := ctx.params ++ t.idx
    let value ← mkLambdaFVars xs (← ctx.tAt (ctx.wrap m t.idx))
    let type ← mkForallFVars xs (mkSort L.succ)
    addRangesUser t.name t.ref t.nameRef
    addDef t.name (← ctx.levelParamsOf [] #[type, value]) type value t.ref

/-- In a `codatatype` block, corecursion and coinduction per type, in the shape of Lean's mutual
recursors (one motive per type), with one state and one step per type, and one relation per type:

* `Tₘ.corec c₁ … cₖ s`, with `cⱼ : ∀ idx, Sⱼ idx → Tⱼ.F params S₁ … Sₖ idx` and `s : Sₘ idx`,
  the states in one universe: `Blk.corec` at the family `Blk.St S₁ … Sₖ` and the step made of
  the `cⱼ` by cases on `Blk.Ix`;
* `Tₘ.dtor_corec`, its rule with `Tₘ.dtor` and the map per type, `Tⱼ.corec c₁ … cₖ` at the
  positions of the `j`-th type: `Blk.dtor_corec` under the map by `ι` (`atTypes`), the two maps
  composed (`F.map_comp`), and the composite equal to the packed corecursors by cases on the
  index;
* `Tₘ.corec_eq` from `Tₘ.dtor_corec` and `Tₘ.ctor_dtor` (not `simp`: it loops), and
  `Tₘ.corec_unique`, for morphisms `hⱼ` with `hhⱼ : (hⱼ s).dtor = Tⱼ.F.map h₁ … hₖ (cⱼ s)`:
  `Blk.corec_unique` at the morphisms packed, its hypothesis at each type from `hhⱼ` under the map
  by `ρ`;
* `Tₘ.bisim R₁ … Rₖ H₁ … Hₖ`, with `Hⱼ : ∀ idx x y, Rⱼ idx x y → Tⱼ.F.Rel R₁ … Rₖ x.dtor y.dtor`:
  `Blk.bisim` at the relation made of the `Rⱼ` by cases on `Blk.Ix`, its hypothesis at each type
  from `Hⱼ` by `Codata.rel_of_map_heq`, the layer at the types being the block's along `ι`.

The block-level `Blk.corec`, `Blk.corec_unique`, `Blk.bisim` take one family over the whole
block. -/
def genTypeCorecs : TermElabM Unit := do
  unless ctx.isBlock do return
  let L ← ctx.tLvl
  let T ← ctx.tFam
  let Ts ← ctx.tyFams
  let (ixTy, _, _) ← ctx.ixType
  let ats ← ctx.atTypes
  let fresh := ctx.motiveLevels
  let wS := ctx.holeLevel (.param fresh[0]!)
  -- `Tₘ.corec` and `Tₘ.dtor_corec`
  do
    ctx.withPerType "S" .implicit (ctx.tyFamType · wS) fun Ss => do
    let StS ← ctx.stAt wS Ss
    ctx.withPerType "c" .default (fun j => ctx.withTyIdx j .default fun js => do
        mkForallFVars js (← mkArrow (mkAppN Ss[j]! js) (← ctx.layerAt j wS Ss js))) fun cs => do
    let step ← ctx.ixCases (fun i => do mkArrow (mkApp StS i) (← ctx.fAt wS StS #[i]))
      fun j uidx => pure (mkAppN cs[j]! uidx)
    let corecAt (m : Nat) (uidx : Array Expr) (s : Expr) : MetaM Expr :=
      ctx.genAt (ctx.tyGenP m "corec") [wS] (Ss ++ cs ++ uidx ++ #[s])
    for m in [0:ctx.types.size] do
      ctx.withTyIdx m .implicit fun uidx => do
      withLocalDeclD `s (mkAppN Ss[m]! uidx) fun s => do
      let value ← ctx.genAt ctx.corec [wS] #[StS, step, ctx.ixAt m uidx, s]
      let xs := ctx.params ++ Ss ++ cs ++ uidx ++ #[s]
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs (← ctx.tyAt m uidx), ← mkLambdaFVars xs value)
      addDef (ctx.tyGenP m "corec") (← ctx.elimLevelParamsOf fresh #[type, value]) type value
        ctx.types[m]!.ref
    -- The corecursors as the functions of the map: `fun idx s => Tⱼ.corec c₁ … cₖ s`.
    let corecFns ← (Array.range ctx.types.size).mapM fun j => ctx.withTyIdx j .default fun js => do
      withLocalDeclD `s (mkAppN Ss[j]! js) fun s => do
      let e ← mkLambdaFVars (js.push s) (← corecAt j js s)
      return if js.isEmpty then e.eta else e
    let packC ← ctx.ixCases (fun i => mkArrow (mkApp StS i) (mkApp ats.StT i))
      fun j uidx => pure (mkAppN corecFns[j]! uidx).headBeta
    -- The block's corecursor as the function of its map, as `Blk.dtor_corec` states it.
    let g ← lam `i ixTy fun i => do lam `s (mkApp StS i) fun s => do
      ctx.genAt ctx.corec [wS] #[StS, step, i, s]
    -- `fun x => ι i (g i x)`, the two maps composed.
    let ιg (i : Expr) : TermElabM Expr := lam `x (mkApp StS i) fun x => do
      return (mkApp2 ats.ι i (mkApp2 g i x).headBeta).headBeta
    let hpt ← ctx.ixCases (fun i => do mkEq (← ιg i) (mkApp packC i).headBeta)
      fun j uidx => do mkEqRefl (← ιg (ctx.ixAt j uidx))
    let ιgF ← lam `i ixTy ιg
    let hφ ← mkAppOptM ``funext #[none, none, ιgF, packC, hpt]
    for m in [0:ctx.types.size] do
      ctx.withTyIdx m .implicit fun uidx => do
      withLocalDeclD `s (mkAppN Ss[m]! uidx) fun s => do
      let ixT := #[ctx.ixAt m uidx]
      let a := mkAppN cs[m]! (uidx.push s)
      let lhs ← ctx.genAt (ctx.tyGenP m "dtor") [] (uidx ++ #[← corecAt m uidx s])
      let rhs ← ctx.genAt (ctx.layerMapN m) [wS, L] (Ss ++ Ts ++ corecFns ++ uidx ++ #[a])
      -- `map ι (dtor (corec s)) = map ι (map g a)`
      let mapι ← lam `z (← ctx.fAt L T ixT) fun z => ctx.mapAt L L T ats.StT ats.ι ixT z
      let e₁ ← mkCongrArg mapι (← ctx.genAt ctx.dtor_corec [wS] (#[StS, step] ++ ixT ++ #[s]))
      -- `map ι (map g a) = map (fun i x => ι i (g i x)) a`
      let e₂ ← mkEqSymm (← ctx.genAt ctx.Fmap_comp [wS, L, L]
        (#[StS, T, ats.StT, ats.ι, g] ++ ixT ++ #[a]))
      -- `… = map (packed corecursors) a`
      let mapφ ← lam `φ (← inferType packC) fun φ => ctx.mapAt wS L StS ats.StT φ ixT a
      let e₃ ← mkCongrArg mapφ hφ
      let value ← mkEqTrans e₁ (← mkEqTrans e₂ e₃)
      let xs := ctx.params ++ Ss ++ cs ++ uidx ++ #[s]
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs (← mkEq lhs rhs), ← mkLambdaFVars xs value)
      let n := ctx.tyGenP m "dtor_corec"
      addThm n (← ctx.elimLevelParamsOf fresh #[type]) type value ctx.types[m]!.ref
      addSimp n
    -- `Tₘ.corec_eq`: `corec s = ctor (dtor (corec s)) = ctor (map … (c s))`.
    for m in [0:ctx.types.size] do
      ctx.withTyIdx m .implicit fun uidx => do
      withLocalDeclD `s (mkAppN Ss[m]! uidx) fun s => do
      let cor ← corecAt m uidx s
      let ctorF ← lam `z (← ctx.layerAt m L Ts uidx) fun z =>
        ctx.genAt (ctx.tyGenP m "ctor") [] (uidx.push z)
      let mapped ← ctx.genAt (ctx.layerMapN m) [wS, L]
        (Ss ++ Ts ++ corecFns ++ uidx ++ #[mkAppN cs[m]! (uidx.push s)])
      let e₁ ← mkEqSymm (← ctx.genAt (ctx.tyGenP m "ctor_dtor") [] (uidx.push cor))
      let e₂ ← mkCongrArg ctorF
        (← ctx.genAt (ctx.tyGenP m "dtor_corec") [wS] (Ss ++ cs ++ uidx ++ #[s]))
      let xs := ctx.params ++ Ss ++ cs ++ uidx ++ #[s]
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs (← mkEq cor (mkApp ctorF mapped).headBeta),
          ← mkLambdaFVars xs (← mkEqTrans e₁ e₂))
      addThm (ctx.tyGenP m "corec_eq") (← ctx.elimLevelParamsOf fresh #[type]) type value
        ctx.types[m]!.ref
    -- `Tₘ.corec_unique`: `Blk.corec_unique` at the morphisms packed, its hypothesis at each type
    -- from `hhⱼ` under the map by `ρ`.
    ctx.withPerType "h" .default (fun j => ctx.tyFnType j Ss[j]! Ts[j]!) fun hs => do
    ctx.withPerType "hh" .default (fun j => ctx.withTyIdx j .default fun js => do
        withLocalDeclD `s (mkAppN Ss[j]! js) fun s => do
        let lhs ← ctx.genAt (ctx.tyGenP j "dtor") [] (js.push (mkAppN hs[j]! (js.push s)))
        let rhs ← ctx.genAt (ctx.layerMapN j) [wS, L]
          (Ss ++ Ts ++ hs ++ js ++ #[mkAppN cs[j]! (js.push s)])
        mkForallFVars (js.push s) (← mkEq lhs rhs)) fun hhs => do
    let packH ← ctx.ixCases (fun i => mkArrow (mkApp StS i) (mkApp T i))
      fun j uidx => pure (mkAppN hs[j]! uidx)
    let packH' ← ctx.ixCases (fun i => mkArrow (mkApp StS i) (mkApp ats.StT i))
      fun j uidx => pure (mkAppN hs[j]! uidx)
    let hρh ← ctx.funextCases (← ctx.compFn StS ats.ρ packH') packH
    let HH ← ctx.ixCases (fun i => do
        withLocalDeclD `s (mkApp StS i) fun s => do
        mkForallFVars #[s] (← mkEq (← ctx.appAt ctx.dtor #[i] #[(mkApp2 packH i s).headBeta])
          (← ctx.mapAt wS L StS T packH #[i] (mkApp2 step i s).headBeta)))
      fun j uidx => do
        let ixT := #[ctx.ixAt j uidx]
        lam `s (mkAppN Ss[j]! uidx) fun s => do
        let x ← ctx.appAt ctx.dtor ixT #[mkAppN hs[j]! (uidx.push s)]
        let a := mkAppN cs[j]! (uidx.push s)
        -- `x = map ρ (map ι x) = map ρ (map packH' a) = map (ρ ∘ packH') a = map packH a`
        let e₁ ← mkEqSymm (← ctx.mapCancel L T ats.StT ats.ι ats.ρ ats.hρι ixT x)
        let mapρ ← lam `z (← ctx.fAt L ats.StT ixT) fun z => ctx.mapAt L L ats.StT T ats.ρ ixT z
        let e₂ ← mkCongrArg mapρ (mkAppN hhs[j]! (uidx.push s))
        let e₃ ← mkEqSymm (← ctx.genAt ctx.Fmap_comp [wS, L, L]
          (#[StS, ats.StT, T, ats.ρ, packH'] ++ ixT ++ #[a]))
        let e₄ ← ctx.mapCongr wS L StS T hρh ixT a
        mkEqTrans e₁ (← mkEqTrans e₂ (← mkEqTrans e₃ e₄))
    for m in [0:ctx.types.size] do
      ctx.withTyIdx m .implicit fun uidx => do
      withLocalDeclD `s (mkAppN Ss[m]! uidx) fun s => do
      let value ← ctx.genAt ctx.corec_unique [wS] #[StS, step, packH, HH, ctx.ixAt m uidx, s]
      let xs := ctx.params ++ Ss ++ cs ++ hs ++ hhs ++ uidx ++ #[s]
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs (← mkEq (mkAppN hs[m]! (uidx.push s)) (← corecAt m uidx s)),
          ← mkLambdaFVars xs value)
      addThm (ctx.tyGenP m "corec_unique") (← ctx.elimLevelParamsOf fresh #[type]) type value
        ctx.types[m]!.ref
  -- `Tₘ.bisim`
  ctx.withPerType "R" .default (fun j => ctx.tyRelType j Ts[j]! Ts[j]!) fun Rs => do
  let dtorAt (j : Nat) (uidx : Array Expr) (x : Expr) : MetaM Expr :=
    ctx.genAt (ctx.tyGenP j "dtor") [] (uidx.push x)
  ctx.withPerType "H" .default (fun j => ctx.withTyIdx j .default fun js => do
      let Tj ← ctx.tyAt j js
      withLocalDeclD `x Tj fun x => withLocalDeclD `y Tj fun y => do
      let rel ← ctx.genAt (ctx.layerRelN j) [L, L]
        (Ts ++ Ts ++ Rs ++ js ++ #[← dtorAt j js x, ← dtorAt j js y])
      mkForallFVars (js ++ #[x, y]) (← mkArrow (mkAppN Rs[j]! (js ++ #[x, y])) rel)) fun Hs => do
  -- The relations packed, on the block and on the layer at the types.
  let RB ← ctx.ixCases (fun i => do mkArrow (mkApp T i) (← mkArrow (mkApp T i) (mkSort .zero)))
    fun j uidx => pure (mkAppN Rs[j]! uidx)
  let RT ← ctx.ixCases
    (fun i => do mkArrow (mkApp ats.StT i) (← mkArrow (mkApp ats.StT i) (mkSort .zero)))
    fun j uidx => pure (mkAppN Rs[j]! uidx)
  let hR ← ctx.ixCases (fun i => do
      withLocalDeclD `x (mkApp T i) fun x => withLocalDeclD `y (mkApp T i) fun y => do
      mkForallFVars #[x, y] (mkIff (mkApp3 RB i x y).headBeta
        (mkApp3 RT i (mkApp2 ats.ι i x).headBeta (mkApp2 ats.ι i y).headBeta).headBeta))
    fun j uidx => do
      let Tj ← ctx.tyAt j uidx
      lam `x Tj fun x => lam `y Tj fun y => do
        return mkApp (mkConst ``Iff.refl) (mkAppN Rs[j]! (uidx ++ #[x, y]))
  -- `Codata.rel_of_map_heq` for the block's functor, map and lifting.
  let FE := mkAppN (← ctx.constWith ctx.F [L]) ctx.params
  let mapE := mkAppN (← ctx.constWith ctx.Fmap [L, L]) ctx.params
  let mapIdE := mkAppN (← ctx.constWith ctx.Fmap_id [L]) ctx.params
  let relE ← lam `X (← ctx.famType L) (bi := .implicit) fun X => do
    lam `R (← ctx.famRel X X) fun R => lam `i ixTy (bi := .implicit) fun i => do
    let FX ← ctx.fAt L X #[i]
    lam `a FX fun a => lam `b FX fun b => ctx.relAt L L X X R #[i] a b
  let HB ← ctx.ixCases (fun i => do
      withLocalDeclD `x (mkApp T i) fun x => withLocalDeclD `y (mkApp T i) fun y => do
      let rel ← ctx.relAt L L T T RB #[i] (← ctx.appAt ctx.dtor #[i] #[x])
        (← ctx.appAt ctx.dtor #[i] #[y])
      mkForallFVars #[x, y] (← mkArrow (mkApp3 RB i x y).headBeta rel))
    fun j uidx => do
      let Tj ← ctx.tyAt j uidx
      let ixT := ctx.ixAt j uidx
      lam `x Tj fun x => lam `y Tj fun y => lam `h (mkAppN Rs[j]! (uidx ++ #[x, y])) fun h => do
        mkAppOptM ``Codata.rel_of_map_heq #[ixTy, FE, mapE, mapIdE, relE, T, ats.StT, ats.hT,
          ats.ι, ats.hι, RB, RT, hR, ixT, ← ctx.appAt ctx.dtor #[ixT] #[x],
          ← ctx.appAt ctx.dtor #[ixT] #[y], mkAppN Hs[j]! (uidx ++ #[x, y, h])]
  for m in [0:ctx.types.size] do
    ctx.withTyIdx m .implicit fun uidx => do
    let Tm ← ctx.tyAt m uidx
    withLocalDecl `x .implicit Tm fun x => do
    withLocalDecl `y .implicit Tm fun y => do
    withLocalDeclD `h (mkAppN Rs[m]! (uidx ++ #[x, y])) fun h => do
    let value ← ctx.genAt ctx.bisim [] #[RB, HB, ctx.ixAt m uidx, x, y, h]
    let xs := ctx.params ++ Rs ++ Hs ++ uidx ++ #[x, y, h]
    let (type, value) ← withBinderInfo ctx.params .implicit do
      return (← mkForallFVars xs (← mkEq x y), ← mkLambdaFVars xs value)
    addThm (ctx.tyGenP m "bisim") (← ctx.levelParamsOf [] #[type]) type value ctx.types[m]!.ref

/-- Coinduction up to equality, for `codatatype`: `T.coinduct R H h`, where the step `H` relates the
layers by `R` or equality, `fun x y => R x y ∨ x = y`: `T.bisim` at that relation, the step at an
equal pair by `T.F.rel_refl`. In a block, per type, `Tₘ.coinduct R₁ … Rₖ H₁ … Hₖ` from `Tₘ.bisim`
and `Tⱼ.F.rel_refl`. Not generated when a constructor is named `coinduct`. -/
def genCoinduct : TermElabM Unit := do
  unless ctx.co do return
  let L ← ctx.tLvl
  let Ts ← if ctx.isBlock then ctx.tyFams else pure #[← ctx.tFam]
  let n := Ts.size
  -- `fun idx x y => R idx x y ∨ x = y`, and `fun idx x => Or.inr rfl` its reflexivity.
  let orEq (j : Nat) (R : Expr) : TermElabM Expr := ctx.withTyIdx j .default fun js => do
    let Tj := mkAppN Ts[j]! js
    withLocalDeclD `x Tj fun x => withLocalDeclD `y Tj fun y => do
    mkLambdaFVars (js ++ #[x, y]) (mkOr (mkAppN R (js ++ #[x, y])) (← mkEq x y))
  let orRefl (j : Nat) (R : Expr) : TermElabM Expr := ctx.withTyIdx j .default fun js => do
    withLocalDeclD `x (mkAppN Ts[j]! js) fun x => do
    mkLambdaFVars (js.push x)
      (mkApp3 (Lean.mkConst ``Or.inr) (mkAppN R (js ++ #[x, x])) (← mkEq x x) (← mkEqRefl x))
  -- The layers and the lifting of the `j`-th type.
  let dtorAt (j : Nat) (js : Array Expr) (x : Expr) : MetaM Expr :=
    if ctx.isBlock then ctx.genAt (ctx.tyGenP j "dtor") [] (js.push x)
    else ctx.appAt ctx.dtor js #[x]
  let relAt (j : Nat) (Rs : Array Expr) (js : Array Expr) (a b : Expr) : MetaM Expr :=
    if ctx.isBlock then ctx.genAt (ctx.layerRelN j) [L, L] (Ts ++ Ts ++ Rs ++ js ++ #[a, b])
    else ctx.relAt L L Ts[0]! Ts[0]! Rs[0]! js a b
  let reflAt (j : Nat) (Rs hs : Array Expr) (js : Array Expr) (a : Expr) : MetaM Expr :=
    if ctx.isBlock then ctx.genAt (.str (ctx.layerN j) "rel_refl") [L] (Ts ++ Rs ++ hs ++ js.push a)
    else ctx.genAt ctx.relReflN [L] (#[Ts[0]!, Rs[0]!, hs[0]!] ++ js.push a)
  let names := (Array.range n).map fun m =>
    if ctx.isBlock then ctx.tyGenP m "coinduct" else ctx.gen "coinduct"
  let reflN := (Array.range n).map fun j =>
    if ctx.isBlock then .str (ctx.layerN j) "rel_refl" else ctx.relReflN
  unless (← reflN.allM fun nm => return (← getEnv).contains nm) do return
  let withRs (k : Array Expr → TermElabM Unit) : TermElabM Unit :=
    if ctx.isBlock then ctx.withPerType "R" .default (fun j => ctx.tyRelType j Ts[j]! Ts[j]!) k
    else do withLocalDeclD `R (← ctx.famRel Ts[0]! Ts[0]!) fun R => k #[R]
  withRs fun Rs => do
  let R's ← (Array.range n).mapM fun j => orEq j Rs[j]!
  let hrefl ← (Array.range n).mapM fun j => orRefl j Rs[j]!
  let HTy (j : Nat) : TermElabM Expr := ctx.withTyIdx j .default fun js => do
    let Tj := mkAppN Ts[j]! js
    withLocalDeclD `x Tj fun x => withLocalDeclD `y Tj fun y => do
    let rel ← relAt j R's js (← dtorAt j js x) (← dtorAt j js y)
    mkForallFVars (js ++ #[x, y]) (← mkArrow (mkAppN Rs[j]! (js ++ #[x, y])) rel)
  let withHs (k : Array Expr → TermElabM Unit) : TermElabM Unit :=
    if ctx.isBlock then ctx.withPerType "H" .default HTy k
    else do withLocalDeclD `H (← HTy 0) fun H => k #[H]
  withHs fun Hs => do
  -- The steps of `bisim` at the relations up to equality.
  let H's ← (Array.range n).mapM fun j => ctx.withTyIdx j .default fun js => do
    let Tj := mkAppN Ts[j]! js
    withLocalDeclD `x Tj fun x => withLocalDeclD `y Tj fun y => do
    withLocalDeclD `h (mkAppN R's[j]! (js ++ #[x, y])).headBeta fun h => do
    let motive ← lam `y Tj fun y => do relAt j R's js (← dtorAt j js x) (← dtorAt j js y)
    let atEq ← withLocalDeclD `e (← mkEq x y) fun e => do
      mkLambdaFVars #[e] (← mkAppOptM ``Eq.ndrec
        #[none, x, motive, ← reflAt j R's hrefl js (← dtorAt j js x), y, e])
    mkLambdaFVars (js ++ #[x, y, h])
      (← mkAppM ``Or.elim #[h, mkAppN Hs[j]! (js ++ #[x, y]), atEq])
  for m in [0:n] do
    if (← getEnv).contains names[m]! then continue
    let ref := if ctx.isBlock then ctx.types[m]!.ref else ctx.ref
    let idxBinders (k : Array Expr → TermElabM Unit) : TermElabM Unit :=
      if ctx.isBlock then ctx.withTyIdx m .implicit k else k ctx.idx
    idxBinders fun js => do
    let Tm := mkAppN Ts[m]! js
    withLocalDecl `x .implicit Tm fun x => do
    withLocalDecl `y .implicit Tm fun y => do
    withLocalDeclD `h (mkAppN Rs[m]! (js ++ #[x, y])) fun h => do
    let hor ← mkAppOptM ``Or.inl #[none, ← mkEq x y, h]
    let value ← if ctx.isBlock then
        ctx.genAt (ctx.tyGenP m "bisim") [] (R's ++ H's ++ js ++ #[x, y, hor])
      else ctx.genAt ctx.bisim [] (#[R's[0]!, H's[0]!] ++ js ++ #[x, y, hor])
    let xs := ctx.params ++ Rs ++ Hs ++ js ++ #[x, y, h]
    let (type, value) ← withBinderInfo (ctx.params ++ js) .implicit do
      return (← mkForallFVars xs (← mkEq x y), ← mkLambdaFVars xs value)
    addThm names[m]! (← ctx.levelParamsOf [] #[type]) type value ref

/-- In a `datatype` block, folding per type, in the shape of Lean's mutual recursors (one motive per
type), with one family and one algebra per type, as step 3 states it for a single type:

* `Tₘ.fold a₁ … aₖ t`, with `aⱼ : ∀ idx, Tⱼ.F params S₁ … Sₖ idx → Sⱼ idx` and `t : Tₘ idx`, the
  families in one universe: `Blk.fold` at the family `Blk.St S₁ … Sₖ` and the algebra made of
  the `aⱼ` by cases on `Blk.Ix`;
* `Tₘ.fold_ctor` (`simp`), its rule with `Tₘ.ctor` and the map per type, `Tⱼ.fold a₁ … aₖ` at the
  positions of the `j`-th type: `Blk.fold_ctor` at `Blk.F.map ρ y`, the two maps composed
  (`F.map_comp`), and the composite equal to the packed folds by cases on the index;
* `Tₘ.fold_eq` from `Tₘ.fold_ctor` and `Tₘ.ctor_dtor`, and `Tₘ.fold_cᵢ` (`simp`) from
  `Tₘ.fold_ctor` and `Tₘ.ctor_cᵢ`, `Tₘ.F.map` computing on `F.cᵢ` by definition;
* `Tₘ.fold_unique`, for morphisms `hⱼ` with `hhⱼ : hⱼ (Tⱼ.ctor y) = aⱼ (Tⱼ.F.map h₁ … hₖ y)`:
  `Blk.fold_unique` at the morphisms packed, its hypothesis at each type from `hhⱼ` at
  `Blk.F.map ι y`.

The block-level `Blk.fold`, `Blk.fold_ctor`, `Blk.fold_unique` take one family over `Blk.Ix`, and
the rules of `Blk.fold` are `Blk.fold_cᵢ`. -/
def genTypeFolds : TermElabM Unit := do
  unless ctx.isBlock do return
  let L ← ctx.tLvl
  let T ← ctx.tFam
  let Ts ← ctx.tyFams
  let (ixTy, _, _) ← ctx.ixType
  let ats ← ctx.atTypes
  let fresh := ctx.motiveLevels
  let wS := ctx.holeLevel (.param fresh[0]!)
  let n := ctx.types.size
  let ref (m : Nat) := ctx.types[m]!.ref
  ctx.withPerType "S" .implicit (ctx.tyFamType · wS) fun Ss => do
  let StS ← ctx.stAt wS Ss
  ctx.withPerType "a" .default (fun j => ctx.withTyIdx j .default fun js => do
      mkForallFVars js (← mkArrow (← ctx.layerAt j wS Ss js) (mkAppN Ss[j]! js))) fun as => do
  let alg ← ctx.ixCases (fun i => do mkArrow (← ctx.fAt wS StS #[i]) (mkApp StS i))
    fun j uidx => pure (mkAppN as[j]! uidx)
  let foldAt (m : Nat) (uidx : Array Expr) (t : Expr) : MetaM Expr :=
    ctx.genAt (ctx.tyGenP m "fold") [wS] (Ss ++ as ++ uidx ++ #[t])
  let thm (m : Nat) (name : Name) (xs : Array Expr) (stmt value : Expr) (simp := false) :
      TermElabM Unit := do
    let xs := ctx.params ++ Ss ++ as ++ xs
    let (type, value) ← withBinderInfo ctx.params .implicit do
      return (← mkForallFVars xs stmt, ← mkLambdaFVars xs value)
    addThm name (← ctx.elimLevelParamsOf fresh #[type]) type value (ref m)
    if simp then addSimp name
  -- `Tₘ.fold`
  for m in [0:n] do
    ctx.withTyIdx m .implicit fun uidx => do
    withLocalDeclD `t (← ctx.tyAt m uidx) fun t => do
    let value ← ctx.genAt ctx.fold [wS] #[StS, alg, ctx.ixAt m uidx, t]
    let xs := ctx.params ++ Ss ++ as ++ uidx ++ #[t]
    let (type, value) ← withBinderInfo ctx.params .implicit do
      return (← mkForallFVars xs (mkAppN Ss[m]! uidx), ← mkLambdaFVars xs value)
    addDef (ctx.tyGenP m "fold") (← ctx.elimLevelParamsOf fresh #[type, value]) type value (ref m)
  -- The folds as the functions of the map, `fun idx t => Tⱼ.fold a₁ … aₖ t`, and packed.
  let foldFns ← (Array.range n).mapM fun j => ctx.withTyIdx j .default fun js => do
    withLocalDeclD `t (← ctx.tyAt j js) fun t => do
    let e ← mkLambdaFVars (js.push t) (← foldAt j js t)
    return if js.isEmpty then e.eta else e
  let packFold ← ctx.ixCases (fun i => mkArrow (mkApp ats.StT i) (mkApp StS i))
    fun j uidx => pure (mkAppN foldFns[j]! uidx).headBeta
  -- The block's fold as the function of its map, as `Blk.fold_ctor` states it.
  let g ← lam `i ixTy fun i => do lam `t (mkApp T i) fun t => do
    ctx.genAt ctx.fold [wS] #[StS, alg, i, t]
  let hgρ ← ctx.funextCases (← ctx.compFn ats.StT g ats.ρ) packFold
  -- `Tₘ.fold_ctor`
  for m in [0:n] do
    ctx.withTyIdx m .implicit fun uidx => do
    let ixT := ctx.wrap m uidx
    withLocalDeclD `y (← ctx.layerAt m L Ts uidx) fun y => do
    let am := mkAppN as[m]! uidx
    let lhs ← foldAt m uidx (← ctx.genAt (ctx.tyGenP m "ctor") [] (uidx.push y))
    let rhs := mkApp am
      (← ctx.genAt (ctx.layerMapN m) [L, wS] (Ts ++ Ss ++ foldFns ++ uidx ++ #[y]))
    -- `fold (ctor (map ρ y)) = a (map g (map ρ y)) = a (map (g ∘ ρ) y) = a (map packFold y)`
    let e₁ ← ctx.genAt ctx.fold_ctor [wS]
      #[StS, alg, ixT[0]!, ← ctx.mapAt L L ats.StT T ats.ρ ixT y]
    let e₂ ← mkEqSymm (← ctx.genAt ctx.Fmap_comp [L, L, wS]
      (#[ats.StT, T, StS, g, ats.ρ] ++ ixT ++ #[y]))
    let e₃ ← ctx.mapCongr L wS ats.StT StS hgρ ixT y
    let value ← mkEqTrans e₁ (← mkCongrArg am (← mkEqTrans e₂ e₃))
    thm m (ctx.tyGenP m "fold_ctor") (uidx.push y) (← mkEq lhs rhs) value (simp := true)
  -- `Tₘ.fold_eq`: `fold t = fold (ctor (dtor t)) = a (map … (dtor t))`
  for m in [0:n] do
    ctx.withTyIdx m .implicit fun uidx => do
    withLocalDeclD `t (← ctx.tyAt m uidx) fun t => do
    let dt ← ctx.genAt (ctx.tyGenP m "dtor") [] (uidx.push t)
    let rhs := mkAppN as[m]! (uidx.push
      (← ctx.genAt (ctx.layerMapN m) [L, wS] (Ts ++ Ss ++ foldFns ++ uidx ++ #[dt])))
    let foldF ← lam `z (← ctx.tyAt m uidx) fun z => foldAt m uidx z
    let e₁ ← mkEqSymm (← mkCongrArg foldF (← ctx.genAt (ctx.tyGenP m "ctor_dtor") [] (uidx.push t)))
    let e₂ ← ctx.genAt (ctx.tyGenP m "fold_ctor") [wS] (Ss ++ as ++ uidx ++ #[dt])
    thm m (ctx.tyGenP m "fold_eq") (uidx.push t) (← mkEq (← foldAt m uidx t) rhs)
      (← mkEqTrans e₁ e₂)
  -- `Tₘ.fold_cᵢ`: `fold (cᵢ ys) = fold (ctor (F.cᵢ ys)) = a (map … (F.cᵢ ys))`, the map on
  -- `F.cᵢ` by definition.
  for c in ctx.ctors do
    ctx.withTArgs c fun ys σ => do
    let m := c.owner
    let uidx := c.uidx.map σ
    let fT ← ctx.fCtorApp c L ats.StT ys
    let mapped ← ctx.layerMapped c ys σ Ts foldFns L wS packFold
    let rhs := mkAppN as[m]! (uidx.push (← ctx.fCtorApp c wS StS mapped))
    let foldF ← lam `z (← ctx.tyAt m uidx) fun z => foldAt m uidx z
    let e₁ ← mkEqSymm (← mkCongrArg foldF (← ctx.genAt (ctx.tName' c "ctor_" "") [] ys))
    let e₂ ← ctx.genAt (ctx.tyGenP m "fold_ctor") [wS] (Ss ++ as ++ uidx ++ #[fT])
    thm m (ctx.tName' c "fold_" "") ys (← mkEq (← foldAt m uidx (← ctx.tCtorApp c ys)) rhs)
      (← mkEqTrans e₁ e₂) (simp := true)
  -- `Tₘ.fold_unique`
  ctx.withPerType "h" .default (fun j => ctx.tyFnType j Ts[j]! Ss[j]!) fun hs => do
  ctx.withPerType "hh" .default (fun j => ctx.withTyIdx j .default fun js => do
      withLocalDeclD `y (← ctx.layerAt j L Ts js) fun y => do
      let lhs := mkAppN hs[j]! (js.push (← ctx.genAt (ctx.tyGenP j "ctor") [] (js.push y)))
      let rhs := mkAppN as[j]! (js.push
        (← ctx.genAt (ctx.layerMapN j) [L, wS] (Ts ++ Ss ++ hs ++ js ++ #[y])))
      mkForallFVars (js.push y) (← mkEq lhs rhs)) fun hhs => do
  let packH ← ctx.ixCases (fun i => mkArrow (mkApp T i) (mkApp StS i))
    fun j uidx => pure (mkAppN hs[j]! uidx)
  let packH' ← ctx.ixCases (fun i => mkArrow (mkApp ats.StT i) (mkApp StS i))
    fun j uidx => pure (mkAppN hs[j]! uidx)
  let hhι ← ctx.funextCases (← ctx.compFn T packH' ats.ι) packH
  let HH ← ctx.ixCases (fun i => do
      withLocalDeclD `y (← ctx.fAt L T #[i]) fun y => do
      mkForallFVars #[y] (← mkEq (mkApp2 packH i (← ctx.appAt ctx.ctor #[i] #[y])).headBeta
        (mkApp2 alg i (← ctx.mapAt L wS T StS packH #[i] y)).headBeta))
    fun j uidx => do
      let ixT := #[ctx.ixAt j uidx]
      lam `y (← ctx.fAt L T ixT) fun y => do
      -- `h (ctor y) = h (ctor (map ρ (map ι y))) = a (map packH' (map ι y)) = a (map packH y)`
      let hF ← lam `z (← ctx.fAt L T ixT) fun z => do
        return mkAppN hs[j]! (uidx.push (← ctx.appAt ctx.ctor ixT #[z]))
      let e₁ ← mkCongrArg hF
        (← mkEqSymm (← ctx.mapCancel L T ats.StT ats.ι ats.ρ ats.hρι ixT y))
      let e₂ := mkAppN hhs[j]! (uidx.push (← ctx.mapAt L L T ats.StT ats.ι ixT y))
      let e₃ ← mkEqSymm (← ctx.genAt ctx.Fmap_comp [L, L, wS]
        (#[T, ats.StT, StS, packH', ats.ι] ++ ixT ++ #[y]))
      let e₄ ← ctx.mapCongr L wS T StS hhι ixT y
      let e₃₄ ← mkCongrArg (mkAppN as[j]! uidx) (← mkEqTrans e₃ e₄)
      mkEqTrans e₁ (← mkEqTrans e₂ e₃₄)
  for m in [0:n] do
    ctx.withTyIdx m .implicit fun uidx => do
    withLocalDeclD `t (← ctx.tyAt m uidx) fun t => do
    let value ← ctx.genAt ctx.fold_unique [wS] #[StS, alg, packH, HH, ctx.ixAt m uidx, t]
    thm m (ctx.tyGenP m "fold_unique") (hs ++ hhs ++ uidx ++ #[t])
      (← mkEq (mkAppN hs[m]! (uidx.push t)) (← foldAt m uidx t)) value

/-! ### `datatype`: the computation rules of `rec` and `fold` -/

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

/-- The name of the computation rule of the family's `fold` for `c`: `T.fold_cᵢ`, or in a block
`Blk.fold_cᵢ` with the block-level name of `c`, since `Tₘ.fold_cᵢ` is the rule of the fold per
type (`genTypeFolds`). -/
def foldRuleN (c : Ctor) : Name :=
  if ctx.isBlock then ctx.gen ("fold_" ++ c.fname.toString) else ctx.tName' c "fold_" ""

/-- `T.rec_cᵢ` (in a block `Blk.rec_cᵢ`) and `T.fold_cᵢ`. The rule of `rec` is that of
`recPos` (`T.recPos_ctor`, at the minor premises of `rec`), followed by `PolyIso.memRec_pos` at
each nested argument (`memValEq`). -/
def genRecLemmas : TermElabM Unit := do
  let L ← ctx.tLvl
  let T ← ctx.tFam
  -- `rec_cᵢ`
  do
    let fresh := ctx.motiveLevels
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
      let posVals ← ctx.recIHVals recPosAt c ys σ (pos := true)
      let mid := pminors[k]!.beta (ys ++ posVals)
      let vals ← ctx.recIHVals recPosAt c ys σ
      let mut h₂ ← mkEqRefl (mkAppN minors[k]! ys)
      for (((a, y), x), p) in (((c.args.zip ys).filter (!·.1.kind.isData)).zip vals).zip
          posVals do
        let e ← match a.kind with
          | .nest n => ctx.memValEq (← ctx.nestMem a n σ) y recPosAt p
          | _ => mkEqRefl x
        h₂ ← mkCongr h₂ e
      let value := mkAppN (.const ``Eq.trans [v]) #[← inferType lhs,
        (← inferType h₁).appFn!.appArg!, mid, mkAppN minors[k]! (ys ++ vals), h₁, h₂]
      let xs := ctx.params ++ #[motive] ++ ys ++ minors
      let (type, value) ← withBinderInfo ctx.params .implicit do
        return (← mkForallFVars xs (← mkEq lhs rhs), ← mkLambdaFVars xs value)
      let n := ctx.recRuleN c
      addThm n (← ctx.elimLevelParamsOf fresh #[type]) type value ctx.ref
      addSimp n
  -- `fold_cᵢ`
  let fresh := ctx.motiveLevels
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
    let n := ctx.foldRuleN c
    addThm n (← ctx.elimLevelParamsOf fresh #[type]) type value ctx.ref
    addSimp n

/-! ### `datatype` blocks: the recursors per type -/

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

/-- In a `datatype` block, `Tₘ.rec` for every type, the recursor in the shape of Lean's mutual
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
  let fresh := ctx.motiveLevels
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
    addDef n (← ctx.elimLevelParamsOf fresh #[type, value]) type value t.ref
    addAttrs n #[← `(Parser.Term.attrInstance| elab_as_elim)]
    mutualRecAttr.setTag n
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
    addThm n (← ctx.elimLevelParamsOf fresh #[type]) type value ctx.types[c.owner]!.ref
    addSimp n

end Ctx

end Codata.Gen
