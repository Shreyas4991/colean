import Colean.Subtypes.Codata

/-!
# Generic theory behind `data`

The inductive dual of `Codata.lean`, for the same signatures: `IsFin` is the *least* fixpoint of
the operator of `IsWf` (`inductive_fixpoint` instead of `coinductive_fixpoint`), and
`Signature.Intype σ : I → Type` the subtype it cuts out. The one-layer constructor and
destructor come from the shared `IsFix` section of `Codata.lean`.

The recursor is where the encoding costs something. `IsFin` is a proposition, so its induction
principle `IsFin.induct` eliminates into `Prop` only; the recursor into a `Sort` is defined by
well-founded recursion on the relation "is an immediate child of", whose well-foundedness *is* a
proposition and is proved by `IsFin.induct`. Consequently `recI` is built from `WellFounded.fix`,
does not reduce definitionally, and its computation rule `recI_ctorI` is propositional. One
dependent recursor `recI` on the container gives everything else: the fold `foldI` into any
family, in any universe, and induction.

The transport theorems `fold_ctor_of`, `rec_of`, `rec_of_ctor`, `induction_of` are what the
command instantiates for its functor `F`, through the isomorphism `toC`/`ofC`; as in the
coinductive case they take the concrete pieces as hypotheses so that `fold` accepts families in
any universe. `Data.Contract` is the contract (`contract.md`): `ctor`, `fold`, `fold_ctor` and
`induction` for the canonical lifting `Data.All`, and the section after it derives the
destructor (Lambek), uniqueness of `fold`, and the characterisation of `T` as the initial
algebra of `F`.
-/

universe w u v u₁ u₂ u₃

namespace Data

/-- The lifting of a functor on families to predicates, defined from its action on functions:
`a` satisfies `All P` when it is the projection of an `F`-value over elements satisfying `P`.
For a polynomial functor this says that every recursive argument satisfies `P`. -/
def All {I : Type w} {F : (I → Type u) → I → Type u}
    (map : ∀ {X Y : I → Type u}, (∀ j, X j → Y j) → ∀ {i}, F X i → F Y i)
    {X : I → Type u} (P : ∀ j, X j → Prop) {i : I} (a : F X i) : Prop :=
  ∃ z : F (fun j => {x : X j // P j x}) i, map (fun _ x => x.1) z = a

end Data

namespace Codata.Signature

variable {σ : Signature.{w, u, v}} {S : σ.I → Type u₃}

/-! ### The predicate and the type -/

/-- Well-founded trees at index `i`: the least fixpoint of the operator of `IsWf`. -/
def IsFin (i : σ.I) (t : Raw σ.Idx σ.Lbl) : Prop :=
  ∃ z : σ.Obj (fun _ => Raw σ.Idx σ.Lbl) i, t = encode i z ∧ ∀ b, IsFin (σ.idx b) (z.child b)
inductive_fixpoint

theorem IsFin.isFix : σ.IsFix IsFin := fun i t => Iff.of_eq (IsFin.eq_def i t)

/-- The inductive family of a signature. -/
def Intype (σ : Signature.{w, u, v}) (i : σ.I) : Type (max w u v) :=
  {t : Raw σ.Idx σ.Lbl // IsFin i t}

/-- The least fixpoint is below the greatest: every well-founded tree is well-formed. -/
theorem IsWf.of_isFin {i : σ.I} {t : Raw σ.Idx σ.Lbl} (h : IsFin i t) : IsWf i t :=
  IsFin.induct IsWf (fun i t h => (IsWf.isFix i t).2 h) i t h

/-- The inclusion of the inductive family into the coinductive one. -/
def Intype.toCotype {i : σ.I} (t : σ.Intype i) : σ.Cotype i := ⟨t.1, IsWf.of_isFin t.2⟩

/-- The constructor on the container. -/
noncomputable def ctorI {i : σ.I} (z : σ.Obj σ.Intype i) : σ.Intype i := IsFin.isFix.ctor z

/-- The destructor on the container. -/
def dtorI {i : σ.I} (t : σ.Intype i) : σ.Obj σ.Intype i := IsFin.isFix.dtor t

theorem dtorI_ctorI {i : σ.I} (z : σ.Obj σ.Intype i) : dtorI (ctorI z) = z :=
  IsFin.isFix.dtor_ctor z

theorem ctorI_dtorI {i : σ.I} (t : σ.Intype i) : ctorI (dtorI t) = t :=
  IsFin.isFix.ctor_dtor t

/-! ### The recursor -/

/-- `s` is an immediate child of `t`, on the total space of the family. -/
def Child (s t : Σ i, σ.Intype i) : Prop := ∃ b, s = ⟨_, (dtorI t.2).child b⟩

/-- Well-founded, by the induction principle of the least fixpoint. -/
theorem child_wf : WellFounded (Child (σ := σ)) := by
  refine ⟨fun ⟨i, t, ht⟩ => ?_⟩
  refine (IsFin.induct (fun i t => IsFin i t ∧ ∀ h : IsFin i t, Acc Child ⟨i, ⟨t, h⟩⟩) ?_
    i t ht).2 ht
  rintro i _ ⟨z, rfl, hz⟩
  refine ⟨(IsFin.isFix i _).2 ⟨z, rfl, fun b => (hz b).1⟩,
    fun h => Acc.intro _ fun s ⟨b, hs⟩ => ?_⟩
  subst hs
  have key : ∀ z₀ : σ.Obj σ.Intype i, z₀ = ⟨z.shape, fun b => ⟨z.child b, (hz b).1⟩⟩ →
      ∀ b, Acc Child ⟨_, z₀.child b⟩ := by
    rintro _ rfl b
    exact (hz b).2 _
  exact key _ (dtorI_ctorI _) b

/-- The recursor on the container, by well-founded recursion on `Child`: dependent, into any
sort. -/
noncomputable def recI {motive : ∀ i, σ.Intype i → Sort u₁}
    (H : ∀ i (z : σ.Obj σ.Intype i), (∀ b, motive _ (z.child b)) → motive i (ctorI z))
    {i : σ.I} (t : σ.Intype i) : motive i t :=
  child_wf.fix (C := fun p => motive p.1 p.2)
    (fun p ih => (congrArg (motive p.1) (ctorI_dtorI p.2)).mp
      (H p.1 (dtorI p.2) fun b => ih ⟨_, (dtorI p.2).child b⟩ ⟨b, rfl⟩))
    ⟨i, t⟩

theorem recI_ctorI {motive : ∀ i, σ.Intype i → Sort u₁}
    (H : ∀ i (z : σ.Obj σ.Intype i), (∀ b, motive _ (z.child b)) → motive i (ctorI z))
    {i : σ.I} (z : σ.Obj σ.Intype i) :
    recI H (ctorI z) = H i z fun b => recI H (z.child b) := by
  show child_wf.fix _ ⟨i, ctorI z⟩ = _
  rw [WellFounded.fix_eq]
  exact cast_ctor_dtor (motive := motive i) ctorI dtorI ctorI_dtorI dtorI_ctorI
    (fun z => H i z fun b => recI H (z.child b)) z

/-- The fold into any family, in any universe. -/
noncomputable def foldI (a : ∀ i, σ.Obj S i → S i) {i : σ.I} (t : σ.Intype i) : S i :=
  recI (motive := fun i _ => S i) (fun i z ih => a i ⟨z.shape, ih⟩) t

theorem foldI_ctorI (a : ∀ i, σ.Obj S i → S i) {i : σ.I} (z : σ.Obj σ.Intype i) :
    foldI a (ctorI z) = a i (Obj.map (fun _ t => foldI a t) z) :=
  recI_ctorI (motive := fun i _ => S i) (fun i z ih => a i ⟨z.shape, ih⟩) z

/-! ### Transport along an isomorphism `F X i ≃ σ.Obj X i` -/

theorem fold_ctor_of {FS : σ.I → Type u₁} {FT : σ.I → Type u₂}
    (toC : ∀ {i}, FT i → σ.Obj σ.Intype i) (ofCT : ∀ {i}, σ.Obj σ.Intype i → FT i)
    (ofCS : ∀ {i}, σ.Obj S i → FS i)
    (map : (∀ j, σ.Intype j → S j) → ∀ {i}, FT i → FS i)
    (ofC_toC : ∀ {i} (y : FT i), ofCT (toC y) = y)
    (ofC_map : ∀ (f : ∀ j, σ.Intype j → S j) {i} (z : σ.Obj σ.Intype i),
      ofCS (Obj.map f z) = map f (ofCT z))
    (a : ∀ i, FS i → S i) {i : σ.I} (y : FT i) :
    foldI (fun j z => a j (ofCS z)) (ctorI (toC y)) =
      a i (map (fun _ t => foldI (fun j z => a j (ofCS z)) t) y) := by
  rw [foldI_ctorI, ofC_map, ofC_toC]

/-- The dependent recursor for `F`, with the induction hypotheses at the positions of `toC`. -/
noncomputable def rec_of {FT : σ.I → Type u₂} (toC : ∀ {i}, FT i → σ.Obj σ.Intype i)
    (ofC : ∀ {i}, σ.Obj σ.Intype i → FT i)
    (toC_ofC : ∀ {i} (z : σ.Obj σ.Intype i), toC (ofC z) = z)
    {motive : ∀ i, σ.Intype i → Sort u₁}
    (H : ∀ i (y : FT i), (∀ b, motive _ ((toC y).child b)) → motive i (ctorI (toC y)))
    {i : σ.I} (t : σ.Intype i) : motive i t :=
  recI (motive := motive)
    (fun i z => (toC_ofC z).rec
      (motive := fun z' _ => (∀ b, motive _ (z'.child b)) → motive i (ctorI z')) (H i (ofC z)))
    t

theorem rec_of_ctor {FT : σ.I → Type u₂} (toC : ∀ {i}, FT i → σ.Obj σ.Intype i)
    (ofC : ∀ {i}, σ.Obj σ.Intype i → FT i)
    (toC_ofC : ∀ {i} (z : σ.Obj σ.Intype i), toC (ofC z) = z)
    (ofC_toC : ∀ {i} (y : FT i), ofC (toC y) = y)
    {motive : ∀ i, σ.Intype i → Sort u₁}
    (H : ∀ i (y : FT i), (∀ b, motive _ ((toC y).child b)) → motive i (ctorI (toC y)))
    {i : σ.I} (y : FT i) :
    rec_of toC ofC toC_ofC H (ctorI (toC y)) =
      H i y fun b => rec_of toC ofC toC_ofC H ((toC y).child b) := by
  have key : ∀ (y' : FT i) (h : toC y' = toC y) (ih : ∀ b, motive _ ((toC y).child b)),
      y' = y → h.rec (motive := fun z' _ => (∀ b, motive _ (z'.child b)) → motive i (ctorI z'))
        (H i y') ih = H i y ih := by
    intro y' h ih hy
    subst hy
    rfl
  rw [rec_of, recI_ctorI]
  exact key _ (toC_ofC (toC y)) _ (ofC_toC y)

/-- Induction for `F`, with the canonical lifting `Data.All`. All families here live in the
universe of `σ.Intype`, so the functor can be a bound variable. -/
theorem induction_of {F : (σ.I → Type (max w u v)) → σ.I → Type (max w u v)}
    (map : ∀ {X Y : σ.I → Type (max w u v)}, (∀ j, X j → Y j) → ∀ {i}, F X i → F Y i)
    (toC : ∀ {i}, F σ.Intype i → σ.Obj σ.Intype i)
    (ofC : ∀ {X : σ.I → Type (max w u v)} {i}, σ.Obj X i → F X i)
    (toC_ofC : ∀ {i} (z : σ.Obj σ.Intype i), toC (ofC z) = z)
    (ofC_toC : ∀ {i} (y : F σ.Intype i), ofC (toC y) = y)
    (ofC_map : ∀ {X Y : σ.I → Type (max w u v)} (f : ∀ j, X j → Y j) {i} (z : σ.Obj X i),
      ofC (Obj.map f z) = map f (ofC z))
    (motive : ∀ i, σ.Intype i → Prop)
    (H : ∀ i (y : F σ.Intype i), Data.All map motive y → motive i (ctorI (toC y)))
    {i : σ.I} (t : σ.Intype i) : motive i t :=
  rec_of toC ofC toC_ofC (motive := motive)
    (fun i y ih => H i y ⟨ofC ⟨(toC y).shape, fun b => ⟨(toC y).child b, ih b⟩⟩,
      (ofC_map _ _).symm.trans (ofC_toC y)⟩) t

end Codata.Signature

namespace Data

/-- The contract for an inductive family `T : I → Type u` and a functor `F` on families, given by
its action on functions with the functor laws: `(T, ctor)` is an algebra with a fold satisfying
its computation rule, and the induction principle holds for the canonical lifting `All map`. -/
structure Contract {I : Type w} (T : I → Type u) (F : (I → Type u) → I → Type u) where
  map {X Y : I → Type u} : (∀ j, X j → Y j) → ∀ {i}, F X i → F Y i
  map_id {X : I → Type u} {i : I} (a : F X i) : map (fun _ x => x) a = a
  map_comp {X Y Z : I → Type u} (g : ∀ j, Y j → Z j) (f : ∀ j, X j → Y j) {i : I} (a : F X i) :
    map (fun j x => g j (f j x)) a = map g (map f a)
  ctor {i : I} : F T i → T i
  fold {S : I → Type u} : (∀ i, F S i → S i) → ∀ {i}, T i → S i
  fold_ctor {S : I → Type u} (a : ∀ i, F S i → S i) {i : I} (y : F T i) :
    fold a (ctor y) = a i (map (fun _ t => fold a t) y)
  induction (motive : ∀ i, T i → Prop)
    (H : ∀ i (y : F T i), All map motive y → motive i (ctor y)) {i : I} (t : T i) : motive i t

namespace Contract

variable {I : Type w} {T : I → Type u} {F : (I → Type u) → I → Type u} (K : Contract T F)

/-- The image of a value under a function into `P` satisfies `All P`. -/
theorem all_map {X Y : I → Type u} (P : ∀ j, Y j → Prop) (f : ∀ j, X j → Y j) {i : I}
    (a : F X i) (h : ∀ j x, P j (f j x)) : All K.map P (K.map f a) :=
  ⟨K.map (fun j x => ⟨f j x, h j x⟩) a, by simp only [← K.map_comp]⟩

/-- The destructor, by Lambek's lemma. -/
def dtor {i : I} (t : T i) : F T i := K.fold (fun _ y => K.map (fun _ y => K.ctor y) y) t

theorem ctor_dtor {i : I} (t : T i) : K.ctor (K.dtor t) = t := by
  refine K.induction (fun _ t => K.ctor (K.dtor t) = t) ?_ t
  rintro i y ⟨z, rfl⟩
  show K.ctor (K.fold _ (K.ctor _)) = _
  rw [K.fold_ctor, ← K.map_comp, ← K.map_comp]
  exact congrArg K.ctor (congrArg (fun f => K.map f z) (funext fun _ => funext fun x => x.2))

theorem dtor_ctor {i : I} (y : F T i) : K.dtor (K.ctor y) = y := by
  show K.fold _ (K.ctor y) = y
  rw [K.fold_ctor, ← K.map_comp]
  have : (fun (_ : I) t => K.ctor (K.fold (fun _ y => K.map (fun _ y => K.ctor y) y) t)) =
      (fun (j : I) (t : T j) => t) := funext fun _ => funext fun t => K.ctor_dtor t
  rw [this, K.map_id]

theorem ctor_injective {i : I} : Function.Injective (K.ctor (i := i)) := fun a b h => by
  rw [← K.dtor_ctor a, ← K.dtor_ctor b, h]

end Contract

section
variable {I : Type w} {T : I → Type u} {S : I → Type u₃} {FS : I → Type u₁} {FT : I → Type u₂}

/-- `fold_eq`, from `fold_ctor` and `ctor_dtor`. -/
theorem fold_eq_of (dtor : ∀ {i}, T i → FT i) (ctor : ∀ {i}, FT i → T i)
    (fold : (∀ i, FS i → S i) → ∀ {i}, T i → S i)
    (map : (∀ j, T j → S j) → ∀ {i}, FT i → FS i)
    (fold_ctor : ∀ (a : ∀ i, FS i → S i) {i} (y : FT i),
      fold a (ctor y) = a i (map (fun _ t => fold a t) y))
    (ctor_dtor : ∀ {i} (t : T i), ctor (dtor t) = t) (a : ∀ i, FS i → S i) {i : I} (t : T i) :
    fold a t = a i (map (fun _ t => fold a t) (dtor t)) := by
  have h := fold_ctor a (dtor t)
  rwa [ctor_dtor] at h

/-- Uniqueness of `fold`, from `induction`. -/
theorem fold_unique_of {F : (I → Type u) → I → Type u}
    (map : ∀ {X Y : I → Type u}, (∀ j, X j → Y j) → ∀ {i}, F X i → F Y i)
    (ctor : ∀ {i}, F T i → T i)
    (induction : ∀ (motive : ∀ i, T i → Prop),
      (∀ i (y : F T i), All map motive y → motive i (ctor y)) → ∀ {i} (t : T i), motive i t)
    (fold : (∀ i, FS i → S i) → ∀ {i}, T i → S i)
    (mapS : ∀ {X : I → Type u}, (∀ j, X j → S j) → ∀ {i}, F X i → FS i)
    (fold_ctor : ∀ (a : ∀ i, FS i → S i) {i} (y : F T i),
      fold a (ctor y) = a i (mapS (fun _ t => fold a t) y))
    (mapS_map : ∀ {X : I → Type u} (g : ∀ j, T j → S j) (f : ∀ j, X j → T j) {i} (z : F X i),
      mapS (fun j x => g j (f j x)) z = mapS g (map f z))
    (a : ∀ i, FS i → S i) (h : ∀ i, T i → S i)
    (hh : ∀ i (y : F T i), h i (ctor y) = a i (mapS h y)) {i : I} (t : T i) :
    h i t = fold a t := by
  refine induction (fun i t => h i t = fold a t) ?_ t
  rintro i y ⟨z, rfl⟩
  rw [hh, fold_ctor, ← mapS_map, ← mapS_map]
  exact congrArg (a i) (congrArg (fun f => mapS f z) (funext fun _ => funext fun x => x.2))

end

/-! ### The contract characterises `T`: it is the initial algebra of `(F, map)`

`fold_ctor` gives an algebra morphism into any algebra, `fold_unique` its uniqueness. So any two
implementations of the contract, for the same `map`, are isomorphic as algebras, by the `fold`s
in both directions. -/

namespace Contract

variable {I : Type w} {T : I → Type u} {F : (I → Type u) → I → Type u} (K : Contract T F)

/-- Uniqueness of algebra morphisms out of `T`. -/
theorem fold_unique {S : I → Type u} (a : ∀ i, F S i → S i) (h : ∀ i, T i → S i)
    (hh : ∀ i (y : F T i), h i (K.ctor y) = a i (K.map h y)) {i : I} (t : T i) :
    h i t = K.fold a t :=
  fold_unique_of K.map K.ctor K.induction K.fold K.map K.fold_ctor
    (fun {_} g f {_} z => K.map_comp g f z) a h hh t

/-- The identity is the algebra morphism `T → T`. -/
theorem fold_ctor_self {i : I} (t : T i) : K.fold (fun _ y => K.ctor y) t = t :=
  (K.fold_unique (fun _ y => K.ctor y) (fun _ t => t)
    (fun _ y => (congrArg K.ctor (K.map_id y)).symm) t).symm

variable {T' : I → Type u} (K' : Contract T' F)

/-- Two implementations of the contract for the same functor are inverse to each other through
their folds: `T` and `T'` are isomorphic, as algebras. The other composite is this theorem with
the roles exchanged. -/
theorem fold_fold (hmap : ∀ {X Y : I → Type u} (f : ∀ j, X j → Y j) {i} (a : F X i),
      K.map f a = K'.map f a) {i : I} (t : T i) :
    K'.fold (fun _ y => K.ctor y) (K.fold (fun _ y => K'.ctor y) t) = t := by
  refine (K.fold_unique (fun _ y => K.ctor y)
    (fun _ t => K'.fold (fun _ y => K.ctor y) (K.fold (fun _ y => K'.ctor y) t)) ?_ t).trans
    (K.fold_ctor_self t)
  intro i y
  rw [K.fold_ctor, K'.fold_ctor, ← hmap, ← K.map_comp]

end Contract

end Data
