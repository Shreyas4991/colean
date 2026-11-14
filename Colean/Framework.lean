import Mathlib.Logic.Function.Basic

/-!
# The framework: contracts and what follows from them

*Spec.* Everything here is stated for an arbitrary functor `F` on families `I → Type u`, given
by its action on functions `map` with the two functor laws, and never looks at the shape of `F`
or at a model.

* `Codata.Rel map` and `Data.All map`: the canonical liftings of `F` to relations and to
  predicates, defined from `map` (a relation holds when the two sides are the projections of one
  value over related pairs; a predicate when the value is the projection of one over elements
  satisfying it).
* `Codata.Contract T F`: `dtor`, `corec`, `dtor_corec`, `bisim` for `Rel map`; the derived
  `ctor` (Lambek), `dtor_ctor`, `ctor_dtor`, `ctor_injective`, `corec_unique`,
  `corec_dtor_self`, `corec_corec` (two contracts for one functor are isomorphic).
* `Data.Contract T F`: `ctor`, `fold`, `fold_ctor`, `induction` for `All map`; the derived
  `dtor` (Lambek), `dtor_ctor`, `ctor_dtor`, `ctor_injective`, `fold_unique`, `fold_ctor_self`,
  `fold_fold`.
* The `_of` theorems (`bisim_canonical_of`, `corec_eq_of`, `corec_unique_of`, `fold_eq_of`,
  `fold_unique_of`) are the same derivations with the contract's fields as hypotheses, so that
  the command can instantiate them for its universe-polymorphic `corec`/`fold` (the contract
  structure fixes one universe).
* The last section holds three index-free lemmas for the surface layer (`cast_ctor_dtor`,
  `inj_of`, `ne_of`), and `rel_of_map_heq`, a lifting read along a map between equal families,
  for the bisimulation of the types of a block, one relation per type.

The contract is documented in `contract.md`; the decomposition in `architecture.md`.
-/

universe w u u₀ v u₁ u₂ u₃

namespace Codata

/-- The lifting of a functor `F` on families to relations, defined from its action on
functions: `a` and `b` are related when they are the two projections of one `F`-value over
`R`-related pairs. This is the only lifting for which `bisim` below is Park's coinduction
principle, so it is fixed here rather than left as a field of the contract. -/
def Rel {I : Type w} {F : (I → Type u) → I → Type u}
    (map : ∀ {X Y : I → Type u}, (∀ j, X j → Y j) → ∀ {i}, F X i → F Y i)
    {X Y : I → Type u} (R : ∀ j, X j → Y j → Prop) {i : I} (a : F X i) (b : F Y i) : Prop :=
  ∃ z : F (fun j => {p : X j × Y j // R j p.1 p.2}) i,
    map (fun _ p => p.1.1) z = a ∧ map (fun _ p => p.1.2) z = b

/-- The contract for an indexed family `T : I → Type u` and a functor `F` on families, given by
its action on functions with the functor laws: `(T, dtor)` is a coalgebra with a corecursor
satisfying its computation rule, and the coinduction principle holds for the canonical lifting
`Rel map`. -/
structure Contract {I : Type w} (T : I → Type u) (F : (I → Type u) → I → Type u) where
  map {X Y : I → Type u} : (∀ j, X j → Y j) → ∀ {i}, F X i → F Y i
  map_id {X : I → Type u} {i : I} (a : F X i) : map (fun _ x => x) a = a
  map_comp {X Y Z : I → Type u} (g : ∀ j, Y j → Z j) (f : ∀ j, X j → Y j) {i : I} (a : F X i) :
    map (fun j x => g j (f j x)) a = map g (map f a)
  dtor {i : I} : T i → F T i
  corec {S : I → Type u} : (∀ i, S i → F S i) → ∀ {i}, S i → T i
  dtor_corec {S : I → Type u} (c : ∀ i, S i → F S i) {i : I} (s : S i) :
    dtor (corec c s) = map (fun _ s => corec c s) (c i s)
  bisim (R : ∀ i, T i → T i → Prop) (H : ∀ i x y, R i x y → Rel map R (dtor x) (dtor y)) {i : I}
    {x y : T i} (h : R i x y) : x = y

namespace Contract

variable {I : Type w} {T : I → Type u} {F : (I → Type u) → I → Type u} (K : Contract T F)

/-- The images of one value under pointwise related functions are related. -/
theorem rel_map {X Y Z : I → Type u} (R : ∀ j, Y j → Z j → Prop) (f : ∀ j, X j → Y j)
    (g : ∀ j, X j → Z j) {i : I} (a : F X i) (h : ∀ j x, R j (f j x) (g j x)) :
    Rel K.map R (K.map f a) (K.map g a) :=
  ⟨K.map (fun j x => ⟨(f j x, g j x), h j x⟩) a, by simp only [← K.map_comp],
    by simp only [← K.map_comp]⟩

/-- The constructor, by Lambek's lemma. -/
def ctor {i : I} (y : F T i) : T i := K.corec (fun _ => K.map fun _ t => K.dtor t) y

theorem ctor_dtor {i : I} (t : T i) : K.ctor (K.dtor t) = t := by
  refine K.bisim (fun _ x y => x = K.ctor (K.dtor y)) ?_ rfl
  rintro i _ y rfl
  have h := K.rel_map (fun _ x y => x = K.ctor (K.dtor y))
    (fun _ t => K.corec (fun _ => K.map fun _ t => K.dtor t) (K.dtor t)) (fun _ t => t)
    (K.dtor y) fun _ _ => rfl
  rw [K.map_id] at h
  show Rel K.map _ (K.dtor (K.corec (fun _ => K.map fun _ t => K.dtor t) (K.dtor y))) (K.dtor y)
  rw [K.dtor_corec, ← K.map_comp]
  exact h

theorem dtor_ctor {i : I} (y : F T i) : K.dtor (K.ctor y) = y := by
  show K.dtor (K.corec (fun _ => K.map fun _ t => K.dtor t) y) = y
  rw [K.dtor_corec, ← K.map_comp]
  have : (fun (_ : I) t => K.corec (fun _ => K.map fun _ t => K.dtor t) (K.dtor t)) =
      (fun (j : I) (t : T j) => t) := funext fun _ => funext fun t => K.ctor_dtor t
  rw [this, K.map_id]

theorem ctor_injective {i : I} : Function.Injective (K.ctor (i := i)) := fun a b h => by
  rw [← K.dtor_ctor a, ← K.dtor_ctor b, h]

end Contract

/-- `bisim` for the canonical lifting, from `bisim` for a lifting `Rel'` that contains it (for
the command: the inductive `F.Rel`, which contains it by `F.rel_map`). -/
theorem bisim_canonical_of {I : Type w} {T : I → Type u} {F : (I → Type u) → I → Type u}
    (map : ∀ {X Y : I → Type u}, (∀ j, X j → Y j) → ∀ {i}, F X i → F Y i)
    (Rel' : ∀ {X Y : I → Type u}, (∀ j, X j → Y j → Prop) → ∀ {i}, F X i → F Y i → Prop)
    (rel_map : ∀ {X Y Z : I → Type u} (R : ∀ j, Y j → Z j → Prop) (f : ∀ j, X j → Y j)
      (g : ∀ j, X j → Z j) {i} (a : F X i), (∀ j x, R j (f j x) (g j x)) →
      Rel' R (map f a) (map g a))
    (dtor : ∀ {i}, T i → F T i)
    (bisim : ∀ (R : ∀ i, T i → T i → Prop), (∀ i x y, R i x y → Rel' R (dtor x) (dtor y)) →
      ∀ {i} {x y : T i}, R i x y → x = y)
    (R : ∀ i, T i → T i → Prop) (H : ∀ i x y, R i x y → Rel map R (dtor x) (dtor y)) {i : I}
    {x y : T i} (h : R i x y) : x = y :=
  bisim R (fun i x y hxy => by
    obtain ⟨z, hz, hz'⟩ := H i x y hxy
    rw [← hz, ← hz']
    exact rel_map R _ _ z fun _ p => p.2) h

section
variable {I : Type w} {T : I → Type u} {S : I → Type u₃} {FS : I → Type u₁} {FT : I → Type u₂}

/-- `corec_eq`, from `dtor_corec` and `ctor_dtor`. -/
theorem corec_eq_of (dtor : ∀ {i}, T i → FT i) (ctor : ∀ {i}, FT i → T i)
    (corec : (∀ i, S i → FS i) → ∀ {i}, S i → T i)
    (map : (∀ j, S j → T j) → ∀ {i}, FS i → FT i)
    (dtor_corec : ∀ (c : ∀ i, S i → FS i) {i} (s : S i),
      dtor (corec c s) = map (fun _ s => corec c s) (c i s))
    (ctor_dtor : ∀ {i} (t : T i), ctor (dtor t) = t) (c : ∀ i, S i → FS i) {i : I} (s : S i) :
    corec c s = ctor (map (fun _ s => corec c s) (c i s)) := by
  rw [← dtor_corec, ctor_dtor]

/-- Uniqueness of `corec`, from `bisim`. -/
theorem corec_unique_of (dtor : ∀ {i}, T i → FT i) (corec : (∀ i, S i → FS i) → ∀ {i}, S i → T i)
    (map : (∀ j, S j → T j) → ∀ {i}, FS i → FT i)
    (Rel : (∀ j, T j → T j → Prop) → ∀ {i}, FT i → FT i → Prop)
    (bisim : ∀ (R : ∀ i, T i → T i → Prop), (∀ i x y, R i x y → Rel R (dtor x) (dtor y)) →
      ∀ {i} {x y : T i}, R i x y → x = y)
    (dtor_corec : ∀ (c : ∀ i, S i → FS i) {i} (s : S i),
      dtor (corec c s) = map (fun _ s => corec c s) (c i s))
    (rel_map : ∀ (R : ∀ j, T j → T j → Prop) (f g : ∀ j, S j → T j) {i} (a : FS i),
      (∀ j x, R j (f j x) (g j x)) → Rel R (map f a) (map g a))
    (c : ∀ i, S i → FS i) (h : ∀ i, S i → T i) (hh : ∀ i (s : S i), dtor (h i s) = map h (c i s))
    {i : I} (s : S i) : h i s = corec c s := by
  refine bisim (fun i x y => ∃ s, x = h i s ∧ y = corec c s) ?_ ⟨s, rfl, rfl⟩
  rintro i _ _ ⟨s, rfl, rfl⟩
  rw [hh, dtor_corec]
  exact rel_map _ _ _ _ fun j s => ⟨s, rfl, rfl⟩

end

/-! ### The contract characterises `T`: it is the final coalgebra of `(F, map)`

`dtor_corec` gives a coalgebra morphism out of any coalgebra, `corec_unique` its uniqueness. So
any two implementations of the contract, for the same `map`, are isomorphic as coalgebras, by
the `corec`s in both directions. -/

namespace Contract

variable {I : Type w} {T : I → Type u} {F : (I → Type u) → I → Type u} (K : Contract T F)

/-- Uniqueness of coalgebra morphisms into `T`. -/
theorem corec_unique {S : I → Type u} (c : ∀ i, S i → F S i) (h : ∀ i, S i → T i)
    (hh : ∀ i (s : S i), K.dtor (h i s) = K.map h (c i s)) {i : I} (s : S i) :
    h i s = K.corec c s :=
  corec_unique_of K.dtor K.corec K.map (Rel K.map) K.bisim K.dtor_corec K.rel_map c h hh s

/-- The identity is the coalgebra morphism `T → T`. -/
theorem corec_dtor_self {i : I} (t : T i) : K.corec (fun _ t => K.dtor t) t = t :=
  (K.corec_unique (fun _ t => K.dtor t) (fun _ t => t) (fun _ _ => (K.map_id _).symm) t).symm

variable {T' : I → Type u} (K' : Contract T' F)

/-- Two implementations of the contract for the same functor are inverse to each other through
their corecursors: `T` and `T'` are isomorphic, as coalgebras. The other composite is this
theorem with the roles exchanged. -/
theorem corec_corec (hmap : ∀ {X Y : I → Type u} (f : ∀ j, X j → Y j) {i} (a : F X i),
      K.map f a = K'.map f a) {i : I} (t : T i) :
    K.corec (fun _ t => K'.dtor t) (K'.corec (fun _ t => K.dtor t) t) = t := by
  refine (K.corec_unique (fun _ t => K.dtor t)
    (fun _ t => K.corec (fun _ t => K'.dtor t) (K'.corec (fun _ t => K.dtor t) t)) ?_ t).trans
    (K.corec_dtor_self t)
  intro i t
  rw [K.dtor_corec, K'.dtor_corec, ← hmap, ← K.map_comp]

end Contract

/-! ### Lemmas that do not mention the index, used at a fixed index -/

section
variable {T : Type u} {FT : Type u₂}

/-- The computation rule of a case analysis defined by casting along `ctor_dtor`: on a
constructor the cast disappears. -/
theorem cast_ctor_dtor {motive : T → Sort v} (ctor : FT → T) (dtor : T → FT)
    (ctor_dtor : ∀ t, ctor (dtor t) = t) (dtor_ctor : ∀ y, dtor (ctor y) = y)
    (aux : ∀ y, motive (ctor y)) (y : FT) :
    (congrArg motive (ctor_dtor (ctor y))).mp (aux (dtor (ctor y))) = aux y := by
  have key : ∀ (z : FT) (h : ctor z = ctor y), z = y →
      (congrArg motive h).mp (aux z) = aux y := by
    intro z h hz
    subst hz
    rfl
  exact key _ (ctor_dtor (ctor y)) (dtor_ctor y)

/-- Injectivity of a derived constructor, in the form of the `injEq` lemma of `F`. -/
theorem inj_of (ctor : FT → T) (hinj : Function.Injective ctor) (a b : FT) {P : Prop}
    (h : (a = b) = P) : ctor a = ctor b ↔ P :=
  hinj.eq_iff.trans (Iff.of_eq h)

/-- Distinct constructors give distinct elements, through `dtor`. -/
theorem ne_of (dtor : T → FT) {x y : T} {a b : FT} (hx : dtor x = a) (hy : dtor y = b)
    (hab : a ≠ b) : x ≠ y :=
  fun h => hab (by rw [← hx, ← hy, h])

end

/-- A lifting of relations along a map from a family to an equal one that leaves every element
as it is: two values are related when their images are, by the same relation read in the other
family. For any functor with a map and its identity law, and any lifting. -/
theorem rel_of_map_heq {I : Type w} {F : (I → Type u) → I → Type v}
    (map : ∀ {X Y : I → Type u}, (∀ i, X i → Y i) → ∀ {i}, F X i → F Y i)
    (map_id : ∀ {X : I → Type u} {i} (a : F X i), map (fun _ x => x) a = a)
    (Rel : ∀ {X : I → Type u}, (∀ i, X i → X i → Prop) → ∀ {i}, F X i → F X i → Prop)
    {X Y : I → Type u} (h : X = Y) (f : ∀ i, X i → Y i) (hf : ∀ i x, HEq (f i x) x)
    {R : ∀ i, X i → X i → Prop} {R' : ∀ i, Y i → Y i → Prop}
    (hR : ∀ i x y, R i x y ↔ R' i (f i x) (f i y)) {i : I} {a b : F X i}
    (hr : Rel R' (map f a) (map f b)) : Rel R a b := by
  subst h
  obtain rfl : f = fun _ x => x := funext fun i => funext fun x => eq_of_heq (hf i x)
  obtain rfl : R = R' := funext fun i => funext fun x => funext fun y => propext (hR i x y)
  rwa [map_id, map_id] at hr

end Codata

namespace Data

/-- The lifting of a functor on families to predicates, defined from its action on functions:
`a` satisfies `All P` when it is the projection of an `F`-value over elements satisfying `P`.
For a polynomial functor this says that every recursive argument satisfies `P`. -/
def All {I : Type w} {F : (I → Type u) → I → Type u}
    (map : ∀ {X Y : I → Type u}, (∀ j, X j → Y j) → ∀ {i}, F X i → F Y i)
    {X : I → Type u} (P : ∀ j, X j → Prop) {i : I} (a : F X i) : Prop :=
  ∃ z : F (fun j => {x : X j // P j x}) i, map (fun _ x => x.1) z = a

end Data

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
