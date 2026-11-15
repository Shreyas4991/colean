import Colean.Model.Cotype
import Colean.Model.Occ

/-!
# The model: a chain-complete partial order on a coinductive type

*Spec.* Input: a contract `K : Contract T F` (`Framework.lean`), a presentation of `F` as the
container functor of a signature `σ` (`Container`: `toC`, `ofC`, natural, inverse to each other,
which the generated types have), and a *bottom layer* `e i : F T i` at every index, without
recursive positions (a constructor without arguments). Output: the order of approximation on
`T i` with `K.ctor (e i)` at the bottom (`Approx`), the supremum of a chain (`csup`, by
`corec`), and Lean's `Lean.Order.CCPO (T i)` (`ccpo`), which `partial_fixpoint` needs on the
result type of a definition. Also what definitions by `partial_fixpoint` and proofs about them
need: the constructor is monotone (`approx_ctor`, `monotone_ctor`), the order unfolded once and
coinduction for it with a lifting equivalent to the canonical one (`ccpo_rel_iff_of`,
`ccpo_coind_of`, for the generated `T.F.Rel`), the bottom of the `CCPO` is the bottom layer
(`bot_eq`), and being below an element is admissible, for fixpoint induction
(`Codata.admissible_rel`). Last, the order on a nested argument through its occurrence structure
(`Occ.order`), and the monotonicity for it of the maps and the constructors of the library's
leaves, and of the pairs of a product.

The order is coinductive: `x ⊑ y` when `x` is the bottom, or `dtor x` and `dtor y` are related
by the canonical lifting `Rel K.map` of the order itself (same constructor, equal data, related
recursive arguments; nested arguments through their positions). It is defined from the contract
and the bottom layer alone, as the greatest such relation. That it is a partial order, and that
chains have suprema, needs the positions of a layer (the lifting of a functor given only by its
action on functions need not preserve intersections or compositions of relations); this is what
`Container` gives, and it is the only thing the theory takes beyond the contract. Antisymmetry is
`bisim`; the supremum of a chain is the bottom if every element is, and otherwise the common
constructor and data of the other elements, with the suprema of the chains of their children
position by position, built by `corec` on sets of elements. It is noncomputable.

The construction follows the one of `CoInd F` in the ISTA-PLV `coinductive` library (Apache 2.0),
on the contract instead of a representation by approximations.
-/

universe w s b u v

namespace Codata

open Lean.Order

section Order

variable {I : Type w} {T : I → Type u} {F : (I → Type u) → I → Type u}

namespace Contract

variable (K : Contract T F)

/-! ### The order, from the contract -/

/-- The canonical lifting is monotone in the relation. -/
theorem rel_mono {X Y : I → Type u} {R S : ∀ j, X j → Y j → Prop} {i : I} {a : F X i}
    {c : F Y i} (h : Rel K.map R a c) (hRS : ∀ j x y, R j x y → S j x y) : Rel K.map S a c := by
  obtain ⟨z, rfl, rfl⟩ := h
  exact ⟨K.map (fun j p => ⟨p.1, hRS j _ _ p.2⟩) z, (K.map_comp _ _ z).symm,
    (K.map_comp _ _ z).symm⟩

/-- Equality is related to itself by the canonical lifting. -/
theorem rel_eq {X : I → Type u} {i : I} (a : F X i) :
    Rel K.map (fun _ x y => x = y) a a := by
  have h := K.rel_map (fun _ x y => x = y) (fun _ x => x) (fun _ x => x) a fun _ _ => rfl
  rwa [K.map_id] at h

variable (e : ∀ i, F T i)

/-- The order of approximation with `K.ctor (e i)` at the bottom: `x ⊑ y` when `x` is the bottom,
or `dtor x` and `dtor y` are related by the canonical lifting of the order; the greatest such
relation. -/
def Approx {i : I} (x y : T i) : Prop :=
  ∃ R : ∀ j, T j → T j → Prop,
    (∀ j x y, R j x y → x = K.ctor (e j) ∨ Rel K.map R (K.dtor x) (K.dtor y)) ∧ R i x y

/-- Coinduction for the order: a relation whose pairs are the bottom on the left, or related by
the lifting of the relation, is contained in the order. -/
theorem approx_coind (R : ∀ j, T j → T j → Prop)
    (H : ∀ j x y, R j x y → x = K.ctor (e j) ∨ Rel K.map R (K.dtor x) (K.dtor y)) {i : I}
    {x y : T i} (h : R i x y) : Approx K e x y :=
  ⟨R, H, h⟩

/-- The order unfolded once. -/
theorem approx_iff {i : I} {x y : T i} :
    Approx K e x y ↔
      x = K.ctor (e i) ∨ Rel K.map (fun j => Approx K e (i := j)) (K.dtor x) (K.dtor y) := by
  constructor
  · rintro ⟨R, hR, h⟩
    exact (hR i x y h).imp_right fun h => K.rel_mono h fun j x y h => ⟨R, hR, h⟩
  · intro h
    refine ⟨fun j x y => Approx K e x y ∨ (x = K.ctor (e j) ∨
      Rel K.map (fun j => Approx K e (i := j)) (K.dtor x) (K.dtor y)), ?_, Or.inr h⟩
    rintro j x y (⟨R, hR, h⟩ | h)
    · exact (hR j x y h).imp_right fun h => K.rel_mono h fun j x y h => Or.inl ⟨R, hR, h⟩
    · exact h.imp_right fun h => K.rel_mono h fun j x y h => Or.inl h

/-- The order is reflexive. -/
theorem approx_refl {i : I} (x : T i) : Approx K e x x :=
  K.approx_coind e (fun _ x y => x = y) (fun _ _ _ h => h ▸ Or.inr (K.rel_eq _)) rfl

/-- The bottom is below everything. -/
theorem bot_approx {i : I} (x : T i) : Approx K e (K.ctor (e i)) x :=
  (K.approx_iff e).2 (Or.inl rfl)

/-- Constructors are monotone: related layers give related values. -/
theorem approx_ctor {i : I} {a c : F T i}
    (h : Rel K.map (fun j => Approx K e (i := j)) a c) : Approx K e (K.ctor a) (K.ctor c) :=
  (K.approx_iff e).2 (Or.inr (by rw [K.dtor_ctor, K.dtor_ctor]; exact h))

end Contract

end Order

variable {σ : Signature.{w, s, b}} {T : σ.I → Type u} {F : (σ.I → Type u) → σ.I → Type u}

namespace Contract

variable (σ) in
/-- A presentation of the functor `F` of a contract as the container functor of the signature
`σ`: an isomorphism `F X i ≃ σ.Obj X i`, natural in the family `X`. The generated types have one,
`T.toC` and `T.ofC` with their laws. -/
structure Container (K : Contract T F) where
  toC {X : σ.I → Type u} {i : σ.I} : F X i → σ.Obj X i
  ofC {X : σ.I → Type u} {i : σ.I} : σ.Obj X i → F X i
  ofC_toC {X : σ.I → Type u} {i : σ.I} (a : F X i) : ofC (toC a) = a
  toC_ofC {X : σ.I → Type u} {i : σ.I} (z : σ.Obj X i) : toC (ofC z) = z
  ofC_map {X Y : σ.I → Type u} (f : ∀ j, X j → Y j) {i : σ.I} (z : σ.Obj X i) :
    ofC (Signature.Obj.map f z) = K.map f (ofC z)

variable (K : Contract T F) (e : ∀ i, F T i)

/-! ### The presentation as a container -/

namespace Container

variable {K} (C : Container σ K)

/-- The presentation is injective. -/
theorem toC_injective {X : σ.I → Type u} {i : σ.I} {a a' : F X i} (h : C.toC a = C.toC a') :
    a = a' := by
  rw [← C.ofC_toC a, h, C.ofC_toC]

/-- The presentation is natural. -/
theorem toC_map {X Y : σ.I → Type u} (f : ∀ j, X j → Y j) {i : σ.I} (a : F X i) :
    C.toC (K.map f a) = Signature.Obj.map f (C.toC a) := by
  have h := congrArg C.toC (C.ofC_map f (C.toC a))
  rwa [C.toC_ofC, C.ofC_toC, eq_comm] at h

/-- The canonical lifting is the lifting of the container: same shape, related children. -/
theorem rel_iff {X Y : σ.I → Type u} {R : ∀ j, X j → Y j → Prop} {i : σ.I} {a : F X i}
    {c : F Y i} : Rel K.map R a c ↔ Signature.Obj.Rel R (C.toC a) (C.toC c) := by
  constructor
  · rintro ⟨z, rfl, rfl⟩
    rw [C.toC_map, C.toC_map]
    exact ⟨_, _, _, rfl, rfl, fun b => ((C.toC z).child b).2⟩
  · rintro ⟨sh, k, k', ha, hc, h⟩
    refine ⟨C.ofC ⟨sh, fun b => ⟨(k b, k' b), h b⟩⟩, ?_, ?_⟩ <;> dsimp only
    · rw [← C.ofC_map]
      exact (congrArg C.ofC ha.symm).trans (C.ofC_toC a)
    · rw [← C.ofC_map]
      exact (congrArg C.ofC hc.symm).trans (C.ofC_toC c)

/-- A lifting `Rel'` that the container's contains (for the generated types, the inductive
`T.F.Rel`, by `T.rel_ofC`) is contained in the canonical one. -/
theorem rel_of {Rel' : (∀ j, T j → T j → Prop) → ∀ {i}, F T i → F T i → Prop}
    (rel_ofC : ∀ (R : ∀ j, T j → T j → Prop) {i} (z z' : σ.Obj T i),
      Rel' R (C.ofC z) (C.ofC z') → Signature.Obj.Rel R z z')
    {R : ∀ j, T j → T j → Prop} {i : σ.I} {a c : F T i} (h : Rel' R a c) : Rel K.map R a c := by
  rw [← C.ofC_toC a, ← C.ofC_toC c] at h
  exact C.rel_iff.2 (rel_ofC R _ _ h)

/-- Two values are equal when their layers are. -/
theorem eq_iff {i : σ.I} {x y : T i} : x = y ↔ C.toC (K.dtor x) = C.toC (K.dtor y) :=
  ⟨fun h => h ▸ rfl, fun h => by rw [← K.ctor_dtor x, ← K.ctor_dtor y, C.toC_injective h]⟩

end Container

/-! ### A partial order -/

variable {K} (C : Container σ K) {e}
  (hbot : ∀ i, σ.B i (C.toC (e i)).shape → False)

include hbot in
/-- A map does not change the bottom layer, which has no positions. -/
theorem map_bot (f : ∀ j, T j → T j) (i : σ.I) : K.map f (e i) = e i := by
  refine C.toC_injective ?_
  rw [C.toC_map]
  exact congrArg (Signature.Obj.mk _) (funext fun b => (hbot i b).elim)

include hbot in
/-- Only the bottom is below the bottom. -/
theorem eq_bot_of_approx {i : σ.I} {x : T i} (h : Approx K e x (K.ctor (e i))) :
    x = K.ctor (e i) := by
  refine ((K.approx_iff e).1 h).elim id fun h => ?_
  rw [C.rel_iff, K.dtor_ctor] at h
  obtain ⟨sh, k, k', hx, he, -⟩ := h
  have hk : k = k' := funext fun b => (hbot i (he ▸ b)).elim
  subst hk
  exact C.eq_iff.2 (by rw [K.dtor_ctor, hx, he])

include hbot in
/-- The order is transitive. -/
theorem approx_trans {i : σ.I} {x y z : T i} (h₁ : Approx K e x y) (h₂ : Approx K e y z) :
    Approx K e x z := by
  refine K.approx_coind e (fun _ x z => ∃ y, Approx K e x y ∧ Approx K e y z) ?_ ⟨y, h₁, h₂⟩
  rintro j x z ⟨y, h₁, h₂⟩
  rcases (K.approx_iff e).1 h₁ with hx | r₁
  · exact Or.inl hx
  rcases (K.approx_iff e).1 h₂ with hy | r₂
  · subst hy
    exact Or.inl (eq_bot_of_approx C hbot h₁)
  right
  rw [C.rel_iff] at r₁ r₂ ⊢
  obtain ⟨sh, k, k', hx, hy, hk⟩ := r₁
  obtain ⟨sh', l, l', hy', hz, hl⟩ := r₂
  rw [hy] at hy'
  cases hy'
  exact ⟨sh, k, l', hx, hz, fun b => ⟨k' b, hk b, hl b⟩⟩

include hbot in
/-- The order is antisymmetric, by `bisim`. -/
theorem approx_antisymm {i : σ.I} {x y : T i} (h₁ : Approx K e x y) (h₂ : Approx K e y x) :
    x = y := by
  refine K.bisim (fun _ x y => Approx K e x y ∧ Approx K e y x) ?_ ⟨h₁, h₂⟩
  rintro j x y ⟨h₁, h₂⟩
  have hbb : Rel K.map (fun _ x y => Approx K e x y ∧ Approx K e y x)
      (K.dtor (K.ctor (e j))) (K.dtor (K.ctor (e j))) := by
    rw [C.rel_iff]
    exact ⟨_, _, _, rfl, rfl, fun b => (hbot j (by rwa [K.dtor_ctor] at b)).elim⟩
  rcases (K.approx_iff e).1 h₁ with hx | r₁
  · subst hx
    rw [eq_bot_of_approx C hbot h₂]
    exact hbb
  rcases (K.approx_iff e).1 h₂ with hy | r₂
  · subst hy
    rw [eq_bot_of_approx C hbot h₁]
    exact hbb
  rw [C.rel_iff] at r₁ r₂ ⊢
  obtain ⟨sh, k, k', hx, hy, hk⟩ := r₁
  obtain ⟨sh', l, l', hy', hx', hl⟩ := r₂
  rw [hx] at hx'
  rw [hy] at hy'
  cases hx'
  cases hy'
  exact ⟨sh, k, k', hx, hy, fun b => ⟨hk b, hl b⟩⟩

/-! ### Suprema of chains -/

variable (K e) in
/-- The children at the position `b` of the elements of `c` other than the bottom whose shape is
`sh`. -/
def Kids {i : σ.I} (c : T i → Prop) (sh : σ.Shape i) (b : σ.B i sh) (y : T (σ.idx b)) : Prop :=
  ∃ x k, c x ∧ x ≠ K.ctor (e i) ∧ C.toC (K.dtor x) = ⟨sh, k⟩ ∧ k b = y

variable (K e) in
open Classical in
/-- One step of the supremum of a set `c`: the bottom layer when `c` has no other element, and
otherwise the shape of its other elements, with the sets of their children at its positions. -/
noncomputable def supStep (i : σ.I) (c : T i → Prop) : F (fun j => T j → Prop) i :=
  if h : ∃ x, c x ∧ x ≠ K.ctor (e i) then
    C.ofC ⟨(C.toC (K.dtor h.choose)).shape, Kids K e C c _⟩
  else K.map (Y := fun j => T j → Prop) (fun _ _ _ => False) (e i)

variable (K e) in
/-- The supremum of a set, a chain in `csup_spec`: by corecursion on sets of elements. -/
noncomputable def csup {i : σ.I} (c : T i → Prop) : T i := K.corec (supStep K e C) c

/-- A chain for the order. -/
abbrev IsChain {i : σ.I} (c : T i → Prop) : Prop :=
  ∀ x y, c x → c y → Approx K e x y ∨ Approx K e y x

/-- Two elements of a chain other than the bottom have the same shape. -/
theorem shape_eq {i : σ.I} {c : T i → Prop} (hc : IsChain (K := K) (e := e) c) {x y : T i}
    (hx : c x) (hy : c y) (hx' : x ≠ K.ctor (e i)) (hy' : y ≠ K.ctor (e i)) :
    (C.toC (K.dtor x)).shape = (C.toC (K.dtor y)).shape := by
  rcases hc x y hx hy with h | h
  · obtain ⟨sh, k, k', h, h', -⟩ :=
      C.rel_iff.1 (((K.approx_iff e).1 h).resolve_left hx')
    rw [h, h']
  · obtain ⟨sh, k, k', h, h', -⟩ :=
      C.rel_iff.1 (((K.approx_iff e).1 h).resolve_left hy')
    rw [h, h']

/-- The children of a chain at one position form a chain. -/
theorem kids_chain {i : σ.I} {c : T i → Prop} (hc : IsChain (K := K) (e := e) c)
    (sh : σ.Shape i) (b : σ.B i sh) : IsChain (K := K) (e := e) (Kids K e C c sh b) := by
  rintro _ _ ⟨x, k, hx, hx', hkx, rfl⟩ ⟨y, l, hy, hy', hly, rfl⟩
  rcases hc x y hx hy with h | h
  · obtain ⟨sh₁, k₁, l₁, h, h', hk⟩ :=
      C.rel_iff.1 (((K.approx_iff e).1 h).resolve_left hx')
    rw [hkx] at h
    rw [hly] at h'
    cases h
    cases h'
    exact Or.inl (hk b)
  · obtain ⟨sh₁, l₁, k₁, h, h', hk⟩ :=
      C.rel_iff.1 (((K.approx_iff e).1 h).resolve_left hy')
    rw [hly] at h
    rw [hkx] at h'
    cases h
    cases h'
    exact Or.inr (hk b)

/-- The supremum of a chain with an element other than the bottom, of shape `sh`: the suprema of
the children at the positions of `sh`. -/
theorem toC_dtor_csup {i : σ.I} {c : T i → Prop} (hc : IsChain (K := K) (e := e) c) {x : T i}
    (hx : c x) (hx' : x ≠ K.ctor (e i)) {sh : σ.Shape i} {k : (b : σ.B i sh) → T (σ.idx b)}
    (hk : C.toC (K.dtor x) = ⟨sh, k⟩) :
    C.toC (K.dtor (csup K e C c)) = ⟨sh, fun b => csup K e C (Kids K e C c sh b)⟩ := by
  have h : ∃ x, c x ∧ x ≠ K.ctor (e i) := ⟨x, hx, hx'⟩
  have hsh : (C.toC (K.dtor h.choose)).shape = sh := by
    rw [shape_eq C hc h.choose_spec.1 hx h.choose_spec.2 hx', hk]
  rw [csup, K.dtor_corec, supStep, dite_eq_left h, ← C.ofC_map, C.toC_ofC]
  subst hsh
  rfl

include hbot in
/-- The supremum of a set with no element but the bottom is the bottom. -/
theorem csup_eq_bot {i : σ.I} {c : T i → Prop} (h : ¬∃ x, c x ∧ x ≠ K.ctor (e i)) :
    csup K e C c = K.ctor (e i) := by
  rw [← K.ctor_dtor (csup K e C c), csup, K.dtor_corec, supStep, dite_eq_right h, ← K.map_comp,
    map_bot C hbot]

/-- An element of a chain is below its supremum. -/
theorem approx_csup {i : σ.I} {c : T i → Prop} (hc : IsChain (K := K) (e := e) c) {y : T i}
    (hy : c y) : Approx K e y (csup K e C c) := by
  refine K.approx_coind e (fun _ y w => ∃ c, IsChain (K := K) (e := e) c ∧ c y ∧
    w = csup K e C c) ?_ ⟨c, hc, hy, rfl⟩
  rintro j y _ ⟨c, hc, hy, rfl⟩
  by_cases hy' : y = K.ctor (e j)
  · exact Or.inl hy'
  right
  rw [C.rel_iff, toC_dtor_csup C hc hy hy' rfl]
  exact ⟨_, _, _, rfl, rfl, fun b => ⟨_, kids_chain C hc _ b, ⟨y, _, hy, hy', rfl, rfl⟩, rfl⟩⟩

include hbot in
/-- The supremum of a chain is below every upper bound. -/
theorem csup_approx {i : σ.I} {c : T i → Prop} (hc : IsChain (K := K) (e := e) c) {z : T i}
    (hz : ∀ y, c y → Approx K e y z) : Approx K e (csup K e C c) z := by
  refine K.approx_coind e (fun _ w z => ∃ c, IsChain (K := K) (e := e) c ∧ w = csup K e C c ∧
    ∀ y, c y → Approx K e y z) ?_ ⟨c, hc, rfl, hz⟩
  rintro j _ z ⟨c, hc, rfl, hz⟩
  rcases Classical.em (∃ x, c x ∧ x ≠ K.ctor (e j)) with ⟨x, hx, hx'⟩ | h
  · right
    obtain ⟨sh, k, k', hk, hk', -⟩ :=
      C.rel_iff.1 (((K.approx_iff e).1 (hz x hx)).resolve_left hx')
    rw [C.rel_iff, toC_dtor_csup C hc hx hx' hk]
    refine ⟨_, _, _, rfl, hk', fun b => ⟨_, kids_chain C hc _ b, rfl, ?_⟩⟩
    rintro _ ⟨y, l, hy, hy', hl, rfl⟩
    obtain ⟨sh₁, l₁, l', h, h', hl'⟩ :=
      C.rel_iff.1 (((K.approx_iff e).1 (hz y hy)).resolve_left hy')
    rw [hl] at h
    rw [hk'] at h'
    cases h
    cases h'
    exact hl' b
  · exact Or.inl (csup_eq_bot C hbot h)

/-! ### The chain-complete partial order -/

variable (K e) in
/-- The order of approximation as Lean's `PartialOrder`. -/
@[reducible] def partialOrder (i : σ.I) : Lean.Order.PartialOrder (T i) where
  rel := Approx K e
  rel_refl := K.approx_refl e _
  rel_trans := approx_trans C hbot
  rel_antisymm := approx_antisymm C hbot

variable (K e) in
/-- The order of approximation as Lean's `CCPO`, which `partial_fixpoint` needs on the result type
of a definition. -/
@[reducible] noncomputable def ccpo (i : σ.I) : CCPO (T i) where
  toPartialOrder := partialOrder K e C hbot i
  has_csup {c} hc := ⟨csup K e C c, fun _ =>
    ⟨fun h _ hy => approx_trans C hbot (approx_csup C hc hy) h, csup_approx C hbot hc⟩⟩

/-- The order of the `CCPO`, unfolded once. -/
theorem ccpo_rel_iff {i : σ.I} {x y : T i} :
    (ccpo K e C hbot i).rel x y ↔ x = K.ctor (e i) ∨
      Rel K.map (fun j => (ccpo K e C hbot j).rel) (K.dtor x) (K.dtor y) :=
  K.approx_iff e

/-- The order of the `CCPO`, unfolded once, with a lifting `Rel'` equivalent to the canonical one
(for the generated types, the inductive `T.F.Rel`, by `T.F.rel_map` and `T.rel_ofC`). -/
theorem ccpo_rel_iff_of {Rel' : (∀ j, T j → T j → Prop) → ∀ {i}, F T i → F T i → Prop}
    (rel_map : ∀ (R : ∀ j, T j → T j → Prop) {i}
      (z : F (fun j => {p : T j × T j // R j p.1 p.2}) i),
      Rel' R (K.map (fun _ p => p.1.1) z) (K.map (fun _ p => p.1.2) z))
    (rel_ofC : ∀ (R : ∀ j, T j → T j → Prop) {i} (z z' : σ.Obj T i),
      Rel' R (C.ofC z) (C.ofC z') → Signature.Obj.Rel R z z')
    {i : σ.I} {x y : T i} :
    (ccpo K e C hbot i).rel x y ↔ x = K.ctor (e i) ∨
      Rel' (fun j => (ccpo K e C hbot j).rel) (K.dtor x) (K.dtor y) := by
  rw [ccpo_rel_iff]
  refine or_congr_right ⟨fun ⟨z, hz, hz'⟩ => hz ▸ hz' ▸ rel_map _ z, C.rel_of rel_ofC⟩

/-- Coinduction for the order of the `CCPO`, up to the order, with a lifting `Rel'` contained in
the canonical one (for the generated types, the inductive `T.F.Rel`, by `T.rel_ofC`): a relation
whose pairs are ordered, or have layers related by the lifting of the relation or the order, is
contained in the order. -/
theorem ccpo_coind_of {Rel' : (∀ j, T j → T j → Prop) → ∀ {i}, F T i → F T i → Prop}
    (rel_ofC : ∀ (R : ∀ j, T j → T j → Prop) {i} (z z' : σ.Obj T i),
      Rel' R (C.ofC z) (C.ofC z') → Signature.Obj.Rel R z z')
    (R : ∀ j, T j → T j → Prop)
    (H : ∀ j x y, R j x y → (ccpo K e C hbot j).rel x y ∨
      Rel' (fun j x y => R j x y ∨ (ccpo K e C hbot j).rel x y) (K.dtor x) (K.dtor y))
    {i : σ.I} {x y : T i} (h : R i x y) : (ccpo K e C hbot i).rel x y := by
  refine K.approx_coind e (fun j x y => R j x y ∨ Approx K e x y) ?_ (Or.inl h)
  rintro j x y (h | h)
  · rcases H j x y h with h | h
    · exact ((K.approx_iff e).1 h).imp_right fun h => K.rel_mono h fun _ _ _ => Or.inr
    · exact Or.inr (C.rel_of rel_ofC h)
  · exact ((K.approx_iff e).1 h).imp_right fun h => K.rel_mono h fun _ _ _ => Or.inr

/-- The bottom of the `CCPO` is the bottom layer's value. -/
theorem bot_eq (i : σ.I) : @bot (T i) (ccpo K e C hbot i) = K.ctor (e i) :=
  approx_antisymm C hbot (@bot_le (T i) (ccpo K e C hbot i) _) (K.bot_approx e _)

/-- Being below an element is admissible, in any `CCPO`: fixpoint induction (`f.fixpoint_induct`
of a definition `f` by `partial_fixpoint`) proves that a definition is below an element, the
bottom for a definition that is not productive. -/
theorem _root_.Codata.admissible_rel {α : Sort v} [CCPO α] (y : α) :
    admissible fun x => x ⊑ y :=
  fun _ hc h => csup_le hc h

/-- A constructor applied to a monotone function is monotone, for the `CCPO`'s order: the
monotonicity lemmas of the constructors, for `partial_fixpoint`. -/
theorem monotone_ctor {γ : Sort v} [Lean.Order.PartialOrder γ] {i : σ.I} (f : γ → F T i)
    (hf : ∀ x y, x ⊑ y → Rel K.map (fun j => (ccpo K e C hbot j).rel) (f x) (f y)) :
    @monotone γ _ (T i) (ccpo K e C hbot i).toPartialOrder fun x => K.ctor (f x) :=
  fun x y h => K.approx_ctor e (hf x y h)

end Contract

/-! ### The order on a nested argument

A nested argument `cs : G T` (`List T`) is ordered by the lifting of the order through its
occurrence structure: the same shape, the contents ordered position by position. This is the
order of `T.F.Rel` on the argument, so a constructor is monotone in it; `partial_fixpoint` then
needs the monotonicity of the functions a definition applies there: for a leaf the maps
(`monotone_list_map`, `monotone_option_map`, `monotone_array_map`) and the constructors
(`monotone_list_cons`, `monotone_option_some`), and the pairs of a product
(`monotone_prod_mk`, …). -/

namespace Occ

universe p' g c

local notation "PO" => Lean.Order.PartialOrder

variable {Sh : Type s} {Pos : Sh → Type p'} {G : Type u → Type g} (o : Occ Sh Pos G)

/-- The order on `G X` through the occurrence structure `o`: the same shape, the contents
ordered. -/
@[reducible] def order {X : Type u} [PO X] : PO (G X) where
  rel := Rel o o fun x y => x ⊑ y
  rel_refl := rel_refl o (fun _ => PartialOrder.rel_refl) _
  rel_trans := by
    rintro x y z ⟨sh, c, c', hx, hy, h⟩ ⟨sh', d, d', hy', hz, h'⟩
    rw [hy] at hy'
    cases hy'
    exact ⟨sh, c, d', hx, hz, fun q => PartialOrder.rel_trans (h q) (h' q)⟩
  rel_antisymm := by
    rintro x y ⟨sh, c, c', hx, hy, h⟩ ⟨sh', d, d', hy', hx', h'⟩
    rw [hx] at hx'
    rw [hy] at hy'
    cases hx'
    cases hy'
    rw [← o.ofC_toC x, ← o.ofC_toC y, hx, hy]
    exact congrArg (fun c => o.ofC ⟨sh, c⟩)
      (funext fun q => PartialOrder.rel_antisymm (h q) (h' q))

/-- The map of a monotone function is monotone, for the order through the structure. -/
theorem monotone_map {X Y : Type u} [PO Y] {γ : Sort c} [PO γ] (a : G X) {f : γ → X → Y}
    (hf : monotone f) : @monotone γ _ (G Y) o.order fun x => map o o (f x) a :=
  fun x y h => rel_map o o o _ (f x) (f y) a fun z => hf x y h z

/-- `List.map` is monotone in the function, for the order through the list's structure. -/
@[partial_fixpoint_monotone]
theorem monotone_list_map {X Y : Type u} [PO Y] {γ : Sort c} [PO γ] (l : List X)
    {f : γ → X → Y} (hf : monotone f) :
    @monotone γ _ (List Y) list.order fun x => (l.map (f x)) := by
  have h := monotone_map list l hf
  simp only [map_list] at h
  exact h

/-- `Option.map` is monotone in the function, for the order through the option's structure. -/
@[partial_fixpoint_monotone]
theorem monotone_option_map {X Y : Type u} [PO Y] {γ : Sort c} [PO γ] (a : Option X)
    {f : γ → X → Y} (hf : monotone f) :
    @monotone γ _ (Option Y) option.order fun x => (a.map (f x)) := by
  have h := monotone_map option a hf
  simp only [map_option] at h
  exact h

/-- `Array.map` is monotone in the function, for the order through the array's structure. -/
@[partial_fixpoint_monotone]
theorem monotone_array_map {X Y : Type u} [PO Y] {γ : Sort c} [PO γ] (a : Array X)
    {f : γ → X → Y} (hf : monotone f) :
    @monotone γ _ (Array Y) array.order fun x => (a.map (f x)) := by
  have h := monotone_map array a hf
  simp only [map_array] at h
  exact h

/-! The constructors of the leaves and of products, for the recursive calls written out in a
nested argument (`[f (n + 1), f (n + 2)]`, `some (f n)`, `(f n, t)`); `[]` and `none` are
constants. A component that is the type itself (the structure's `hole`) is ordered by the type's
order, which is what `partial_fixpoint` proves a recursive call monotone in, so a product has a
lemma per place of the holes: the one with the holes first, since `partial_fixpoint` applies the
first lemma that fits. -/

/-- `List.cons` is monotone, for the order through the list's structure. -/
@[partial_fixpoint_monotone]
theorem monotone_list_cons {X : Type u} [PO X] {γ : Sort c} [PO γ] {f : γ → X}
    {g : γ → List X} (hf : monotone f) (hg : @monotone γ _ (List X) list.order g) :
    @monotone γ _ (List X) list.order fun x => f x :: g x :=
  fun x y h => (rel_list _ _).mpr (.cons (hf x y h) ((rel_list _ _).mp (hg x y h)))

/-- `Option.some` is monotone, for the order through the option's structure. -/
@[partial_fixpoint_monotone]
theorem monotone_option_some {X : Type u} [PO X] {γ : Sort c} [PO γ] {f : γ → X}
    (hf : monotone f) : @monotone γ _ (Option X) option.order fun x => some (f x) :=
  fun x y h => (rel_option _ _).mpr (.some (hf x y h))

section Prod

variable {X : Type u} [PO X] {γ : Sort c} [PO γ] {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p'}
  {Sh₂ : Type b} {Pos₂ : Sh₂ → Type w} {G₁ : Type u → Type g} {G₂ : Type u → Type v}

/-- A pair of two occurrences of the type is monotone in both, for the order through the
product's structure. -/
@[partial_fixpoint_monotone]
theorem monotone_prod_mk_hole {f g : γ → X} (hf : monotone f) (hg : monotone g) :
    @monotone γ _ (X × X) (prod hole hole).order fun x => (f x, g x) :=
  fun x y h => (rel_prod _ _ _ _ _ _).mpr ⟨rel_hole_intro (hf x y h), rel_hole_intro (hg x y h)⟩

/-- A pair with an occurrence of the type first is monotone, for the order through the
product's structure. -/
@[partial_fixpoint_monotone]
theorem monotone_prod_mk_hole_left (o₂ : Occ Sh₂ Pos₂ G₂) {f : γ → X} {g : γ → G₂ X}
    (hf : monotone f) (hg : @monotone γ _ (G₂ X) o₂.order g) :
    @monotone γ _ (X × G₂ X) (prod hole o₂).order fun x => (f x, g x) :=
  fun x y h => (rel_prod _ _ _ _ _ _).mpr ⟨rel_hole_intro (hf x y h), hg x y h⟩

/-- A pair with an occurrence of the type second is monotone, for the order through the
product's structure. -/
@[partial_fixpoint_monotone]
theorem monotone_prod_mk_hole_right (o₁ : Occ Sh₁ Pos₁ G₁) {f : γ → G₁ X} {g : γ → X}
    (hf : @monotone γ _ (G₁ X) o₁.order f) (hg : monotone g) :
    @monotone γ _ (G₁ X × X) (prod o₁ hole).order fun x => (f x, g x) :=
  fun x y h => (rel_prod _ _ _ _ _ _).mpr ⟨hf x y h, rel_hole_intro (hg x y h)⟩

/-- A pair is monotone in both components, each for the order through its structure. -/
@[partial_fixpoint_monotone]
theorem monotone_prod_mk (o₁ : Occ Sh₁ Pos₁ G₁) (o₂ : Occ Sh₂ Pos₂ G₂) {f : γ → G₁ X}
    {g : γ → G₂ X} (hf : @monotone γ _ (G₁ X) o₁.order f)
    (hg : @monotone γ _ (G₂ X) o₂.order g) :
    @monotone γ _ (G₁ X × G₂ X) (prod o₁ o₂).order fun x => (f x, g x) :=
  fun x y h => (rel_prod _ _ _ _ _ _).mpr ⟨hf x y h, hg x y h⟩

end Prod

end Occ

end Codata
