import Mathlib.Logic.Function.Basic
import MetricCorec.Subtypes.Raw

/-!
# Generic theory behind `codata`

A `codata` declaration is a *signature*, a polynomial functor: the non-recursive data of the
constructors (the *shapes*) and, for each shape, its positions for recursive arguments. The
command generates the positions as an inductive family indexed by shapes, one nullary constructor
per plain recursive argument and one unary constructor per argument under a function type, whose
domain may depend on the shape (`Vis {X} (e : E X) (k : X → T)` has positions `X`). Everything
the contract asks for is built here once, generically over a signature `σ`, for the container
functor `σ.Obj X = { shape : σ.Shape, child : σ.B shape → X }`:

* `Signature.Cotype σ`: the subtype of `Raw σ.Idx σ.Shape` cut out by the greatest fixpoint
  `IsWf`, where path indices are a shape with one of its positions. Placing `empty` at the
  indices of the other shapes decides equality of shapes, classically: `corec` and the
  constructors are noncomputable, which is accepted here;
* `dtorC`, `corecC`, `dtorC_corecC`, `bisimC`: the contract for `σ.Obj`.

The command generates, for its user-facing functor `F` (the constructor list as an inductive
type), an isomorphism `toC`/`ofC` between `F` and `σ.Obj` with the three laws `ofC_toC`,
`ofC_map`, `rel_ofC`, and instantiates the transport theorems `dtor_corec_of` and `bisim_of`.
These take the concrete pieces as hypotheses rather than an abstract functor `F`: a bound
functor variable lives in one universe, while `corec` must accept states in any universe, so the
hypotheses mention `F S` and `F T` as two separate types.

The section `Codata.Contract` derives the constructors from the contract alone, and the `_of`
theorems after it derive `corec_eq`, `corec_unique`, the computation rule of case analysis,
injectivity and disjointness of constructors, again from the contract, for the command to
instantiate.
-/

universe u v w u₁ u₂

/-- A signature: the non-recursive data of the constructors (the *shapes*) and, for each shape,
its positions for recursive arguments. This is a polynomial functor `A, B`. -/
structure Signature where
  Shape : Type u
  B : Shape → Type v

namespace Signature

variable (σ : Signature.{u, v})

/-- The indices of children in the encoding: a shape and one of its positions. -/
abbrev Idx : Type (max u v) := Σ s : σ.Shape, σ.B s

/-- The container functor of a signature: a constructor with its data, and its recursive
arguments. -/
structure Obj (X : Type u₁) : Type (max u v u₁) where
  shape : σ.Shape
  child : σ.B shape → X

variable {σ} {X : Type u₁} {Y : Type u₂} {S : Type w}

namespace Obj

/-- The action on functions. -/
def map (f : X → Y) (z : σ.Obj X) : σ.Obj Y := ⟨z.shape, fun b => f (z.child b)⟩

/-- The lifting to relations: same constructor and data, related recursive arguments. -/
abbrev Rel (R : X → Y → Prop) (z : σ.Obj X) (z' : σ.Obj Y) : Prop :=
  ∃ (s : σ.Shape) (c : σ.B s → X) (c' : σ.B s → Y),
    z = ⟨s, c⟩ ∧ z' = ⟨s, c'⟩ ∧ ∀ b, R (c b) (c' b)

end Obj

/-! ### Encoding one layer into `Raw`

The children of a node sit at the indices `⟨s, b⟩` of its own shape `s`, and `empty` sits at the
indices of the other shapes. Telling the two apart decides equality of shapes, classically: the
encoding, hence `corec` and the constructors, is noncomputable. -/

open Classical in
/-- One layer of a tree. -/
noncomputable def encode (z : σ.Obj (Raw σ.Idx σ.Shape)) : Raw σ.Idx σ.Shape :=
  Raw.mk (some z.shape) fun i => if h : i.1 = z.shape then z.child (h ▸ i.2) else Raw.empty

@[simp] theorem root_encode (z : σ.Obj (Raw σ.Idx σ.Shape)) : (encode z).root = some z.shape :=
  rfl

theorem child_encode_self (z : σ.Obj (Raw σ.Idx σ.Shape)) (b : σ.B z.shape) :
    (encode z).child ⟨z.shape, b⟩ = z.child b :=
  dif_pos rfl

theorem child_encode_of_ne (z : σ.Obj (Raw σ.Idx σ.Shape)) {s : σ.Shape} (h : s ≠ z.shape)
    (b : σ.B s) : (encode z).child ⟨s, b⟩ = Raw.empty :=
  dif_neg h

/-! ### The predicate and the type -/

/-- Well-formed trees: every node is a layer whose children are well-formed. The greatest
fixpoint. -/
def IsWf (t : Raw σ.Idx σ.Shape) : Prop :=
  ∃ z : σ.Obj (Raw σ.Idx σ.Shape), t = encode z ∧ ∀ b, IsWf (z.child b)
coinductive_fixpoint

/-- The coinductive type of a signature. -/
def Cotype (σ : Signature.{u, v}) : Type (max u v) := {t : Raw σ.Idx σ.Shape // IsWf t}

theorem IsWf.root_ne_none {t : Raw σ.Idx σ.Shape} (h : IsWf t) : t.root ≠ none := by
  rw [IsWf.eq_def] at h
  obtain ⟨z, rfl, -⟩ := h
  simp

theorem IsWf.child {t : Raw σ.Idx σ.Shape} (h : IsWf t) {s : σ.Shape} (hs : t.root = some s)
    (b : σ.B s) : IsWf (t.child ⟨s, b⟩) := by
  rw [IsWf.eq_def] at h
  obtain ⟨z, rfl, hz⟩ := h
  obtain rfl : s = z.shape := (Option.some.inj hs).symm
  rw [child_encode_self]
  exact hz b

theorem IsWf.child_eq_empty {t : Raw σ.Idx σ.Shape} (h : IsWf t) {s : σ.Shape}
    (hs : t.root = some s) {s' : σ.Shape} (hne : s' ≠ s) (b : σ.B s') :
    t.child ⟨s', b⟩ = Raw.empty := by
  rw [IsWf.eq_def] at h
  obtain ⟨z, rfl, -⟩ := h
  obtain rfl : s = z.shape := (Option.some.inj hs).symm
  exact child_encode_of_ne z hne b

/-- A well-formed tree is the layer made of its root and its children. -/
theorem IsWf.eq_encode {t : Raw σ.Idx σ.Shape} (h : IsWf t) {s : σ.Shape} (hs : t.root = some s) :
    t = encode ⟨s, fun b => t.child ⟨s, b⟩⟩ := by
  refine Raw.ext_root_child hs fun ⟨s', b⟩ => ?_
  by_cases hs' : s' = s
  · subst hs'
    exact (child_encode_self ⟨s', fun b => t.child ⟨s', b⟩⟩ b).symm
  · rw [child_encode_of_ne _ hs', h.child_eq_empty hs hs']

/-! ### The destructor -/

/-- The shape at the root, which `IsWf` guarantees to exist. -/
def rootShape (t : σ.Cotype) : σ.Shape :=
  match h : t.1.root with
  | some s => s
  | none => absurd h t.2.root_ne_none

theorem root_eq (t : σ.Cotype) : t.1.root = some (rootShape t) := by
  unfold rootShape
  split
  · assumption
  · exact absurd ‹_› t.2.root_ne_none

/-- The destructor on the container: the root shape, and the children as elements of the
type. -/
def dtorC (t : σ.Cotype) : σ.Obj σ.Cotype :=
  ⟨rootShape t, fun b => ⟨t.1.child ⟨rootShape t, b⟩, t.2.child (root_eq t) b⟩⟩

/-- The tree is the layer of its destructor. -/
theorem val_eq_encode_dtorC (t : σ.Cotype) : t.1 = encode (Obj.map Subtype.val (dtorC t)) :=
  t.2.eq_encode (root_eq t)

/-! ### The corecursor -/

open Classical in
/-- The coalgebra on `Option S` underlying `corecRaw`: `none` is the state of `empty`. -/
noncomputable def coalg (c : S → σ.Obj S) : Option S → Option σ.Shape × (σ.Idx → Option S)
  | none => (none, fun _ => none)
  | some s =>
    (some (c s).shape,
      fun i => if h : i.1 = (c s).shape then some ((c s).child (h ▸ i.2)) else none)

/-- Unfolding a coalgebra into `Raw`. -/
noncomputable def corecRaw (c : S → σ.Obj S) (s : S) : Raw σ.Idx σ.Shape :=
  Raw.corec (coalg c) (some s)

theorem corec_coalg_none (c : S → σ.Obj S) : Raw.corec (coalg c) none = Raw.empty :=
  Raw.eq_of_bisim (R := fun t₁ t₂ => t₁ = Raw.corec (coalg c) none ∧ t₂ = Raw.empty)
    (by rintro _ _ ⟨rfl, rfl⟩; exact ⟨rfl, fun i => ⟨rfl, rfl⟩⟩) ⟨rfl, rfl⟩

@[simp] theorem root_corecRaw (c : S → σ.Obj S) (s : S) :
    (corecRaw c s).root = some (c s).shape := rfl

open Classical in
theorem corecRaw_eq (c : S → σ.Obj S) (s : S) :
    corecRaw c s = encode ⟨(c s).shape, fun b => corecRaw c ((c s).child b)⟩ := by
  refine Raw.ext_root_child rfl fun ⟨s', b⟩ => ?_
  show Raw.corec (coalg c)
    (if h : s' = (c s).shape then some ((c s).child (h ▸ b)) else none) = _
  by_cases h : s' = (c s).shape
  · subst h
    rw [(child_encode_self ⟨(c s).shape, fun b => corecRaw c ((c s).child b)⟩ b :)]
    exact congrArg (Raw.corec (coalg c)) (dif_pos rfl)
  · rw [dif_neg h, child_encode_of_ne _ h]
    exact corec_coalg_none c

theorem isWf_corecRaw (c : S → σ.Obj S) (s : S) : IsWf (corecRaw c s) := by
  refine IsWf.coinduct (fun t => ∃ s, t = corecRaw c s) ?_ _ ⟨s, rfl⟩
  rintro _ ⟨s, rfl⟩
  exact ⟨_, corecRaw_eq c s, fun b => ⟨_, rfl⟩⟩

/-- The corecursor on the container. -/
noncomputable def corecC (c : S → σ.Obj S) (s : S) : σ.Cotype :=
  ⟨corecRaw c s, isWf_corecRaw c s⟩

theorem dtorC_corecC (c : S → σ.Obj S) (s : S) :
    dtorC (corecC c s) = Obj.map (corecC c) (c s) := by
  refine congrArg (Obj.mk (c s).shape) (funext fun b => Subtype.ext ?_)
  show (corecRaw c s).child ⟨(c s).shape, b⟩ = corecRaw c ((c s).child b)
  rw [corecRaw_eq c s, child_encode_self]

/-! ### Bisimulation -/

theorem bisimC (R : σ.Cotype → σ.Cotype → Prop)
    (H : ∀ x y, R x y → Obj.Rel R (dtorC x) (dtorC y)) {x y : σ.Cotype} (h : R x y) : x = y := by
  apply Subtype.ext
  refine Raw.eq_of_bisim' (R := fun t₁ t₂ => ∃ x y : σ.Cotype, t₁ = x.1 ∧ t₂ = y.1 ∧ R x y) ?_
    ⟨x, y, rfl, rfl, h⟩
  rintro _ _ ⟨x, y, rfl, rfl, h⟩
  obtain ⟨s, c, c', hz, hz', hR⟩ := H x y h
  rw [val_eq_encode_dtorC x, val_eq_encode_dtorC y, hz, hz']
  refine ⟨rfl, fun ⟨s', b⟩ => ?_⟩
  by_cases hs : s = s'
  · subst hs
    exact Or.inr ⟨c b, c' b, child_encode_self (Obj.map Subtype.val ⟨s, c⟩) b,
      child_encode_self (Obj.map Subtype.val ⟨s, c'⟩) b, hR b⟩
  · exact Or.inl ((child_encode_of_ne (Obj.map Subtype.val ⟨s, c⟩) (Ne.symm hs) b).trans
      (child_encode_of_ne (Obj.map Subtype.val ⟨s, c'⟩) (Ne.symm hs) b).symm)

/-! ### Transport along an isomorphism `F X ≃ σ.Obj X`

For a user-facing functor `F`, `dtor := ofC ∘ dtorC` and `corec c := corecC (toC ∘ c)`. The two
theorems take the components of the isomorphism at the types where they are used. -/

theorem dtor_corec_of {FS : Type u₁} {FT : Type u₂}
    (toC : FS → σ.Obj S) (ofCS : σ.Obj S → FS) (ofCT : σ.Obj σ.Cotype → FT)
    (map : (S → σ.Cotype) → FS → FT)
    (ofC_toC : ∀ a, ofCS (toC a) = a)
    (ofC_map : ∀ (f : S → σ.Cotype) (z : σ.Obj S), ofCT (Obj.map f z) = map f (ofCS z))
    (c : S → FS) (s : S) :
    ofCT (dtorC (corecC (fun s => toC (c s)) s)) = map (corecC (fun s => toC (c s))) (c s) := by
  rw [dtorC_corecC, ofC_map]
  exact congrArg _ (ofC_toC (c s))

theorem bisim_of {FT : Type u₂} (ofCT : σ.Obj σ.Cotype → FT)
    (Rel : (σ.Cotype → σ.Cotype → Prop) → FT → FT → Prop)
    (rel_ofC : ∀ (R : σ.Cotype → σ.Cotype → Prop) z z',
      Rel R (ofCT z) (ofCT z') → Obj.Rel R z z')
    (R : σ.Cotype → σ.Cotype → Prop)
    (H : ∀ x y, R x y → Rel R (ofCT (dtorC x)) (ofCT (dtorC y))) {x y : σ.Cotype} (h : R x y) :
    x = y :=
  bisimC R (fun x y hxy => rel_ofC R _ _ (H x y hxy)) h

end Signature

/-! ### Derived from the contract: constructors and `corec_eq`

Everything below uses only the five items of `contract.md` and the laws of `F.map`/`F.Rel`: the
functor laws, and the fact that `F.Rel` relates the images of one element under pointwise
related maps. -/

namespace Codata

/-- The contract of `contract.md` for a type `T` and a functor `F`, together with the laws of
`F.map` and `F.Rel`. Since `F` is a bound variable it lives in one universe, so `corec` is only
recorded for states in the universe of `T`; that is all the derivations below need. `T` is a
parameter rather than a field so that its universe is fixed before `F` is elaborated. -/
structure Contract (T : Type u) (F : Type u → Type u) where
  map {X Y : Type u} : (X → Y) → F X → F Y
  Rel {X Y : Type u} : (X → Y → Prop) → F X → F Y → Prop
  map_id {X : Type u} (a : F X) : map id a = a
  map_comp {X Y Z : Type u} (g : Y → Z) (f : X → Y) (a : F X) :
    map (g ∘ f) a = map g (map f a)
  rel_map {X Y Z : Type u} (R : Y → Z → Prop) (f : X → Y) (g : X → Z) (a : F X)
    (h : ∀ x, R (f x) (g x)) : Rel R (map f a) (map g a)
  dtor : T → F T
  corec {S : Type u} : (S → F S) → S → T
  dtor_corec {S : Type u} (c : S → F S) (s : S) : dtor (corec c s) = map (corec c) (c s)
  bisim (R : T → T → Prop) (H : ∀ x y, R x y → Rel R (dtor x) (dtor y)) {x y : T} (h : R x y) :
    x = y

namespace Contract

variable {T : Type u} {F : Type u → Type u} (K : Contract T F) {S : Type u}

/-- The constructor, by Lambek's lemma: the coalgebra morphism out of `(F T, map dtor)`. -/
def ctor (y : F T) : T := K.corec (K.map K.dtor) y

theorem ctor_dtor (t : T) : K.ctor (K.dtor t) = t := by
  refine K.bisim (fun x y => x = K.ctor (K.dtor y)) ?_ rfl
  rintro _ y rfl
  have h := K.rel_map (fun x y => x = K.ctor (K.dtor y)) (K.corec (K.map K.dtor) ∘ K.dtor) id
    (K.dtor y) fun _ => rfl
  rw [K.map_id] at h
  show K.Rel _ (K.dtor (K.corec (K.map K.dtor) (K.dtor y))) (K.dtor y)
  rw [K.dtor_corec, ← K.map_comp]
  exact h

theorem dtor_ctor (y : F T) : K.dtor (K.ctor y) = y := by
  show K.dtor (K.corec (K.map K.dtor) y) = y
  rw [K.dtor_corec, ← K.map_comp]
  have : K.corec (K.map K.dtor) ∘ K.dtor = id := funext K.ctor_dtor
  rw [this, K.map_id]

theorem ctor_injective : Function.Injective K.ctor := fun a b h => by
  rw [← K.dtor_ctor a, ← K.dtor_ctor b, h]

end Contract

/-! ### More derived facts, with the pieces as hypotheses

These need `F` at two types (`F S` and `F T`), so they are stated on the concrete pieces rather
than on a `Contract`. -/

section
variable {T : Type u} {S : Type w} {FS : Type u₁} {FT : Type u₂}

/-- `corec_eq`, from `dtor_corec` and `ctor_dtor`. -/
theorem corec_eq_of (dtor : T → FT) (ctor : FT → T) (corec : (S → FS) → S → T)
    (map : (S → T) → FS → FT)
    (dtor_corec : ∀ (c : S → FS) (s : S), dtor (corec c s) = map (corec c) (c s))
    (ctor_dtor : ∀ t, ctor (dtor t) = t) (c : S → FS) (s : S) :
    corec c s = ctor (map (corec c) (c s)) := by
  rw [← dtor_corec, ctor_dtor]

/-- Uniqueness of `corec`, from `bisim`. -/
theorem corec_unique_of (dtor : T → FT) (corec : (S → FS) → S → T) (map : (S → T) → FS → FT)
    (Rel : (T → T → Prop) → FT → FT → Prop)
    (bisim : ∀ (R : T → T → Prop), (∀ x y, R x y → Rel R (dtor x) (dtor y)) →
      ∀ {x y : T}, R x y → x = y)
    (dtor_corec : ∀ (c : S → FS) (s : S), dtor (corec c s) = map (corec c) (c s))
    (rel_map : ∀ (R : T → T → Prop) (f g : S → T) (a : FS), (∀ x, R (f x) (g x)) →
      Rel R (map f a) (map g a))
    (c : S → FS) (h : S → T) (hh : ∀ s, dtor (h s) = map h (c s)) (s : S) : h s = corec c s := by
  refine bisim (fun x y => ∃ s, x = h s ∧ y = corec c s) ?_ ⟨s, rfl, rfl⟩
  rintro _ _ ⟨s, rfl, rfl⟩
  rw [hh, dtor_corec]
  exact rel_map _ _ _ _ fun s => ⟨s, rfl, rfl⟩

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

end Codata
