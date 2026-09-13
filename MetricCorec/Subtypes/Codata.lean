import Mathlib.Logic.Function.Basic
import MetricCorec.Subtypes.Raw

/-!
# Generic theory behind `codata`

A `codata` declaration is a *signature*, an indexed polynomial functor: an index type `I`, the
non-recursive data of the constructors producing each index (the *shapes*, `Shape : I → Type`),
for each shape its positions for recursive arguments (`B : (i : I) → Shape i → Type`), and the
index of the argument at each position (`idx : B i s → I`). A plain type is a family over `Unit`.
The command generates the positions as an inductive family, one nullary constructor per plain
recursive argument and one unary constructor per argument under a function type, whose domain
may depend on the shape (`Vis {X} (e : E X) (k : X → T)` has positions `X`). Everything the
contract asks for is built here once, generically over a signature `σ`, for the container
functor `σ.Obj (X : I → Type) i = { shape : σ.Shape i, child : (b : σ.B i shape) → X (σ.idx b) }`:

* `Signature.Cotype σ : I → Type`: the subtype of `Raw σ.Idx σ.Lbl` cut out by the greatest
  fixpoint `IsWf : I → Raw → Prop`, where labels are an index with a shape and path indices are
  a label with one of its positions. Placing `empty` at the indices of the other labels decides
  equality of labels, classically: `corec` and the constructors are noncomputable, which is
  accepted here;
* `dtorC`, `corecC`, `dtorC_corecC`, `bisimC`: the contract for `σ.Obj`. The index is implicit
  wherever an argument determines it (`dtorC`, `corecC`, `map`, `Rel`, …) and explicit in
  families of functions and relations (`∀ j, X j → Y j`).

The index of a position is a function rather than a further index of `B` so that it is
*computed* (`idx b` reduces once `b` is a constructor) and never has to be inferred by
unification: with propositions as indices, unification cannot recover a proof argument from
`idx`-shaped terms, since any two proofs are definitionally equal.

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

universe w u v u₁ u₂ u₃

namespace Codata

/-- An indexed signature: an index type, the data of the constructors producing each index,
their positions for recursive arguments, and the index of the argument at each position. -/
structure Signature where
  I : Type w
  Shape : I → Type u
  B : (i : I) → Shape i → Type v
  idx : ∀ {i : I} {s : Shape i}, B i s → I

namespace Signature

variable (σ : Signature.{w, u, v})

/-- The labels of nodes: an index and a shape producing it. -/
abbrev Lbl : Type (max w u) := Σ i : σ.I, σ.Shape i

/-- The indices of children in the encoding: a label and one of its positions. -/
abbrev Idx : Type (max w u v) := Σ l : σ.Lbl, σ.B l.1 l.2

/-- The container functor of a signature, on indexed families. -/
structure Obj (X : σ.I → Type u₁) (i : σ.I) : Type (max w u v u₁) where
  shape : σ.Shape i
  child : (b : σ.B i shape) → X (σ.idx b)

variable {σ} {X : σ.I → Type u₁} {Y : σ.I → Type u₂} {S : σ.I → Type u₃}

namespace Obj

/-- The action on functions. -/
def map (f : ∀ j, X j → Y j) {i : σ.I} (z : σ.Obj X i) : σ.Obj Y i :=
  ⟨z.shape, fun b => f _ (z.child b)⟩

/-- The lifting to relations: same constructor and data, related recursive arguments. -/
abbrev Rel (R : ∀ j, X j → Y j → Prop) {i : σ.I} (z : σ.Obj X i) (z' : σ.Obj Y i) : Prop :=
  ∃ (s : σ.Shape i) (c : (b : σ.B i s) → X (σ.idx b)) (c' : (b : σ.B i s) → Y (σ.idx b)),
    z = ⟨s, c⟩ ∧ z' = ⟨s, c'⟩ ∧ ∀ b, R _ (c b) (c' b)

end Obj

/-! ### Encoding one layer into `Raw` -/

/-- Transport a position along an equality of labels. -/
def castB {l l' : σ.Lbl} (h : l = l') (b : σ.B l.1 l.2) : σ.B l'.1 l'.2 := h ▸ b

open Classical in
/-- One layer of a tree at index `i`. -/
noncomputable def encode (i : σ.I) (z : σ.Obj (fun _ => Raw σ.Idx σ.Lbl) i) : Raw σ.Idx σ.Lbl :=
  Raw.mk (some ⟨i, z.shape⟩) fun p =>
    if h : p.1 = ⟨i, z.shape⟩ then z.child (castB h p.2) else Raw.empty

@[simp] theorem root_encode (i : σ.I) (z : σ.Obj (fun _ => Raw σ.Idx σ.Lbl) i) :
    (encode i z).root = some ⟨i, z.shape⟩ := rfl

theorem child_encode_self (i : σ.I) (z : σ.Obj (fun _ => Raw σ.Idx σ.Lbl) i)
    (b : σ.B i z.shape) : (encode i z).child ⟨⟨i, z.shape⟩, b⟩ = z.child b :=
  dif_pos rfl

theorem child_encode_of_ne (i : σ.I) (z : σ.Obj (fun _ => Raw σ.Idx σ.Lbl) i) {l : σ.Lbl}
    (h : l ≠ ⟨i, z.shape⟩) (b : σ.B l.1 l.2) : (encode i z).child ⟨l, b⟩ = Raw.empty :=
  dif_neg h

/-! ### The predicate and the type -/

/-- Well-formed trees at index `i`: every node is a layer whose children are well-formed at
their own indices. The greatest fixpoint over indexed predicates. -/
def IsWf (i : σ.I) (t : Raw σ.Idx σ.Lbl) : Prop :=
  ∃ z : σ.Obj (fun _ => Raw σ.Idx σ.Lbl) i, t = encode i z ∧ ∀ b, IsWf (σ.idx b) (z.child b)
coinductive_fixpoint

/-- The coinductive family of a signature. -/
def Cotype (σ : Signature.{w, u, v}) (i : σ.I) : Type (max w u v) :=
  {t : Raw σ.Idx σ.Lbl // IsWf i t}

theorem IsWf.root_ne_none {i : σ.I} {t : Raw σ.Idx σ.Lbl} (h : IsWf i t) : t.root ≠ none := by
  rw [IsWf.eq_def] at h
  obtain ⟨z, rfl, -⟩ := h
  simp

theorem IsWf.root_idx {i : σ.I} {t : Raw σ.Idx σ.Lbl} (h : IsWf i t) {l : σ.Lbl}
    (hl : t.root = some l) : l.1 = i := by
  rw [IsWf.eq_def] at h
  obtain ⟨z, rfl, -⟩ := h
  obtain rfl := Option.some.inj hl
  rfl

theorem IsWf.child {i : σ.I} {t : Raw σ.Idx σ.Lbl} (h : IsWf i t) {s : σ.Shape i}
    (hs : t.root = some ⟨i, s⟩) (b : σ.B i s) : IsWf (σ.idx b) (t.child ⟨⟨i, s⟩, b⟩) := by
  rw [IsWf.eq_def] at h
  obtain ⟨z, rfl, hz⟩ := h
  obtain rfl : s = z.shape := (eq_of_heq (Sigma.mk.inj (Option.some.inj hs)).2).symm
  rw [child_encode_self]
  exact hz b

theorem IsWf.child_eq_empty {i : σ.I} {t : Raw σ.Idx σ.Lbl} (h : IsWf i t) {s : σ.Shape i}
    (hs : t.root = some ⟨i, s⟩) {l' : σ.Lbl} (hne : l' ≠ ⟨i, s⟩) (b : σ.B l'.1 l'.2) :
    t.child ⟨l', b⟩ = Raw.empty := by
  rw [IsWf.eq_def] at h
  obtain ⟨z, rfl, -⟩ := h
  obtain rfl : s = z.shape := (eq_of_heq (Sigma.mk.inj (Option.some.inj hs)).2).symm
  exact child_encode_of_ne i z hne b

/-- A well-formed tree is the layer made of its root and its children. -/
theorem IsWf.eq_encode {i : σ.I} {t : Raw σ.Idx σ.Lbl} (h : IsWf i t) {s : σ.Shape i}
    (hs : t.root = some ⟨i, s⟩) : t = encode i ⟨s, fun b => t.child ⟨⟨i, s⟩, b⟩⟩ := by
  refine Raw.ext_root_child hs fun ⟨l', b⟩ => ?_
  by_cases hl : l' = ⟨i, s⟩
  · subst hl
    exact (child_encode_self i ⟨s, fun b => t.child ⟨⟨i, s⟩, b⟩⟩ b).symm
  · rw [child_encode_of_ne _ _ hl, h.child_eq_empty hs hl]

/-! ### The destructor -/

/-- The shape at the root, which `IsWf` guarantees to exist and to produce the index. -/
def rootShape {i : σ.I} (t : σ.Cotype i) : σ.Shape i :=
  match h : t.1.root with
  | some l => (t.2.root_idx h) ▸ l.2
  | none => absurd h t.2.root_ne_none

theorem root_eq {i : σ.I} (t : σ.Cotype i) : t.1.root = some ⟨i, rootShape t⟩ := by
  unfold rootShape
  split
  · rename_i l h
    obtain ⟨i', s⟩ := l
    have hi : i' = i := t.2.root_idx h
    subst hi
    exact h
  · exact absurd ‹_› t.2.root_ne_none

/-- The destructor on the container. -/
def dtorC {i : σ.I} (t : σ.Cotype i) : σ.Obj σ.Cotype i :=
  ⟨rootShape t, fun b => ⟨t.1.child ⟨⟨i, rootShape t⟩, b⟩, t.2.child (root_eq t) b⟩⟩

/-- The tree is the layer of its destructor. -/
theorem val_eq_encode_dtorC {i : σ.I} (t : σ.Cotype i) :
    t.1 = encode i (Obj.map (fun _ => Subtype.val) (dtorC t)) :=
  t.2.eq_encode (root_eq t)

/-! ### The corecursor -/

open Classical in
/-- The coalgebra on `Option (Σ i, S i)` underlying `corecRaw`: `none` is the state of
`empty`. -/
noncomputable def coalg (c : ∀ i, S i → σ.Obj S i) :
    Option (Σ i, S i) → Option σ.Lbl × (σ.Idx → Option (Σ i, S i))
  | none => (none, fun _ => none)
  | some ⟨i, s⟩ =>
    (some ⟨i, (c i s).shape⟩, fun p =>
      if h : p.1 = ⟨i, (c i s).shape⟩ then some ⟨_, (c i s).child (castB h p.2)⟩ else none)

/-- Unfolding a coalgebra into `Raw`. -/
noncomputable def corecRaw (c : ∀ i, S i → σ.Obj S i) (i : σ.I) (s : S i) : Raw σ.Idx σ.Lbl :=
  Raw.corec (coalg c) (some ⟨i, s⟩)

theorem corec_coalg_none (c : ∀ i, S i → σ.Obj S i) : Raw.corec (coalg c) none = Raw.empty :=
  Raw.eq_of_bisim (R := fun t₁ t₂ => t₁ = Raw.corec (coalg c) none ∧ t₂ = Raw.empty)
    (by rintro _ _ ⟨rfl, rfl⟩; exact ⟨rfl, fun i => ⟨rfl, rfl⟩⟩) ⟨rfl, rfl⟩

@[simp] theorem root_corecRaw (c : ∀ i, S i → σ.Obj S i) (i : σ.I) (s : S i) :
    (corecRaw c i s).root = some ⟨i, (c i s).shape⟩ := rfl

open Classical in
theorem corecRaw_eq (c : ∀ i, S i → σ.Obj S i) (i : σ.I) (s : S i) :
    corecRaw c i s = encode i ⟨(c i s).shape, fun b => corecRaw c _ ((c i s).child b)⟩ := by
  refine Raw.ext_root_child rfl fun ⟨l, b⟩ => ?_
  show Raw.corec (coalg c)
    (if h : l = ⟨i, (c i s).shape⟩ then some ⟨_, (c i s).child (castB h b)⟩ else none) = _
  by_cases h : l = ⟨i, (c i s).shape⟩
  · subst h
    rw [(child_encode_self i ⟨(c i s).shape, fun b => corecRaw c _ ((c i s).child b)⟩ b :)]
    exact congrArg (Raw.corec (coalg c)) (dif_pos rfl)
  · rw [dif_neg h, child_encode_of_ne _ _ h]
    exact corec_coalg_none c

theorem isWf_corecRaw (c : ∀ i, S i → σ.Obj S i) (i : σ.I) (s : S i) : IsWf i (corecRaw c i s) := by
  refine IsWf.coinduct (fun i t => ∃ s, t = corecRaw c i s) ?_ i _ ⟨s, rfl⟩
  rintro i _ ⟨s, rfl⟩
  exact ⟨_, corecRaw_eq c i s, fun b => ⟨_, rfl⟩⟩

/-- The corecursor on the container. -/
noncomputable def corecC (c : ∀ i, S i → σ.Obj S i) {i : σ.I} (s : S i) : σ.Cotype i :=
  ⟨corecRaw c i s, isWf_corecRaw c i s⟩

theorem dtorC_corecC (c : ∀ i, S i → σ.Obj S i) {i : σ.I} (s : S i) :
    dtorC (corecC c s) = Obj.map (fun _ s => corecC c s) (c i s) := by
  refine congrArg (Obj.mk (c i s).shape) (funext fun b => Subtype.ext ?_)
  show (corecRaw c i s).child ⟨⟨i, (c i s).shape⟩, b⟩ = corecRaw c _ ((c i s).child b)
  rw [corecRaw_eq c i s, child_encode_self]

/-! ### Bisimulation -/

theorem bisimC (R : ∀ i, σ.Cotype i → σ.Cotype i → Prop)
    (H : ∀ i x y, R i x y → Obj.Rel R (dtorC x) (dtorC y)) {i : σ.I} {x y : σ.Cotype i}
    (h : R i x y) : x = y := by
  apply Subtype.ext
  refine Raw.eq_of_bisim'
    (R := fun t₁ t₂ => ∃ (i : σ.I) (x y : σ.Cotype i), t₁ = x.1 ∧ t₂ = y.1 ∧ R i x y) ?_
    ⟨i, x, y, rfl, rfl, h⟩
  rintro _ _ ⟨i, x, y, rfl, rfl, h⟩
  obtain ⟨s, c, c', hz, hz', hR⟩ := H i x y h
  rw [val_eq_encode_dtorC x, val_eq_encode_dtorC y, hz, hz']
  refine ⟨rfl, fun ⟨l', b⟩ => ?_⟩
  by_cases hl : (⟨i, s⟩ : σ.Lbl) = l'
  · subst hl
    exact Or.inr ⟨_, c b, c' b,
      child_encode_self i (Obj.map (fun _ => Subtype.val) (⟨s, c⟩ : σ.Obj σ.Cotype i)) b,
      child_encode_self i (Obj.map (fun _ => Subtype.val) (⟨s, c'⟩ : σ.Obj σ.Cotype i)) b,
      hR b⟩
  · exact Or.inl
      ((child_encode_of_ne i (Obj.map (fun _ => Subtype.val) (⟨s, c⟩ : σ.Obj σ.Cotype i))
          (Ne.symm hl) b).trans
        (child_encode_of_ne i (Obj.map (fun _ => Subtype.val) (⟨s, c'⟩ : σ.Obj σ.Cotype i))
          (Ne.symm hl) b).symm)

/-! ### Transport along an isomorphism `F X i ≃ σ.Obj X i` -/

theorem dtor_corec_of {FS : σ.I → Type u₁} {FT : σ.I → Type u₂}
    (toC : ∀ {i}, FS i → σ.Obj S i) (ofCS : ∀ {i}, σ.Obj S i → FS i)
    (ofCT : ∀ {i}, σ.Obj σ.Cotype i → FT i)
    (map : (∀ j, S j → σ.Cotype j) → ∀ {i}, FS i → FT i)
    (ofC_toC : ∀ {i} (a : FS i), ofCS (toC a) = a)
    (ofC_map : ∀ (f : ∀ j, S j → σ.Cotype j) {i} (z : σ.Obj S i),
      ofCT (Obj.map f z) = map f (ofCS z))
    (c : ∀ i, S i → FS i) {i : σ.I} (s : S i) :
    ofCT (dtorC (corecC (fun j s => toC (c j s)) s)) =
      map (fun _ s => corecC (fun j s => toC (c j s)) s) (c i s) := by
  rw [dtorC_corecC, ofC_map]
  exact congrArg _ (ofC_toC (c i s))

theorem bisim_of {FT : σ.I → Type u₂} (ofCT : ∀ {i}, σ.Obj σ.Cotype i → FT i)
    (Rel : (∀ j, σ.Cotype j → σ.Cotype j → Prop) → ∀ {i}, FT i → FT i → Prop)
    (rel_ofC : ∀ (R : ∀ j, σ.Cotype j → σ.Cotype j → Prop) {i} (z z' : σ.Obj σ.Cotype i),
      Rel R (ofCT z) (ofCT z') → Obj.Rel R z z')
    (R : ∀ i, σ.Cotype i → σ.Cotype i → Prop)
    (H : ∀ i x y, R i x y → Rel R (ofCT (dtorC x)) (ofCT (dtorC y)))
    {i : σ.I} {x y : σ.Cotype i} (h : R i x y) : x = y :=
  bisimC R (fun i x y hxy => rel_ofC R _ _ (H i x y hxy)) h

end Signature

/-! ### Derived from the contract, for indexed families -/

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

end Codata
