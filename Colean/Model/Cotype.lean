import Colean.Raw
import Colean.Framework

/-!
# The model, coinductive part: signatures and the greatest fixpoint on `Raw`

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

*Spec.* Input: a signature `σ`. Output: the family `Cotype σ` with the pieces of the coinductive
contract (`Framework.lean`) on the container functor `σ.Obj`, and the transport theorems that
turn them into the contract for a functor `F` isomorphic to `σ.Obj`. Nothing here is specific
to a declaration.
-/

universe w u u₀ v u₁ u₂ u₃

namespace Codata

/-- An indexed signature: an index type, the data of the constructors producing each index,
their positions for recursive arguments, and the index of the argument at each position. The
positions depend on the shape only through `sh₀`, into the *erased* shapes `Shape₀`: with a type
parameter, `Shape₀` is the data without the parameter's values, so that the encoding indexes
children by data independent of the parameter, and the type is a container in it
(`Param.lean`). Without parameters `Shape₀ = Shape` and `sh₀` is the identity. -/
structure Signature where
  I : Type w
  Shape : I → Type u
  Shape₀ : I → Type u₀
  sh₀ : ∀ {i : I}, Shape i → Shape₀ i
  B : (i : I) → Shape₀ i → Type v
  idx : ∀ {i : I} {s : Shape₀ i}, B i s → I

namespace Signature

variable (σ : Signature.{w, u, u₀, v})

/-- The labels of nodes: an index and a shape producing it. -/
abbrev Lbl : Type (max w u) := Σ i : σ.I, σ.Shape i

/-- The erased labels, which index the children: an index and an erased shape. -/
abbrev Lbl₀ : Type (max w u₀) := Σ i : σ.I, σ.Shape₀ i

/-- The indices of children in the encoding: an erased label and one of its positions. -/
abbrev Idx : Type (max w u₀ v) := Σ l : σ.Lbl₀, σ.B l.1 l.2

/-- The container functor of a signature, on indexed families. -/
structure Obj (X : σ.I → Type u₁) (i : σ.I) : Type (max w u v u₁) where
  shape : σ.Shape i
  child : (b : σ.B i (σ.sh₀ shape)) → X (σ.idx b)

variable {σ} {X : σ.I → Type u₁} {Y : σ.I → Type u₂} {S : σ.I → Type u₃}

namespace Obj

/-- The action on functions. -/
def map (f : ∀ j, X j → Y j) {i : σ.I} (z : σ.Obj X i) : σ.Obj Y i :=
  ⟨z.shape, fun b => f _ (z.child b)⟩

/-- The lifting to relations: same constructor and data, related recursive arguments. -/
abbrev Rel (R : ∀ j, X j → Y j → Prop) {i : σ.I} (z : σ.Obj X i) (z' : σ.Obj Y i) : Prop :=
  ∃ (s : σ.Shape i) (c : (b : σ.B i (σ.sh₀ s)) → X (σ.idx b))
    (c' : (b : σ.B i (σ.sh₀ s)) → Y (σ.idx b)),
    z = ⟨s, c⟩ ∧ z' = ⟨s, c'⟩ ∧ ∀ b, R _ (c b) (c' b)

end Obj

/-! ### Encoding one layer into `Raw` -/

/-- Transport a position along an equality of erased labels. -/
def castB {l l' : σ.Lbl₀} (h : l = l') (b : σ.B l.1 l.2) : σ.B l'.1 l'.2 := h ▸ b

open Classical in
/-- One layer of a tree at index `i`. -/
noncomputable def encode (i : σ.I) (z : σ.Obj (fun _ => Raw σ.Idx σ.Lbl) i) : Raw σ.Idx σ.Lbl :=
  Raw.mk (some ⟨i, z.shape⟩) fun p =>
    if h : p.1 = ⟨i, σ.sh₀ z.shape⟩ then z.child (castB h p.2) else Raw.empty

@[simp] theorem root_encode (i : σ.I) (z : σ.Obj (fun _ => Raw σ.Idx σ.Lbl) i) :
    (encode i z).root = some ⟨i, z.shape⟩ := rfl

theorem child_encode_self (i : σ.I) (z : σ.Obj (fun _ => Raw σ.Idx σ.Lbl) i)
    (b : σ.B i (σ.sh₀ z.shape)) : (encode i z).child ⟨⟨i, σ.sh₀ z.shape⟩, b⟩ = z.child b :=
  dite_eq_left rfl

theorem child_encode_of_ne (i : σ.I) (z : σ.Obj (fun _ => Raw σ.Idx σ.Lbl) i) {l : σ.Lbl₀}
    (h : l ≠ ⟨i, σ.sh₀ z.shape⟩) (b : σ.B l.1 l.2) : (encode i z).child ⟨l, b⟩ = Raw.empty :=
  dite_eq_right h

/-! ### Predicates that are fixpoints of the one-layer operator

Both fixpoints, the greatest (`IsWf`, below) and the least (`IsFin`, in `Data.lean`), unfold
into one layer whose children satisfy the predicate again, and fold back. The destructor and the
constructor of the subtype cut out by such a predicate, and their two computation rules, depend
on nothing else, so they are proved once here. -/

variable (σ) in
/-- `P` is a fixpoint of the operator "one layer whose children satisfy `P`". -/
def IsFix (P : σ.I → Raw σ.Idx σ.Lbl → Prop) : Prop :=
  ∀ i t, P i t ↔ ∃ z : σ.Obj (fun _ => Raw σ.Idx σ.Lbl) i, t = encode i z ∧ ∀ b, P (σ.idx b) (z.child b)

namespace IsFix

variable {P : σ.I → Raw σ.Idx σ.Lbl → Prop} (hP : σ.IsFix P)
include hP

theorem root_ne_none {i : σ.I} {t : Raw σ.Idx σ.Lbl} (h : P i t) : t.root ≠ none := by
  obtain ⟨z, rfl, -⟩ := (hP i t).1 h
  simp

theorem root_idx {i : σ.I} {t : Raw σ.Idx σ.Lbl} (h : P i t) {l : σ.Lbl}
    (hl : t.root = some l) : l.1 = i := by
  obtain ⟨z, rfl, -⟩ := (hP i t).1 h
  obtain rfl := Option.some.inj hl
  rfl

theorem child {i : σ.I} {t : Raw σ.Idx σ.Lbl} (h : P i t) {s : σ.Shape i}
    (hs : t.root = some ⟨i, s⟩) (b : σ.B i (σ.sh₀ s)) :
    P (σ.idx b) (t.child ⟨⟨i, σ.sh₀ s⟩, b⟩) := by
  obtain ⟨z, rfl, hz⟩ := (hP i t).1 h
  obtain rfl : s = z.shape := (eq_of_heq (Sigma.mk.inj (Option.some.inj hs)).2).symm
  rw [child_encode_self]
  exact hz b

theorem child_eq_empty {i : σ.I} {t : Raw σ.Idx σ.Lbl} (h : P i t) {s : σ.Shape i}
    (hs : t.root = some ⟨i, s⟩) {l' : σ.Lbl₀} (hne : l' ≠ ⟨i, σ.sh₀ s⟩) (b : σ.B l'.1 l'.2) :
    t.child ⟨l', b⟩ = Raw.empty := by
  obtain ⟨z, rfl, -⟩ := (hP i t).1 h
  obtain rfl : s = z.shape := (eq_of_heq (Sigma.mk.inj (Option.some.inj hs)).2).symm
  exact child_encode_of_ne i z hne b

/-- A tree satisfying `P` is the layer made of its root and its children. -/
theorem eq_encode {i : σ.I} {t : Raw σ.Idx σ.Lbl} (h : P i t) {s : σ.Shape i}
    (hs : t.root = some ⟨i, s⟩) : t = encode i ⟨s, fun b => t.child ⟨⟨i, σ.sh₀ s⟩, b⟩⟩ := by
  refine Raw.ext_root_child hs fun ⟨l', b⟩ => ?_
  by_cases hl : l' = ⟨i, σ.sh₀ s⟩
  · subst hl
    exact (child_encode_self i ⟨s, fun b => t.child ⟨⟨i, σ.sh₀ s⟩, b⟩⟩ b).symm
  · rw [child_encode_of_ne _ _ hl, hP.child_eq_empty h hs hl]

/-- The shape at the root, which `P` guarantees to exist and to produce the index. -/
def rootShape {i : σ.I} (t : {t // P i t}) : σ.Shape i :=
  match h : t.1.root with
  | some l => (hP.root_idx t.2 h) ▸ l.2
  | none => absurd h (hP.root_ne_none t.2)

theorem root_eq {i : σ.I} (t : {t // P i t}) : t.1.root = some ⟨i, hP.rootShape t⟩ := by
  unfold rootShape
  split
  · rename_i l h
    obtain ⟨i', s⟩ := l
    have hi : i' = i := hP.root_idx t.2 h
    subst hi
    exact h
  · exact absurd ‹_› (hP.root_ne_none t.2)

/-- The destructor of the subtype, on the container. -/
def dtor {i : σ.I} (t : {t // P i t}) : σ.Obj (fun j => {t // P j t}) i :=
  ⟨hP.rootShape t, fun b =>
    ⟨t.1.child ⟨⟨i, σ.sh₀ (hP.rootShape t)⟩, b⟩, hP.child t.2 (hP.root_eq t) b⟩⟩

/-- The tree is the layer of its destructor. -/
theorem val_eq_encode_dtor {i : σ.I} (t : {t // P i t}) :
    t.1 = encode i (Obj.map (fun _ => Subtype.val) (hP.dtor t)) :=
  hP.eq_encode t.2 (hP.root_eq t)

/-- The constructor of the subtype: encode one layer. -/
noncomputable def ctor {i : σ.I} (z : σ.Obj (fun j => {t // P j t}) i) : {t // P i t} :=
  ⟨encode i (Obj.map (fun _ => Subtype.val) z), (hP i _).2 ⟨_, rfl, fun b => (z.child b).2⟩⟩

theorem dtor_ctor {i : σ.I} (z : σ.Obj (fun j => {t // P j t}) i) : hP.dtor (hP.ctor z) = z := by
  obtain ⟨s, c⟩ := z
  refine congrArg (Obj.mk s) (funext fun b => Subtype.ext ?_)
  exact child_encode_self i (Obj.map (fun _ => Subtype.val) (⟨s, c⟩ : σ.Obj (fun j => {t // P j t}) i)) b

theorem ctor_dtor {i : σ.I} (t : {t // P i t}) : hP.ctor (hP.dtor t) = t :=
  Subtype.ext (hP.val_eq_encode_dtor t).symm

end IsFix

/-! ### The predicate and the type -/

/-- Well-formed trees at index `i`: every node is a layer whose children are well-formed at
their own indices. The greatest fixpoint over indexed predicates. -/
def IsWf (i : σ.I) (t : Raw σ.Idx σ.Lbl) : Prop :=
  ∃ z : σ.Obj (fun _ => Raw σ.Idx σ.Lbl) i, t = encode i z ∧ ∀ b, IsWf (σ.idx b) (z.child b)
coinductive_fixpoint

theorem IsWf.isFix : σ.IsFix IsWf := fun i t => Iff.of_eq (IsWf.eq_def i t)

/-- The coinductive family of a signature. -/
def Cotype (σ : Signature.{w, u, u₀, v}) (i : σ.I) : Type (max w u u₀ v) :=
  {t : Raw σ.Idx σ.Lbl // IsWf i t}

/-! ### The destructor -/

/-- The destructor on the container. -/
def dtorC {i : σ.I} (t : σ.Cotype i) : σ.Obj σ.Cotype i := IsWf.isFix.dtor t

/-- The tree is the layer of its destructor. -/
theorem val_eq_encode_dtorC {i : σ.I} (t : σ.Cotype i) :
    t.1 = encode i (Obj.map (fun _ => Subtype.val) (dtorC t)) :=
  IsWf.isFix.val_eq_encode_dtor t

/-- The constructor on the container: encode one layer. The command derives its constructor
from the contract instead (`Contract.ctor`, by corecursion) and relates the two by
`ctor_eq_ctorC_of`. -/
noncomputable def ctorC {i : σ.I} (z : σ.Obj σ.Cotype i) : σ.Cotype i := IsWf.isFix.ctor z

theorem dtorC_ctorC {i : σ.I} (z : σ.Obj σ.Cotype i) : dtorC (ctorC z) = z :=
  IsWf.isFix.dtor_ctor z

theorem ctorC_dtorC {i : σ.I} (t : σ.Cotype i) : ctorC (dtorC t) = t :=
  IsWf.isFix.ctor_dtor t

/-- A constructor that is a left inverse of the destructor is the constructor on the container,
through the isomorphism. -/
theorem ctor_eq_ctorC_of {FT : σ.I → Type u₂} (ofCT : ∀ {i}, σ.Obj σ.Cotype i → FT i)
    (toC : ∀ {i}, FT i → σ.Obj σ.Cotype i) (ofC_toC : ∀ {i} (y : FT i), ofCT (toC y) = y)
    (ctor : ∀ {i}, FT i → σ.Cotype i)
    (ctor_dtor : ∀ {i} (t : σ.Cotype i), ctor (ofCT (dtorC t)) = t) {i : σ.I} (y : FT i) :
    ctor y = ctorC (toC y) := by
  rw [← ctor_dtor (ctorC (toC y)), dtorC_ctorC, ofC_toC]

/-! ### The corecursor -/

open Classical in
/-- The coalgebra on `Option (Σ i, S i)` underlying `corecRaw`: `none` is the state of
`empty`. -/
noncomputable def coalg (c : ∀ i, S i → σ.Obj S i) :
    Option (Σ i, S i) → Option σ.Lbl × (σ.Idx → Option (Σ i, S i))
  | none => (none, fun _ => none)
  | some ⟨i, s⟩ =>
    (some ⟨i, (c i s).shape⟩, fun p =>
      if h : p.1 = ⟨i, σ.sh₀ (c i s).shape⟩ then some ⟨_, (c i s).child (castB h p.2)⟩
      else none)

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
    (if h : l = ⟨i, σ.sh₀ (c i s).shape⟩ then some ⟨_, (c i s).child (castB h b)⟩ else none) = _
  by_cases h : l = ⟨i, σ.sh₀ (c i s).shape⟩
  · subst h
    rw [(child_encode_self i ⟨(c i s).shape, fun b => corecRaw c _ ((c i s).child b)⟩ b :)]
    exact congrArg (Raw.corec (coalg c)) (dite_eq_left rfl)
  · rw [dite_eq_right h, child_encode_of_ne _ _ h]
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
  show (corecRaw c i s).child ⟨⟨i, σ.sh₀ (c i s).shape⟩, b⟩ = corecRaw c _ ((c i s).child b)
  exact (congrArg (Raw.child · ⟨⟨i, σ.sh₀ (c i s).shape⟩, b⟩) (corecRaw_eq c i s)).trans
    (child_encode_self i ⟨(c i s).shape, fun b => corecRaw c _ ((c i s).child b)⟩ b)

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
  by_cases hl : (⟨i, σ.sh₀ s⟩ : σ.Lbl₀) = l'
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

end Codata
