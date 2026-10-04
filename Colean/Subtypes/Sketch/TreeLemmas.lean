import Colean.Subtypes.Sketch.Tree

/-!
# What `Tree` supports beyond its corecursor

Injectivity and disjointness of constructors, case analysis, the computable destructor `dest`,
bisimulation `eq_of_bisim`, and two examples: `mirror` (with `mirror_mirror` by bisimulation)
and the full infinite tree `full`.
-/

universe u v

namespace Tree

variable {α : Type u} {S : Type v}

/-! ### The raw constructors -/

@[simp] theorem root_rawLeaf : (rawLeaf : Raw ℕ (Shape α)).root = some .leaf := rfl
@[simp] theorem child_rawLeaf (i : ℕ) : (rawLeaf : Raw ℕ (Shape α)).child i = Raw.empty := by
  cases i <;> rfl
@[simp] theorem root_rawNode (a : α) (l r : Raw ℕ (Shape α)) :
    (rawNode a l r).root = some (.node a) := rfl
@[simp] theorem child_rawNode_zero (a : α) (l r : Raw ℕ (Shape α)) :
    (rawNode a l r).child 0 = l := rfl
@[simp] theorem child_rawNode_one (a : α) (l r : Raw ℕ (Shape α)) :
    (rawNode a l r).child 1 = r := rfl
@[simp] theorem child_rawNode_add_two (a : α) (l r : Raw ℕ (Shape α)) (i : ℕ) :
    (rawNode a l r).child (i + 2) = Raw.empty := by
  cases i <;> rfl

@[simp] theorem rawLeaf_ne_rawNode (a : α) (l r : Raw ℕ (Shape α)) : rawLeaf ≠ rawNode a l r := by
  intro h; simpa using congrArg Raw.root h

@[simp] theorem rawNode_inj {a a' : α} {l l' r r' : Raw ℕ (Shape α)} :
    rawNode a l r = rawNode a' l' r' ↔ a = a' ∧ l = l' ∧ r = r' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg Raw.root h, by simpa using congrArg (Raw.child · 0) h,
      by simpa using congrArg (Raw.child · 1) h⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-! ### Constructors -/

@[simp] theorem val_leaf : (leaf : Tree α).1 = rawLeaf := rfl
@[simp] theorem val_node (a : α) (l r : Tree α) : (node a l r).1 = rawNode a l.1 r.1 := rfl

@[simp] theorem leaf_ne_node (a : α) (l r : Tree α) : leaf ≠ node a l r := fun h =>
  rawLeaf_ne_rawNode a l.1 r.1 (congrArg Subtype.val h)

@[simp] theorem node_ne_leaf (a : α) (l r : Tree α) : node a l r ≠ leaf := (leaf_ne_node a l r).symm

@[simp] theorem node_inj {a a' : α} {l l' r r' : Tree α} :
    node a l r = node a' l' r' ↔ a = a' ∧ l = l' ∧ r = r' := by
  constructor
  · intro h
    obtain ⟨h₁, h₂, h₃⟩ := rawNode_inj.mp (congrArg Subtype.val h)
    exact ⟨h₁, Subtype.ext h₂, Subtype.ext h₃⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-! ### Case analysis and the destructor -/

theorem cases (t : Tree α) : t = leaf ∨ ∃ a l r, t = node a l r := by
  obtain ⟨t, ht⟩ := t
  rw [IsTree.eq_def] at ht
  rcases ht with rfl | ⟨a, l, r, rfl, hl, hr⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨a, ⟨l, hl⟩, ⟨r, hr⟩, rfl⟩

theorem isTree_child {t : Raw ℕ (Shape α)} (ht : IsTree t) {a : α} (h : t.root = some (.node a)) :
    IsTree (t.child 0) ∧ IsTree (t.child 1) := by
  rw [IsTree.eq_def] at ht
  rcases ht with rfl | ⟨a', l, r, rfl, hl, hr⟩
  · simp at h
  · simpa using And.intro hl hr

/-- The computable destructor. -/
def dest (t : Tree α) : Option (α × Tree α × Tree α) :=
  match h : t.1.root with
  | some (.node a) =>
    some (a, ⟨t.1.child 0, (isTree_child t.2 h).1⟩, ⟨t.1.child 1, (isTree_child t.2 h).2⟩)
  | _ => none

@[simp] theorem dest_leaf : dest (leaf : Tree α) = none := rfl
@[simp] theorem dest_node (a : α) (l r : Tree α) : dest (node a l r) = some (a, l, r) := rfl

theorem dest_eq_none_iff {t : Tree α} : dest t = none ↔ t = leaf := by
  rcases cases t with rfl | ⟨a, l, r, rfl⟩ <;> simp

theorem dest_eq_some_iff {t : Tree α} {a : α} {l r : Tree α} :
    dest t = some (a, l, r) ↔ t = node a l r := by
  rcases cases t with rfl | ⟨a', l', r', rfl⟩ <;> simp

@[simp] theorem dest_corec (f : S → Option (α × S × S)) (s : S) :
    dest (corec f s) = (f s).map fun p => (p.1, corec f p.2.1, corec f p.2.2) := by
  rw [corec_eq]
  rcases f s with _ | ⟨a, l, r⟩ <;> simp

/-! ### Bisimulation -/

theorem eq_of_bisim (R : Tree α → Tree α → Prop)
    (H : ∀ t₁ t₂, R t₁ t₂ → (t₁ = leaf ∧ t₂ = leaf) ∨
      ∃ a l₁ r₁ l₂ r₂, t₁ = node a l₁ r₁ ∧ t₂ = node a l₂ r₂ ∧ R l₁ l₂ ∧ R r₁ r₂)
    {t₁ t₂ : Tree α} (h : R t₁ t₂) : t₁ = t₂ := by
  apply Subtype.ext
  refine Raw.eq_of_bisim' (R := fun x₁ x₂ => ∃ t₁ t₂ : Tree α, x₁ = t₁.1 ∧ x₂ = t₂.1 ∧ R t₁ t₂)
    ?_ ⟨t₁, t₂, rfl, rfl, h⟩
  rintro _ _ ⟨t₁, t₂, rfl, rfl, h⟩
  rcases H t₁ t₂ h with ⟨rfl, rfl⟩ | ⟨a, l₁, r₁, l₂, r₂, rfl, rfl, hl, hr⟩
  · exact ⟨rfl, fun _ => Or.inl rfl⟩
  · refine ⟨rfl, fun i => ?_⟩
    match i with
    | 0 => exact Or.inr ⟨l₁, l₂, rfl, rfl, hl⟩
    | 1 => exact Or.inr ⟨r₁, r₂, rfl, rfl, hr⟩
    | _ + 2 => exact Or.inl rfl

/-! ### Examples -/

/-- The mirror image, by corecursion. -/
def mirror (t : Tree α) : Tree α :=
  corec (fun t => (dest t).map fun p => (p.1, p.2.2, p.2.1)) t

@[simp] theorem mirror_leaf : mirror (leaf : Tree α) = leaf := by
  rw [mirror, corec_eq]; rfl

@[simp] theorem mirror_node (a : α) (l r : Tree α) :
    mirror (node a l r) = node a (mirror r) (mirror l) := by
  rw [mirror, corec_eq]; rfl

theorem mirror_mirror (t : Tree α) : mirror (mirror t) = t := by
  refine eq_of_bisim (fun t₁ t₂ => t₁ = mirror (mirror t₂)) ?_ rfl
  rintro _ t rfl
  rcases cases t with rfl | ⟨a, l, r, rfl⟩
  · simp
  · exact Or.inr ⟨a, _, _, l, r, by simp, rfl, rfl, rfl⟩

/-- The full infinite tree with every label equal to `a`. -/
def full (a : α) : Tree α := corec (fun x => some (x, x, x)) a

theorem full_eq (a : α) : full a = node a (full a) (full a) := by
  show corec _ a = _
  rw [corec_eq]; rfl

theorem mirror_full (a : α) : mirror (full a) = full a := by
  refine eq_of_bisim (fun t₁ t₂ => t₁ = mirror (full a) ∧ t₂ = full a) ?_ ⟨rfl, rfl⟩
  rintro _ _ ⟨rfl, rfl⟩
  refine Or.inr ⟨a, mirror (full a), mirror (full a), full a, full a, ?_, full_eq a, ⟨rfl, rfl⟩,
    ⟨rfl, rfl⟩⟩
  calc mirror (full a) = mirror (node a (full a) (full a)) := by rw [← full_eq]
    _ = node a (mirror (full a)) (mirror (full a)) := mirror_node _ _ _

end Tree
