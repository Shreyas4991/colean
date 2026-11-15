import Mathlib.Logic.Equiv.Defs
import Sketch.TreeLemmas

/-!
# `FinTree`: the inductive type defined by the operator of `Tree`

```
inductive FinTree (α) | leaf | node (a : α) (l r : FinTree α)
```

`IsFinTree` is the least fixpoint (`inductive_fixpoint`) of the same operator as `Tree.IsTree`.
As in `FinList.lean`: induction from `IsFinTree.induct`, the inclusion `toTree` into the
coinductive type, recursion into data by well-founded recursion on "is an immediate subtree of",
and the isomorphism `equivNative` with the native `inductive`. Here the two fixpoints differ
visibly: the full infinite tree is not a finite tree (`not_isFinTree_full`).
-/

open Codata

universe u v

open Tree

namespace Tree

variable {α : Type u}

/-- The least fixpoint of the operator of `IsTree`. -/
def IsFinTree (t : Raw ℕ (Shape α)) : Prop :=
  t = rawLeaf ∨ ∃ a l r, t = rawNode a l r ∧ IsFinTree l ∧ IsFinTree r
inductive_fixpoint

end Tree

/-- Finite binary trees with leaves. -/
def FinTree (α : Type u) : Type u := {t : Raw ℕ (Tree.Shape α) // Tree.IsFinTree t}

namespace FinTree

variable {α : Type u}

theorem isFinTree_rawLeaf : IsFinTree (rawLeaf : Raw ℕ (Shape α)) := by
  rw [IsFinTree.eq_def]; exact Or.inl rfl

theorem isFinTree_rawNode {a : α} {l r : Raw ℕ (Shape α)} (hl : IsFinTree l) (hr : IsFinTree r) :
    IsFinTree (rawNode a l r) := by
  rw [IsFinTree.eq_def]; exact Or.inr ⟨a, l, r, rfl, hl, hr⟩

/-- The leaf. -/
def leaf : FinTree α := ⟨rawLeaf, isFinTree_rawLeaf⟩

/-- A node with two subtrees. -/
def node (a : α) (l r : FinTree α) : FinTree α := ⟨rawNode a l.1 r.1, isFinTree_rawNode l.2 r.2⟩

@[simp] theorem leaf_ne_node (a : α) (l r : FinTree α) : leaf ≠ node a l r := fun h =>
  rawLeaf_ne_rawNode a l.1 r.1 (congrArg Subtype.val h)

@[simp] theorem node_ne_leaf (a : α) (l r : FinTree α) : node a l r ≠ leaf :=
  (leaf_ne_node a l r).symm

@[simp] theorem node_inj {a a' : α} {l l' r r' : FinTree α} :
    node a l r = node a' l' r' ↔ a = a' ∧ l = l' ∧ r = r' := by
  constructor
  · intro h
    obtain ⟨h₁, h₂, h₃⟩ := rawNode_inj.mp (congrArg Subtype.val h)
    exact ⟨h₁, Subtype.ext h₂, Subtype.ext h₃⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-- Induction, from the generated `IsFinTree.induct`. -/
theorem induction {motive : FinTree α → Prop} (leaf : motive leaf)
    (node : ∀ a l r, motive l → motive r → motive (node a l r)) (t : FinTree α) : motive t := by
  obtain ⟨t, ht⟩ := t
  refine (IsFinTree.induct (fun t => ∃ h : IsFinTree t, motive ⟨t, h⟩) ?_ t ht).elim fun _ h => h
  rintro t (rfl | ⟨a, l, r, rfl, ⟨hl, ihl⟩, ⟨hr, ihr⟩⟩)
  · exact ⟨isFinTree_rawLeaf, leaf⟩
  · exact ⟨isFinTree_rawNode hl hr, node a ⟨l, hl⟩ ⟨r, hr⟩ ihl ihr⟩

/-- The least fixpoint is below the greatest. -/
theorem isTree_of_isFinTree {t : Raw ℕ (Shape α)} (h : IsFinTree t) : IsTree t :=
  IsFinTree.induct IsTree (fun t h => IsTree.eq_def t ▸ h) t h

/-- The inclusion of finite trees into trees. -/
def toTree (t : FinTree α) : Tree α := ⟨t.1, isTree_of_isFinTree t.2⟩

@[simp] theorem toTree_leaf : toTree (leaf : FinTree α) = Tree.leaf := rfl
@[simp] theorem toTree_node (a : α) (l r : FinTree α) :
    toTree (node a l r) = Tree.node a (toTree l) (toTree r) := rfl

/-- The greatest fixpoint is strictly bigger than the least one: the full infinite tree is not
a finite tree. Proved by the induction principle of the least fixpoint. -/
theorem not_isFinTree_full (a : α) : ¬ IsFinTree (full a).1 := fun hfin =>
  have hx : (full a).1 = rawNode a (full a).1 (full a).1 := congrArg Subtype.val (full_eq a)
  IsFinTree.induct (fun t => t ≠ (full a).1)
    (by
      rintro t (rfl | ⟨b, l, r, rfl, hl, -⟩) h
      · exact rawLeaf_ne_rawNode a _ _ (h.trans hx)
      · exact hl (rawNode_inj.mp (h.trans hx)).2.1)
    _ hfin rfl

theorem cases (t : FinTree α) : t = leaf ∨ ∃ a l r, t = node a l r :=
  induction (motive := fun t => t = leaf ∨ ∃ a l r, t = node a l r) (Or.inl rfl)
    (fun a l r _ _ => Or.inr ⟨a, l, r, rfl⟩) t

theorem isFinTree_child {t : Raw ℕ (Shape α)} (ht : IsFinTree t) {a : α}
    (h : t.root = some (.node a)) : IsFinTree (t.child 0) ∧ IsFinTree (t.child 1) := by
  rw [IsFinTree.eq_def] at ht
  rcases ht with rfl | ⟨a', l, r, rfl, hl, hr⟩
  · simp at h
  · simpa using And.intro hl hr

/-- The computable destructor. -/
def dest (t : FinTree α) : Option (α × FinTree α × FinTree α) :=
  match h : t.1.root with
  | some (.node a) =>
    some (a, ⟨t.1.child 0, (isFinTree_child t.2 h).1⟩, ⟨t.1.child 1, (isFinTree_child t.2 h).2⟩)
  | _ => none

@[simp] theorem dest_leaf : dest (leaf : FinTree α) = none := rfl
@[simp] theorem dest_node (a : α) (l r : FinTree α) : dest (node a l r) = some (a, l, r) := rfl

theorem dest_eq_none_iff {t : FinTree α} : dest t = none ↔ t = leaf := by
  rcases cases t with rfl | ⟨a, l, r, rfl⟩ <;> simp

theorem dest_eq_some_iff {t : FinTree α} {a : α} {l r : FinTree α} :
    dest t = some (a, l, r) ↔ t = node a l r := by
  rcases cases t with rfl | ⟨a', l', r', rfl⟩ <;> simp

/-! ### Recursion into data, and the native inductive type -/

/-- `s` is an immediate subtree of `t`. -/
def IsSub (s t : FinTree α) : Prop := ∃ a l r, t = node a l r ∧ (s = l ∨ s = r)

theorem isSub_wf : WellFounded (IsSub (α := α)) :=
  ⟨induction (motive := Acc IsSub)
    (Acc.intro _ fun _ ⟨a, l, r, h, _⟩ => absurd h (leaf_ne_node a l r))
    fun _ _ _ ihl ihr => Acc.intro _ fun _ ⟨_, _, _, h, hs⟩ => by
      obtain ⟨rfl, rfl, rfl⟩ := node_inj.mp h
      rcases hs with rfl | rfl
      · exact ihl
      · exact ihr⟩

instance : WellFoundedRelation (FinTree α) := ⟨IsSub, isSub_wf⟩

/-- The native inductive type, for comparison. -/
inductive Native (α : Type u)
  | leaf
  | node (a : α) (l r : Native α)

-- The linter does not see the use of `h` inside `decreasing_by`.
set_option linter.unusedVariables false in
/-- To the native type, by well-founded recursion on `IsSub`. Computable. -/
def toNative (t : FinTree α) : Native α :=
  match h : dest t with
  | none => .leaf
  | some (a, l, r) => .node a (toNative l) (toNative r)
termination_by t
decreasing_by all_goals exact ⟨_, _, _, dest_eq_some_iff.mp h, by simp⟩

@[simp] theorem toNative_leaf : toNative (leaf : FinTree α) = .leaf := by
  rw [toNative]; rfl

@[simp] theorem toNative_node (a : α) (l r : FinTree α) :
    toNative (node a l r) = .node a (toNative l) (toNative r) := by
  rw [toNative]; rfl

/-- From the native type, by structural recursion. -/
def ofNative : Native α → FinTree α
  | .leaf => leaf
  | .node a l r => node a (ofNative l) (ofNative r)

theorem toNative_ofNative (t : Native α) : toNative (ofNative t) = t := by
  induction t with
  | leaf => simp [ofNative]
  | node a l r ihl ihr => simp [ofNative, ihl, ihr]

theorem ofNative_toNative (t : FinTree α) : ofNative (toNative t) = t := by
  refine induction (motive := fun t => ofNative (toNative t) = t) ?_ ?_ t
  · simp [ofNative]
  · intro a l r ihl ihr
    simp [ofNative, ihl, ihr]

/-- `FinTree α` is the native inductive type. -/
def equivNative : FinTree α ≃ Native α := ⟨toNative, ofNative, ofNative_toNative, toNative_ofNative⟩

end FinTree
