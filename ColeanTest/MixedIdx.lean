import Colean.MutualCmd

/-! # Test: a run with indices inside a mixed block

An inner run may have indices: the open family gets its instances at every index, and the outer
run nests through it at the index of each field. (An outer run with indices is not supported:
`MixedRejected.lean`.) -/

universe u

namespace MixedIdxTest

open Codata

noncomputable section

-- Infinite trees whose children are vectors of trees, of the length the node says.
mixed_mutual
codatatype ITree (α : Type u)
  | node (a : α) (n : Nat) (cs : IForest α n)
datatype IForest (α : Type u) : Nat → Type u
  | nil : IForest α 0
  | cons {n : Nat} (t : ITree α) (f : IForest α n) : IForest α (n + 1)
end

/-- info: @ITree.node : {α : Type u_1} → α → (n : ℕ) → IForest α n → ITree α -/
#guard_msgs in #check @ITree.node
/--
info: @IForest.cons : {α : Type u_1} → {n : ℕ} → ITree α → IForest α n → IForest α (n + 1)
-/
#guard_msgs in #check @IForest.cons
/--
info: @IForest.rec : {α : Type u_2} →
  {motive : (j₁ : ℕ) → IForest α j₁ → Sort u_1} →
    motive 0 IForest.nil →
      ({n : ℕ} → (t : ITree α) → (f : IForest α n) → motive n f → motive (n + 1) (IForest.cons t f)) →
        {i₁ : ℕ} → (t : IForest α i₁) → motive i₁ t
-/
#guard_msgs in #check @IForest.rec

/-- The length of a vector of trees, by its fold: the index. -/
def IForest.length {α : Type u} {n : Nat} (f : IForest α n) : Nat :=
  IForest.fold (S := fun _ => Nat) (fun _ y => match y with | .nil => 0 | .cons _ k => k + 1) f

example {α : Type u} (t : ITree α) : (IForest.cons t (.cons t .nil)).length = 2 := by
  simp [IForest.length]

theorem IForest.length_eq {α : Type u} {n : Nat} (f : IForest α n) : f.length = n := by
  induction f with
  | nil => simp [IForest.length]
  | cons t f ih => simp_all [IForest.length]

/-- The binary tree, with vectors of length two. -/
def ITree.bin {α : Type u} (a : α) : ITree α :=
  ITree.corec (S := Unit) (fun _ => .node a 2 (.cons () (.cons () .nil))) ()

theorem ITree.bin_eq {α : Type u} (a : α) :
    ITree.bin a = .node a 2 (.cons (.bin a) (.cons (.bin a) .nil)) := by
  conv_lhs => rw [← ITree.ctor_dtor (ITree.bin a), ITree.bin, ITree.dtor_corec]
  simp [ITree.bin]

-- The other order: induction over trees through coinductive families of trees.
mixed_mutual
datatype JTree (α : Type u)
  | node (a : α) (n : Nat) (cs : JForest α n)
codatatype JForest (α : Type u) : Nat → Type u
  | nil : JForest α 0
  | cons {n : Nat} (t : JTree α) (f : JForest α n) : JForest α (n + 1)
end

/--
info: @JTree.rec : {α : Type u_2} →
  {motive : JTree α → Sort u_1} →
    ((a : α) → (n : ℕ) → (cs : JForest α n) → ((t : JTree α) → t ∈ cs → motive t) → motive (JTree.node a n cs)) →
      (t : JTree α) → motive t
-/
#guard_msgs in #check @JTree.rec
/--
info: @JForest.mem_cons : ∀ {α : Type u_1} {n : ℕ} (t : JTree α) (f : JForest α n) (x : JTree α),
  x ∈ JForest.cons t f ↔ x = t ∨ x ∈ f
-/
#guard_msgs in #check @JForest.mem_cons

/-- The labels of a tree's members, by induction through the forests: the hypothesis is for the
trees in the forest of children. -/
def JTree.firstLabel {α : Type u} (t : JTree α) : α :=
  JTree.rec (motive := fun _ => α) (fun a _ _ _ => a) t

example {α : Type u} (t : JTree α) : ∃ a n cs, t = .node a n cs := by
  induction t with
  | node a n cs ih => exact ⟨a, n, cs, rfl⟩

example {α : Type u} (a : α) : (JTree.node a 0 .nil).firstLabel = a := by
  simp [JTree.firstLabel]

end

end MixedIdxTest
