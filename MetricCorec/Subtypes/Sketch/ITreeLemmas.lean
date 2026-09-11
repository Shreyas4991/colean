import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Defs
import MetricCorec.Subtypes.Sketch.ITree

/-!
# What `ITree` supports beyond its corecursor

The label and the subtrees of a tree, and the isomorphism `ITree I α ≃ (List I → α)`: the final
coalgebra of `X ↦ α × (I → X)` is the type of functions on paths, for every `I`. An example
branching over `ℝ` closes the file.
-/

universe u v w

namespace ITree

variable {I : Type u} {α : Type v} {S : Type w}

theorem root_eq {t : Raw I α} (h : IsITree t) : ∃ a, t.root = some a := by
  rw [IsITree.eq_def] at h
  obtain ⟨a, c, rfl, -⟩ := h
  exact ⟨a, rfl⟩

theorem isITree_child {t : Raw I α} (h : IsITree t) (i : I) : IsITree (t.child i) := by
  rw [IsITree.eq_def] at h
  obtain ⟨a, c, rfl, hc⟩ := h
  exact hc i

/-- The `i`-th subtree. -/
def child (t : ITree I α) (i : I) : ITree I α := ⟨t.1.child i, isITree_child t.2 i⟩

theorem get_isSome (t : ITree I α) (p : List I) : (t.1.get p).isSome := by
  induction p generalizing t with
  | nil => obtain ⟨a, ha⟩ := root_eq t.2; simp [ha]
  | cons i p ih => exact ih (child t i)

/-- The label at a path. -/
def label (t : ITree I α) (p : List I) : α := (t.1.get p).get (get_isSome t p)

@[simp] theorem label_node_nil (a : α) (c : I → ITree I α) : label (node a c) [] = a := rfl
@[simp] theorem label_node_cons (a : α) (c : I → ITree I α) (i : I) (p : List I) :
    label (node a c) (i :: p) = label (c i) p := rfl

/-- A function on paths as a tree, by corecursion. -/
def ofFun (g : List I → α) : ITree I α := corec (fun g => (g [], fun i p => g (i :: p))) g

theorem label_ofFun (g : List I → α) : label (ofFun g) = g := by
  funext p
  induction p generalizing g with
  | nil => rfl
  | cons i p ih => exact ih fun p => g (i :: p)

theorem ofFun_label (t : ITree I α) : ofFun (label t) = t := by
  apply Subtype.ext
  refine Raw.eq_of_bisim (R := fun x y => ∃ t : ITree I α, x = (ofFun (label t)).1 ∧ y = t.1) ?_
    ⟨t, rfl, rfl⟩
  rintro _ _ ⟨t, rfl, rfl⟩
  refine ⟨?_, fun i => ⟨child t i, rfl, rfl⟩⟩
  show some (label t []) = t.1.root
  exact Option.some_get _

/-- `ITree I α` is `List I → α`. -/
def equivFun : ITree I α ≃ (List I → α) := ⟨label, ofFun, ofFun_label, label_ofFun⟩

/-! ### Branching over the reals -/

/-- A tree with a child for every real number: the label at path `[r₁, …, rₙ]` is the sum. -/
noncomputable def sums : ITree ℝ ℝ := corec (fun x => (x, fun r => x + r)) 0

example : label sums [1, 2, 3] = (0 + 1) + 2 + 3 := rfl

end ITree
