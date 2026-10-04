import Mathlib
import Colean.Lemmas
import Colean.CompletionBounded
import Colean.MapDiscreteCompl

/-
## Example 2: Infinite binary tree

coinductive BinTree (α : Type)
| node (label : α) (left right : BinTree α)
-/

open UniformSpace

noncomputable section
open Classical

namespace BinTree

inductive Partial (α : Type)
| todo
| node (label : α) (left right : Partial α)
deriving Inhabited


namespace Partial


def dist {α : Type} : Partial α → Partial α → ℝ
| .todo, .todo => 0
| .node v1 l1 r1, .node v2 l2 r2 =>
  if v1 = v2 then
    2⁻¹ * (dist l1 l2 ⊔ dist r1 r2)
  else
    1
| _, _ => 1

theorem dist_nonneg {α : Type} (p1 p2 : Partial α) : 0 ≤ dist p1 p2 := by
  fun_induction dist p1 p2 <;> grind

theorem dist_le_one {α : Type} (p1 p2 : Partial α) : dist p1 p2 ≤ 1 := by
  fun_induction dist p1 p2 <;> grind

example (x y a b : ℝ) (h : x = a ∧ y = b) : x + y = a + b := by simp only [h]

theorem dist_ultra {α : Type} (p1 p2 p3 : Partial α) : dist p1 p3 ≤ dist p1 p2 ⊔ dist p2 p3 :=
  match p1, p2, p3 with
  -- when `p1` and `p2` constructors are different RHS is 1, so it's trivial
  | .todo, .node v2 l2 r2, .todo => (dist_le_one _ _).trans (le_max_left _ _)
  | .todo, .node v2 l2 r2, .node v3 l3 r3 => (dist_le_one _ _).trans (le_max_left _ _)
  | .node v1 l1 r1, .todo, .todo => (dist_le_one _ _).trans (le_max_left _ _)
  | .node v1 l1 r1, .todo, .node v3 l3 r3 => (dist_le_one _ _).trans (le_max_left _ _)
  -- when `p2` and `p3` constructors are different, RHS is 1, so it's trivial
  | .todo, .todo, .node v3 l3 r3 => (dist_le_one _ _).trans (le_max_right _ _)
  | .node v1 l1 r1, .node v2 l2 r2, .todo => (dist_le_one _ _).trans (le_max_right _ _)
  -- the only cases left is when they all have the same constructor
  -- if there is no non-recursive arguments then LHS is zero
  | .todo, .todo, .todo => (dist_nonneg _ _).trans (le_max_left _ _)
  -- if there are non-recursive argument, we need to split if-then-else
  | .node v1 l1 r1, .node v2 l2 r2, .node v3 l3 r3 =>
    -- if `p1` and `p2` args don't concide, the RHS is 1
    if h12 : ¬ v1 = v2 then
      (dist_le_one _ _).trans (le_max_of_le_left (by simp [dist, h12]))
    -- if `p2` and `p3` args don't concide, the RHS is 1
    else if h23 : ¬ v2 = v3 then
      (dist_le_one _ _).trans (le_max_of_le_right (by simp [dist, h23]))
    -- if `p1`, `p2`, `p3` args concide we navigate to the first branch of `if-then-else` in
    -- `dist`, cancel `2⁻¹` multiplier and use `order` with "inductive" calls
    -- to recursive arguments
    else by
      simp only [dist, of_not_not h12, of_not_not h23, ↓reduceIte, half_sup_le_sup_halves]
      order [dist_ultra l1 l2 l3, dist_ultra r1 r2 r3]

instance {α : Type} : MetricSpace (Partial α) where
  dist := dist
  dist_self p := by induction p <;> grind [dist]
  dist_comm p1 p2 := by induction p1 generalizing p2 <;> induction p2 <;> grind [dist]
  dist_triangle p1 p2 p3 :=
    (dist_ultra p1 p2 p3).trans <| max_le_add_of_nonneg (dist_nonneg p1 p2) (dist_nonneg p2 p3)
  eq_of_dist_eq_zero := by
    intro p1 p2
    have := @dist_nonneg
    fun_induction p1.dist p2 <;> grind

instance {α : Type} : BoundedSpace (Partial α) :=
  Metric.boundedSpace_iff.mpr ⟨1, dist_le_one⟩


def depth {α : Type} (p : Partial α) : ℕ :=
  match p with
  | .todo => 0
  | .node _ left right =>
    left.depth ⊔ right.depth + 1

theorem eq_of_dist_lt_half_pow_depth {α : Type} (p q : Partial α) (h : dist p q < 2⁻¹ ^ p.depth) : p = q :=
  match p, q with
  | .todo, .todo => rfl
  | .todo, .node _ _ _ => False.elim (h.not_ge half_pow_le_one)
  | .node _ _ _, .todo => False.elim (h.not_ge half_pow_le_one)
  | .node p_label p_left p_right, .node q_label q_left q_right =>
    if h_if : p_label = q_label then
      by
        simp only [dist, depth, h_if, pow_succ', ↓reduceIte, mul_lt_mul_iff_right₀ half_pos', sup_lt_iff, half_pow_sup_eq] at h
        repeat apply congr
        · rfl
        · exact h_if
        · exact eq_of_dist_lt_half_pow_depth _ _ (by order)
        · exact eq_of_dist_lt_half_pow_depth _ _ (by order)
    else
      False.elim <| h.not_ge (half_pow_le_one' (by simp [dist, h_if]))


instance {α : Type} : DiscreteTopology (Partial α) :=
  DiscreteTopology.of_all_isolated fun p ↦
    ⟨2⁻¹ ^ p.depth, pow_pos half_pos' _, eq_of_dist_lt_half_pow_depth p⟩

def ContainsTodo (α : Type) : Set (Partial α)
| .todo => True
| .node _ l r => ContainsTodo α l ∨ ContainsTodo α r

@[simp]
theorem todo_ContainsTodo (α : Type) : todo ∈ ContainsTodo α := by
  change ContainsTodo α todo
  simp [ContainsTodo]

@[simp]
theorem node_ContainsTodo_iff (α : Type) (v : α) (l r : Partial α) :
    node v l r ∈ ContainsTodo α ↔ l ∈ ContainsTodo α ∨ r ∈ ContainsTodo α := by
  sorry

end Partial

abbrev Complete (α : Type) : Type := Completion (Partial α)

namespace Complete

def ContainsTodo (α : Type) : Set (Complete α) := Completion.coe' '' (Partial.ContainsTodo α)

#synth UniformSpace (Complete Nat → Complete Nat)

def todo {α : Type} : Complete α :=
  Completion.coe' .todo

-- def node {α : Type} : α → Complete α → Complete α → Complete α :=
--   fun label ↦ Completion.extension fun left ↦ Completion.extension fun right ↦
--     Completion.coe' <| Partial.node label left right

def node {α : Type} (label : α) (left right : Complete α) : Complete α :=
  left.extension fun left => right.extension fun right =>
    Completion.coe' <| Partial.node label left right

theorem node_left_uniform_continuous {α : Type} {label : α} {left : Partial α} :
    UniformContinuous (fun right => Completion.coe' <| Partial.node label left right) := by
  apply UniformContinuous.comp (Completion.uniformContinuous_coe _)
  sorry

theorem node_uniform_continuous {α : Type} {label : α} {right : Complete α} :
    UniformContinuous (fun left => right.extension fun right =>
      Completion.coe' <| Partial.node label left right) := by
  sorry

-- theorem node_not_ContainsTodo {α : Type} (label : α) (left right : Complete α)
--     (h_left : left ∉ ContainsTodo _) (h_right : right ∉ ContainsTodo _) :
--     node label left right ∉ ContainsTodo _ := by
--   let : TopologicalSpace α := ⊥
--   have : DiscreteTopology α := ⟨rfl⟩
--   intro ⟨res, h_bad, h_eq⟩
--   let S : Set ((α × Complete α) × Complete α) :=
--     Set.preimage (Function.uncurry (Function.uncurry node)) {Completion.coe' res}
--   have hS_open : IsOpen S := by
--     apply IsOpen.preimage
--     ·
--     sorry -- as preimage of open {res}
--   let P : Set (α × Complete α × Complete α) :=
--     {(label, left, right) | (∃ left' : Partial α, left = left') ∧ (∃ right' : Partial α, right = right')}

--   have hP_dense : Dense P := by
--     sorry -- standard
--   by_cases h : (label, left, right) ∈ P
--   · obtain ⟨⟨left', rfl⟩, ⟨right', rfl⟩⟩ := h
--     rw [node, Completion.extension_coe node_uniform_continuous,
--       Completion.extension_coe node_left_uniform_continuous, Completion.coe_inj] at h_eq
--     simp [ContainsTodo] at h_left h_right
--     simp [h_eq] at h_bad
--     grind
--   · obtain ⟨⟨label1, _, _⟩, ⟨⟨⟨left1, rfl⟩, ⟨right1, rfl⟩⟩, h_eq1⟩, ⟨label2, _, _⟩, ⟨⟨⟨⟨left2, rfl⟩, ⟨right2, rfl⟩⟩, h_eq2⟩, h_neq⟩⟩ :=
--       hP_dense.inter_open_infinite hS_open ⟨(label, left, right), ⟨h_eq.symm, h⟩⟩ |>.nontrivial
--     change node label1 left1 right1 = res at h_eq1
--     change node label2 left2 right2 = res at h_eq2
--     rw [node, Completion.extension_coe node_uniform_continuous,
--       Completion.extension_coe node_left_uniform_continuous, Completion.coe_inj] at h_eq1 h_eq2
--     grind

theorem node_not_ContainsTodo {α : Type} (label : α) (left right : Complete α)
    (h_left : left ∉ ContainsTodo _) (h_right : right ∉ ContainsTodo _) :
    node label left right ∉ ContainsTodo _ := by
  intro ⟨res, h_bad, h_eq⟩
  let S : Set (α × Complete α × Complete α) :=
    {(label, left, right) | node label left right = res}
  let P : Set (α × Complete α × Complete α) :=
    {(label, left, right) | (∃ left' : Partial α, left = left') ∧ (∃ right' : Partial α, right = right')}
  let : TopologicalSpace α := ⊥
  have : DiscreteTopology α := ⟨rfl⟩
  have hS_open : IsOpen S := by
    sorry -- as preimage of open {res}
  have hP_dense : Dense P := by
    sorry -- standard
  by_cases h : (label, left, right) ∈ P
  · obtain ⟨⟨left', rfl⟩, ⟨right', rfl⟩⟩ := h
    rw [node, Completion.extension_coe node_uniform_continuous,
      Completion.extension_coe node_left_uniform_continuous, Completion.coe_inj] at h_eq
    simp [ContainsTodo] at h_left h_right
    simp [h_eq] at h_bad
    grind
  · obtain ⟨⟨label1, _, _⟩, ⟨⟨⟨left1, rfl⟩, ⟨right1, rfl⟩⟩, h_eq1⟩, ⟨label2, _, _⟩, ⟨⟨⟨⟨left2, rfl⟩, ⟨right2, rfl⟩⟩, h_eq2⟩, h_neq⟩⟩ :=
      hP_dense.inter_open_infinite hS_open ⟨(label, left, right), ⟨h_eq.symm, h⟩⟩ |>.nontrivial
    change node label1 left1 right1 = res at h_eq1
    change node label2 left2 right2 = res at h_eq2
    rw [node, Completion.extension_coe node_uniform_continuous,
      Completion.extension_coe node_left_uniform_continuous, Completion.coe_inj] at h_eq1 h_eq2
    grind


-- theorem node_not_ContainsTodo {α : Type} (label : α) (left right : Complete α)
--     (h_left : left ∉ ContainsTodo _) (h_right : right ∉ ContainsTodo _) :
--     node label left right ∉ ContainsTodo _ := by
--   unfold node
--   have h1 : ∀ left ∉ Partial.ContainsTodo _, ∀ right ∉ Partial.ContainsTodo _,
--       ↑(Partial.node label left right) ∉ Complete.ContainsTodo α := by
--     intro left hleft right hright
--     simp [ContainsTodo, hleft, hright]
--   have h2 : ∀ left ∉ Partial.ContainsTodo _,
--       Completion.extension (fun right => ↑(Partial.node label left right)) right ∉ Complete.ContainsTodo α := by
--     intro left h_left
--     replace h1 := h1 left h_left
--     set g := fun (right : Partial α) ↦ Completion.coe' (Partial.node label left right)
--     change ∀ right ∉ Partial.ContainsTodo α, g right ∉ ContainsTodo α at h1
--     apply extension_notMem_of_discrete_topology h1 _ _ h_right
--     · sorry
--     · sorry
--   have h3 :
--       Completion.extension (fun left => Completion.extension (fun right => ↑(Partial.node label left right))) left right ∉ Complete.ContainsTodo α := by
--     -- intro left hleft right hright
--     replace h2 := fun left hleft ↦ h2 left hleft
--     set g := fun (left : Partial α) ↦ Completion.extension fun right => Completion.coe' (Partial.node label left right)
--     change ∀ left ∉ Partial.ContainsTodo α, g left right ∉ ContainsTodo α at h2

--     apply extension_notMem_of_discrete_topology
--     sorry
--     -- change Completion.extension (fun left => g left) left right ∉ Complete.ContainsTodo α
--   exact h3


-- theorem node_not_ContainsTodo_aux {α : Type} (c : Complete α) (h : c ∉ ContainsTodo α)
--     (f : Partial α → Complete α) (hf_cont : UniformContinuous f)
--     (hf : ∀ p ∉ Partial.ContainsTodo _, f p ∉ ContainsTodo _) :
--     c.extension f ∉ ContainsTodo α := by
--   induction c using Completion.induction_on with
--   | hp =>
--     sorry
--   | ih p =>
--     simp [ContainsTodo] at h
--     rw [Completion.extension_coe hf_cont]
--     grind

-- theorem node_not_ContainsTodo {α : Type} (label : α) (left right : Complete α)
--     (h_left : left ∉ ContainsTodo _) (h_right : right ∉ ContainsTodo _) :
--     node label left right ∉ ContainsTodo _ := by
--   unfold node
--   have h1 : ∀ left ∉ Partial.ContainsTodo _, ∀ right ∉ Partial.ContainsTodo _,
--       Completion.coe' (Partial.node label left right) ∉ Complete.ContainsTodo α := by
--     intro left hleft right hright
--     simp [ContainsTodo, hleft, hright]
--   have h2 : ∀ left ∉ Partial.ContainsTodo _,
--       (right.extension fun right => ↑(Partial.node label left right)) ∉ Complete.ContainsTodo α := by
--     intro left hleft
--     specialize h1 left hleft
--     apply extension_notMem_of_discrete_topology h1 _ sorry h_right
--     change UniformContinuous <| Completion.coe' ∘ (fun right => Partial.node label left right)
--     apply UniformContinuous.comp (Completion.uniformContinuous_coe _)
--     sorry -- easy
--   have h3 : left.extension (fun left => right.extension fun right => ↑(Partial.node label left right)) ∉ Complete.ContainsTodo α := by
--     apply extension_notMem_of_discrete_topology h2 _ sorry h_left
--     change UniformContinuous fun a => right.extension (fun right => Completion.coe' (Partial.node label a right))
--     change UniformContinuous <| (fun (f : Partial α → Partial α) => right.extension (fun right => Completion.coe' (f right))) ∘ (fun left => Partial.node label left)
--     apply UniformContinuous.comp
--     · sorry
--       -- change UniformContinuous fun f => Completion.extension (fun right => ↑(f right)) right
--     · sorry
--   exact h3

inductive DestructType (α : Type)
| todo
| node (label : α) (left right : Complete α)

def DestructType.construct {α : Type} : DestructType α → Complete α
  | .todo => .todo
  | .node label left right => .node label left right

theorem DestructType.construct_injective {α : Type} : Function.Injective (@construct α) := by
  sorry

instance {α : Type} : MetricSpace (DestructType α) :=
  MetricSpace.induced DestructType.construct DestructType.construct_injective inferInstance

def DestructType.fromPartial {α : Type} : Partial α → DestructType α
  | .todo => .todo
  | .node label left right => .node label (Completion.coe' left) (Completion.coe' right)

theorem DestructType.fromPartial_continuous {α : Type} : UniformContinuous (@DestructType.fromPartial α) := by
  sorry

def destruct {α : Type} (c : Complete α) : DestructType α :=
  c.extension DestructType.fromPartial

theorem destruct_todo {α : Type} : destruct (@Complete.todo α) = DestructType.todo := by
  simp [Complete.todo, destruct, UniformSpace.Completion.extension_coe DestructType.fromPartial_continuous]
  rfl

theorem destruct_node {α : Type} (label : α) (left right : Complete α) :
    destruct (node label left right) = DestructType.node label left right := by
  induction left, right using Completion.induction_on₂ with
  | hp =>
    
  -- simp [Complete.node, destruct]

def casesOn {α : Type} {motive : Complete α → Sort*}
    (leaf : motive (@todo α))
    (node : (label : α) → (left : Complete α) → (right : Complete α) → motive (node label left right))
    (t : Complete α) :
    motive t :=
  t.extension fun t => by sorry


end Complete

end BinTree

def BinTree (α : Type) : Type := {c : BinTree.Complete α // c ∉ BinTree.Complete.ContainsTodo α}

instance (α : Type) : MetricSpace (BinTree α) := Subtype.metricSpace

instance (α : Type) : CompleteSpace (BinTree α) := sorry -- use closedness of ContainsTodo

instance (α : Type) : BoundedSpace (BinTree α) := instBoundedSpaceSubtype

namespace BinTree

def node {α : Type} : α → BinTree α → BinTree α → BinTree α :=
  fun label ↦ fun ⟨left, h_left⟩ ↦ left.extension (by sorry)


-- def node {α : Type} (label : α) (left right : BinTree α) : BinTree α where
--   val := Complete.node label left.val right.val
--   property := Complete.node_not_ContainsTodo _ _ _ left.property right.property

inductive DestructType (α : Type)
| node (label : α) (left right : BinTree α)

namespace DestructType

variable {α : Type}

def construct (d : DestructType α) : BinTree α :=
  match d with
  | .node label left right => .node label left right

instance : MetricSpace (DestructType α) :=
  MetricSpace.induced construct sorry inferInstance

end DestructType

-- def destructAux {α : Type} (t : Complete α) : Option (DestructType α) :=
--   t.extension fun t =>
--     sorry

def destruct {α : Type} (t : BinTree α) : DestructType α :=
  t.val.extension fun t =>
    match t with
    | .node label left right => .node label (Completion.coe' left) right

end BinTree

end
