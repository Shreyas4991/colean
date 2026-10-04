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

theorem dist_def {α : Type} (p1 p2 : Partial α) : Dist.dist p1 p2 = dist p1 p2 := rfl

theorem dist_continuous {α : Type} : UniformContinuous₂ (@Partial.dist α) := by
  exact uniformContinuous₂_dist

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

def nodeUncurried {α : Type} : ((α × Partial α) × Partial α) → Partial α :=
    Function.uncurry <| Function.uncurry <| Partial.node

theorem nodeUncurried_AntiLipschitz {α : Type} :
    let _ : MetricSpace α := discreteMetricSpace;
    AntilipschitzWith 2 (@nodeUncurried α) := by
  intro _
  apply AntilipschitzWith.of_le_mul_dist
  intro ⟨⟨label1, left1⟩, right1⟩ ⟨⟨label2, left2⟩, right2⟩
  simp [Prod.dist_eq, nodeUncurried, discreteMetricSpace_dist_eq, Partial.dist_def, Partial.dist]
  split_ifs with h
  · simp [dist_nonneg]
  · grind [dist_le_one]

theorem nodeUncurried_continuous {α : Type} :
    let _ : MetricSpace α := discreteMetricSpace;
    UniformContinuous (@nodeUncurried α) := by
  intro _
  apply LipschitzWith.uniformContinuous (K := 1)
  rw [lipschitzWith_iff_dist_le_mul]
  intro ((label1, left1), right1) ((label2, left2), right2)
  simp [Partial.nodeUncurried, Prod.dist_eq, Partial.dist_def, -le_sup_iff, Partial.dist]
  split_ifs with h
  · subst h
    trans max (left1.dist left2) (right1.dist right2)
    · exact half_mul_le (le_sup_of_le_left (Partial.dist_nonneg _ _))
    · order
  · simp [discreteMetricSpace_dist_eq, h]

def todoDepth {α : Type} : Partial α → ℝ
  | todo => 1
  | node _ left right =>
    2⁻¹ * (todoDepth left ⊔ todoDepth right)

theorem todoDepth_nonneg {α : Type} (p : Partial α) : 0 ≤ p.todoDepth := by
  fun_induction todoDepth <;> grind

theorem todoDepth_le_one {α : Type} (p : Partial α) : p.todoDepth ≤ 1 := by
  fun_induction todoDepth <;> grind

theorem todoDepth_lipschitz {α : Type} : LipschitzWith 1 (@todoDepth α) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro p q
  simp [dist_def, Real.dist_eq]
  fun_induction p.dist q <;>
    grind [dist, todoDepth, Real.dist_eq, Dist.dist, todoDepth_nonneg,
      todoDepth_le_one, abs_eq_max_neg]

theorem todoDepth_continuous {α : Type} : UniformContinuous (@todoDepth α) :=
  todoDepth_lipschitz.uniformContinuous

end Partial

abbrev Complete (α : Type) : Type := Completion (Partial α)

namespace Complete

def todo {α : Type} : Complete α :=
  Completion.coe' .todo

def nodeUncurried {α : Type} : (α × Complete α) × Complete α → Complete α :=
  let _ : MetricSpace α := discreteMetricSpace
  have : DiscreteUniformity α := discreteMetricSpace_discrete
  (Completion.map Partial.nodeUncurried) ∘ iso
where
  iso [MetricSpace α] [DiscreteUniformity α] :
      (α × Complete α) × Complete α ≃ᵢ Completion ((α × Partial α) × Partial α) :=
    IsometryEquiv.trans (h₂ := PseudoMetricSpace.pullProdCompletion) <|
    IsometryEquiv.prodCongrLeft <|
    IsometryEquiv.trans (h₂ := PseudoMetricSpace.pullProdCompletion) <|
    IsometryEquiv.prodCongrLeft <|
    PseudoMetricSpace.completeEquivSelf.symm

def node {α : Type} (label : α) (left right : Complete α) : Complete α :=
  (Function.curry <| Function.curry <| nodeUncurried) label left right

theorem nodeUncurried_continuous {α : Type} :
    let _ : MetricSpace α := discreteMetricSpace;
    UniformContinuous (@nodeUncurried α) := by
  intro
  unfold nodeUncurried
  apply UniformContinuous.comp Completion.uniformContinuous_map
  apply IsometryEquiv.uniformContinuous

theorem nodeUncurried_AntiLipschitz {α : Type} :
    let _ : MetricSpace α := discreteMetricSpace;
    AntilipschitzWith 2 (@nodeUncurried α) := by
  intro
  unfold nodeUncurried
  rw [show (2 : NNReal) = 1 * 2 by simp]
  apply AntilipschitzWith.comp
  · apply AntilipschitzWith.completion_map Partial.nodeUncurried_AntiLipschitz
      Partial.nodeUncurried_continuous
  · exact (IsometryEquiv.isometry _).antilipschitz

theorem nodeUncurried_injective {α : Type} : Function.Injective (@nodeUncurried α) := by
  let _ : MetricSpace α := discreteMetricSpace
  have : DiscreteUniformity α := discreteMetricSpace_discrete
  apply nodeUncurried_AntiLipschitz.injective

inductive DestructType (α : Type)
| todo
| node (label : α) (left right : Complete α)

def construct {α : Type} (c : DestructType α) : Complete α :=
  match c with
  | .todo => .todo
  | .node label left right => .node label left right

theorem todo_neq_node {α : Type} {label : α} {left right : Complete α} :
    todo ≠ node label left right := by
  let _ : MetricSpace α := discreteMetricSpace
  have : DiscreteUniformity α := discreteMetricSpace_discrete
  suffices todo ∉ Set.range (Completion.map Partial.nodeUncurried) by
    contrapose! this
    rw [this]
    apply Set.mem_range_self
  apply coe_notMem_completion_range Partial.nodeUncurried_continuous
  simp [Partial.nodeUncurried, Partial.dist_def, Partial.dist]

theorem construct_injective {α : Type} : Function.Injective (@construct α) := by
  let _ : MetricSpace α := discreteMetricSpace
  have : DiscreteUniformity α := discreteMetricSpace_discrete
  intro d1 d2 h
  cases d1 with
  | todo =>
    cases d2 with
    | todo => rfl
    | node label2 left2 right2 =>
      exfalso
      change todo = node _ _ _ at h
      apply todo_neq_node h
  | node label1 left1 right1 =>
    cases d2 with
    | todo =>
      exfalso
      symm at h
      change todo = node _ _ _ at h
      apply todo_neq_node h
    | node label2 left2 right2 =>
      simp [construct, node] at h
      apply nodeUncurried_injective at h
      grind

instance (α : Type) : MetricSpace (DestructType α) :=
  MetricSpace.induced construct construct_injective inferInstance

instance (α : Type) : CompleteSpace (DestructType α) := by
  let _ : MetricSpace α := discreteMetricSpace
  have : DiscreteUniformity α := discreteMetricSpace_discrete
  suffices IsComplete (Set.range (@construct α)) by
    apply IsUniformInducing.completeSpace (f := @construct α)
    · exact (MetricSpace.isometry_induced _ construct_injective).isUniformInducing
    · exact this
  have : Set.range (@construct α) = {todo} ∪ Set.range (@nodeUncurried α) := by
    ext c
    constructor
    · rintro ⟨d, rfl⟩
      cases d with
      | todo => simp [construct]
      | node label left right => simp [construct, node]
    · rintro (rfl | ⟨⟨⟨label, left⟩, right⟩, rfl⟩)
      · use .todo
        rfl
      · use .node label left right
        rfl
  rw [this]
  apply IsComplete.union
  · exact isComplete_singleton
  · exact (nodeUncurried_AntiLipschitz.isUniformInducing nodeUncurried_continuous).isComplete_range

def destructPartial {α : Type} (p : Partial α) : DestructType α :=
  match p with
  | .todo => .todo
  | .node label left right => .node label (Completion.coe' left) (Completion.coe' right)

def destruct {α : Type} (c : Complete α) : DestructType α :=
  c.extension destructPartial

theorem dist_extension {α : Type} (x y : Complete α) :
    Completion.extension₂ Partial.dist x y = dist x y := by
  rfl

set_option linter.unusedSimpArgs false in
theorem destructPartial_isometry {α : Type} : Isometry (@destructPartial α) := by
  let _ : MetricSpace α := discreteMetricSpace
  have : DiscreteUniformity α := discreteMetricSpace_discrete
  apply Isometry.of_dist_eq
  intro p q
  simp [dist]
  cases p with
  | todo =>
    cases q with
    | todo =>
      simp [construct, todo, node, nodeUncurried, destructPartial,
        Completion.map_coe Partial.nodeUncurried_continuous,
        Completion.extension₂_coe_coe Partial.dist_continuous, nodeUncurried.iso]
    | node label2 left2 right2 =>
      simp [construct, todo, node, nodeUncurried, destructPartial,
        Completion.map_coe Partial.nodeUncurried_continuous,
        Completion.extension₂_coe_coe Partial.dist_continuous, nodeUncurried.iso]
      rfl
  | node label1 left1 right1 =>
    cases q with
    | todo =>
      simp [construct, todo, node, nodeUncurried, destructPartial,
        Completion.map_coe Partial.nodeUncurried_continuous,
        Completion.extension₂_coe_coe Partial.dist_continuous, nodeUncurried.iso]
      rfl
    | node label2 left2 right2 =>
      simp [construct, todo, node, nodeUncurried, destructPartial,
        Completion.map_coe Partial.nodeUncurried_continuous,
        Completion.extension₂_coe_coe Partial.dist_continuous, nodeUncurried.iso]
      rfl

theorem construct_destructPartial {α : Type} (p : Partial α) :
    construct (destructPartial p) = Completion.coe' p := by
  cases p with
  | todo => rfl
  | node label left right =>
    simp [construct, destructPartial, node, nodeUncurried, nodeUncurried.iso,
      Completion.map_coe Partial.nodeUncurried_continuous]
    rfl

theorem construct_destruct {α : Type} : Function.LeftInverse (@construct α) destruct := by
  let _ : MetricSpace α := discreteMetricSpace
  have : DiscreteUniformity α := discreteMetricSpace_discrete
  intro c
  induction c using Completion.induction_on with
  | hp =>
    apply isClosed_fixedPoints
    apply Continuous.comp' (MetricSpace.isometry_induced _ construct_injective).continuous
    apply UniformSpace.Completion.continuous_extension
  | ih p =>
    simp [destruct]
    rw [Completion.extension_coe destructPartial_isometry.uniformContinuous]
    cases p with
    | todo => rfl
    | node label left right =>
      simp [construct, node, nodeUncurried, destructPartial, nodeUncurried.iso,
        Completion.map_coe Partial.nodeUncurried_continuous]
      rfl

def equivDestruct {α : Type} : Complete α ≃ᵢ DestructType α where
  toFun := destruct
  invFun := construct
  right_inv :=
    Function.rightInverse_of_injective_of_leftInverse construct_injective construct_destruct
  left_inv := construct_destruct
  isometry_toFun :=
    Isometry.right_inv (MetricSpace.isometry_induced _ construct_injective) construct_destruct.rightInverse

#print axioms equivDestruct

@[simp]
theorem destruct_todo {α : Type} : destruct (@todo α) = .todo := by
  change equivDestruct _ = _
  apply_fun equivDestruct.symm
  simp only [IsometryEquiv.symm_apply_apply]
  rfl

theorem destruct_eq_todo {α : Type} {c : Complete α} (h : c.destruct = .todo) :
    c = todo := by
  change c.equivDestruct = .todo at h
  apply_fun equivDestruct.symm at h
  simp at h
  exact h

@[simp]
theorem destruct_node {α : Type} {label : α} {left right : Complete α} : destruct (node label left right) = .node label left right := by
  change equivDestruct _ = _
  apply_fun equivDestruct.symm
  simp only [IsometryEquiv.symm_apply_apply]
  rfl

theorem destruct_eq_node {α : Type} {c : Complete α} {label : α} {left right : Complete α}
    (h : c.destruct = .node label left right) :
    c = .node label left right := by
  change c.equivDestruct = _ at h
  apply_fun equivDestruct.symm at h
  simp at h
  exact h

@[elab_as_elim, cases_eliminator]
def casesOn {α : Type} {motive : Complete α → Sort*}
    (todo : motive (@todo α))
    (node : (label : α) → (left : Complete α) → (right : Complete α) → motive (node label left right))
    (t : Complete α) :
    motive t :=
  match h : destruct t with
  | .todo => (destruct_eq_todo h) ▸ todo
  | .node label left right => (destruct_eq_node h) ▸ node label left right

@[simp]
theorem todo_ne_node {α : Type} {label : α} {left right : Complete α} :
    Complete.todo ≠ Complete.node label left right := by
  apply_fun destruct
  simp

@[simp]
theorem node_ne_todo {α : Type} {label : α} {left right : Complete α} :
    Complete.node label left right ≠ .todo := by
  apply_fun destruct
  simp

@[simp]
theorem node_eq_node_iff {α : Type} {label1 label2 : α} {left1 left2 right1 right2 : Complete α} :
    node label1 left1 right1 = node label2 left2 right2 ↔ label1 = label2 ∧ left1 = left2 ∧ right1 = right2 where
  mpr h := by grind
  mp h := by
    apply_fun destruct at h
    simpa using h

def todoDepth {α : Type} : Complete α → ℝ :=
  Completion.extension Partial.todoDepth

theorem todoDepth_continuous {α : Type} :
    UniformContinuous (@todoDepth α) :=
  Completion.uniformContinuous_extension

theorem todoDepth_nonneg {α : Type} (c : Complete α) : 0 ≤ c.todoDepth := by
  induction c using Completion.induction_on with
  | hp => exact isClosed_le continuous_const todoDepth_continuous.continuous
  | ih p =>
    rw [todoDepth, Completion.extension_coe Partial.todoDepth_continuous]
    exact Partial.todoDepth_nonneg p

theorem todoDepth_todo {α : Type} : (@todo α).todoDepth = 1 := by
  rw [todo, todoDepth, Completion.extension_coe Partial.todoDepth_continuous]
  rfl

theorem todoDepth_node {α : Type} {label : α} {left right : Complete α} :
    (node label left right).todoDepth = 2⁻¹ * (left.todoDepth ⊔ right.todoDepth) := by
  let _ : MetricSpace α := discreteMetricSpace
  have hdu : DiscreteUniformity α := discreteMetricSpace_discrete
  simp [node, nodeUncurried, Function.curry_apply]

  generalize h : nodeUncurried.iso ((label, left), right) = x
  rw [show left = (nodeUncurried.iso.symm x).1.2 by simp [← h]]
  rw [show right = (nodeUncurried.iso.symm x).2 by simp [← h]]
  clear label left right h

  induction x using Completion.induction_on with
  | hp =>
    apply isClosed_eq
    · apply Continuous.comp
      · exact Completion.continuous_extension
      · exact Completion.continuous_map
    · apply Continuous.mul continuous_const
      apply Continuous.max
      · apply Continuous.comp
        · fun_prop
        · fun_prop
      · apply Continuous.comp
        · fun_prop
        · fun_prop
  | ih x =>
    simp [Completion.map_coe Partial.nodeUncurried_continuous, todoDepth,
      Completion.extension_coe Partial.todoDepth_continuous, nodeUncurried.iso]
    rfl

-- coinductive TodoFree (α : Type) : Complete α → Prop
-- | node {label left right} (h_left : TodoFree α left) (h_right : TodoFree α right) :
--     TodoFree α (node label left right)


-- #check TodoFree.casesOn

def TodoFree (α : Type) (c : Complete α) : Prop :=
  c.todoDepth = 0

theorem TodoFree.not_todo {α : Type} : ¬ TodoFree α (@todo α) := by
  grind [TodoFree, todoDepth_todo]

theorem TodoFree.node_iff {α : Type} {label : α} {left right : Complete α} :
    TodoFree α (.node label left right) ↔ TodoFree α left ∧ TodoFree α right := by
  grind [TodoFree, todoDepth_node, todoDepth_nonneg]

theorem TodoFree.node {α : Type} {label : α} {left right : Complete α}
    (h_left : TodoFree α left) (h_right : TodoFree α right) :
    TodoFree α (.node label left right) := by
  grind [TodoFree.node_iff]

theorem TodoFree.node_left {α : Type} {label : α} {left right : Complete α} (h : TodoFree α (.node label left right)) :
    TodoFree _ left := by
  grind [TodoFree.node_iff]

theorem TodoFree.node_right {α : Type} {label : α} {left right : Complete α} (h : TodoFree α (.node label left right)) :
    TodoFree _ right := by
  grind [TodoFree.node_iff]

theorem TodoFree.closed {α : Type} : IsClosed (TodoFree α) := by
  let _ : MetricSpace α := discreteMetricSpace
  have hdu : DiscreteUniformity α := discreteMetricSpace_discrete
  unfold TodoFree
  apply isClosed_eq _ continuous_const
  apply UniformSpace.Completion.continuous_extension

end Complete

end BinTree


def BinTree (α : Type) : Type := Subtype (BinTree.Complete.TodoFree α)

namespace BinTree

variable {α : Type}

instance : MetricSpace (BinTree α) := Subtype.metricSpace

instance : CompleteSpace (BinTree α) := by
  apply IsComplete.completeSpace_coe
  apply IsClosed.isComplete
  exact Complete.TodoFree.closed

instance : BoundedSpace (BinTree α) := instBoundedSpaceSubtype

def node (label : α) (left right : BinTree α) : BinTree α where
  val := Complete.node label left.val right.val
  property := Complete.TodoFree.node left.prop right.prop

inductive DestructType (α : Type)
| node (label : α) (left right : BinTree α)

def construct (d : DestructType α) : BinTree α :=
  match d with
  | .node label left right => .node label left right

set_option linter.unnecessarySeqFocus false in
theorem construct_injective : Function.Injective (@construct α) := by
  intro x y h
  apply_fun (Complete.destruct ∘ Subtype.val) at h
  cases x <;> cases y <;> simpa [construct, node, ← Subtype.ext_iff] using h

instance : MetricSpace (DestructType α) :=
  MetricSpace.induced construct construct_injective inferInstance

def destruct (t : BinTree α) : DestructType α :=
  match h : t.val.destruct with
  | .todo => False.elim (by
      obtain ⟨t, ht⟩ := t
      simp at h
      apply Complete.destruct_eq_todo at h
      simp [h, Complete.TodoFree.not_todo] at ht
    )
  | .node label left right =>
    have h' := Complete.destruct_eq_node h
    .node label ⟨left, (h' ▸ t.prop).node_left⟩ ⟨right, (h' ▸ t.prop).node_right⟩

def destructEquiv : BinTree α ≃ DestructType α where
  toFun := destruct
  invFun := construct
  left_inv t := by
    fun_cases destruct t with
    | case1 label left right h_destruct h =>
      simp [construct, node]
      apply Subtype.ext h.symm
  right_inv d := by
    cases d with
    | node label' left' right' =>
      simp [construct]
      fun_cases destruct with
      | case1 label left right h h' =>
        simp
        rw [Subtype.ext_iff, Subtype.ext_iff]
        simp [node] at h'
        simp [h']

end BinTree

end