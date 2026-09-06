import Mathlib
import MetricCorec.StrictDiscrete
import MetricCorec.MapDiscreteCompl

/-
## Example 1: CoList

coinductive CoList (α : Type)
| nil
| cons (hd : α) (tl : CoList α)
-/


-- Step 1. Define `T.Partial` as inductive with extra constructor
inductive CoList.Partial (α : Type)
| nil
| cons (hd : α) (tl : CoList.Partial α)
| todo

instance {α : Type} : Nontrivial (CoList.Partial α) where
  exists_pair_ne := ⟨.todo, .nil, by simp⟩

@[simp]
theorem Nontrivial.not_all_eq {β : Type*} [Nontrivial β] (b : β) :
    ¬ ∀ x, x = b := by push_neg; exact exists_ne b

-- Step 2. Establish a metric space structure and prove constructors are continuous
open Classical in
noncomputable def CoList.Partial.dist {α : Type} : CoList.Partial α → CoList.Partial α → ℝ
  | .todo, .todo => 0
  | .nil, .nil => 0
  | .cons hd₁ tl₁, .cons hd₂ tl₂ =>
    if hd₁ = hd₂ then
      (1 / 2) * dist tl₁ tl₂
    else
      1
  | _, _ => 1

@[grind .]
theorem CoList.Partial.dist_nonneg {α : Type} (x y : CoList.Partial α) :
    0 ≤ x.dist y := by fun_induction x.dist y <;> grind

@[grind .]
theorem CoList.Partial.dist_le_one {α : Type} (x y : CoList.Partial α) :
    x.dist y ≤ 1 := by fun_induction x.dist y <;> grind

theorem CoList.Partial.dist_ultrametric {α : Type} (x y z : CoList.Partial α) :
    x.dist z ≤ x.dist y ⊔ y.dist z := by
  induction x generalizing y z <;> induction y generalizing z <;> induction z <;>
    grind [CoList.Partial.dist]



noncomputable instance {α : Type} : MetricSpace (CoList.Partial α) where
  dist := CoList.Partial.dist
  dist_self x := by
    induction x <;> grind [CoList.Partial.dist]
  dist_comm x y := by
    induction x generalizing y <;> induction y <;> grind [CoList.Partial.dist]
  dist_triangle x y z := by
    apply (CoList.Partial.dist_ultrametric x y z).trans
    apply max_le_add_of_nonneg <;> grind
  eq_of_dist_eq_zero := by
    intro x y h
    fun_induction x.dist y <;> grind

@[grind .]
theorem CoList.Partial.dist_le_one' {α : Type} (x y : CoList.Partial α) :
    Dist.dist x y ≤ 1 := CoList.Partial.dist_le_one x y

instance {α : Type} : BoundedSpace (CoList.Partial α) := by
  rw [Metric.boundedSpace_iff]
  use 1
  intro x y
  apply CoList.Partial.dist_le_one

theorem CoList.Partial.dist_def {α : Type} (x y : CoList.Partial α) :
    Dist.dist x y = x.dist y := rfl

theorem CoList.Partial.cons_lipschitz {α : Type} (hd : α) :
    LipschitzWith (1 / 2) (CoList.Partial.cons hd) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp [CoList.Partial.dist_def, dist]

theorem CoList.Partial.cons_continuous {α : Type} (hd : α) :
    Continuous (CoList.Partial.cons hd) :=
  LipschitzWith.continuous (CoList.Partial.cons_lipschitz _)

-- Step 3. Define `T.Completion`
-- abbrev CoList.Completion (α : Type) : Type := UniformSpace.Completion (CoList.Partial α)

open UniformSpace

-- TODO: upstream
instance {α : Type} [PseudoMetricSpace α] [BoundedSpace α] :
    BoundedSpace (Completion α) := by
  constructor
  rw [← DenseRange.closure_range (Completion.denseRange_coe)]
  apply Bornology.IsBounded.closure
  rw [← Set.image_univ]
  exact Completion.coe_isometry.lipschitz.isBounded_image BoundedSpace.bounded_univ

-- #synth BoundedSpace (UniformSpace.Completion (CoList.Partial Nat))

-- Step 4. Define `ToDoFree` subtype and the target type
def CoList.ContainsTodo (α : Type) : Set (CoList.Partial α)
  | .todo => True
  | .nil => False
  | .cons _ tl => ContainsTodo _ tl

@[simp]
theorem CoList.todo_mem_ContainsTodo {α : Type} : .todo ∈ ContainsTodo α := by
  change ContainsTodo α .todo
  simp [ContainsTodo]

@[simp]
theorem CoList.not_notMem_ContainsTodo {α : Type} : .nil ∉ ContainsTodo α := by
  change ¬ ContainsTodo α .nil
  simp [ContainsTodo]

@[simp]
theorem CoList.cons_mem_ContainsTodo_iff {α : Type} {hd : α} {tl : CoList.Partial α} :
    .cons hd tl ∈ ContainsTodo α ↔ tl ∈ ContainsTodo α := by
  change ContainsTodo α (.cons hd tl) ↔ ContainsTodo α tl
  simp [ContainsTodo]

def CoList (α : Type) : Type :=
  ((UniformSpace.Completion.coe' '' (CoList.ContainsTodo α))ᶜ : Set _)

noncomputable instance (α : Type) : MetricSpace (CoList α) :=
  Subtype.metricSpace

theorem CoList.ContainsTodo_isStrictDiscrete {α : Type} :
    IsStrictDiscreteSet (CoList.ContainsTodo α) := by
  intro x hx
  induction x with
  | todo =>
    clear hx
    have : ({Partial.todo} : Set (Partial α)) = Metric.ball Partial.todo (1/2) := by
      ext x
      simp
      refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
      cases x with
      | todo => rfl
      | nil => norm_num [CoList.Partial.dist_def, CoList.Partial.dist] at h
      | cons => norm_num [CoList.Partial.dist_def, CoList.Partial.dist] at h
    rw [this]
    exact Metric.isOpen_ball
  | nil => simp at hx
  | cons hd tl ih =>
    simp at hx
    specialize ih hx
    simp [Metric.isOpen_iff] at ih ⊢
    obtain ⟨ε, hε, h_tl⟩ := ih
    use ε / 2, by linarith
    intro y hy
    cases y with
    | todo =>
      simp [CoList.Partial.dist_def, CoList.Partial.dist] at hy
      have : ∀ y, dist y tl < ε := by
        intro y
        linarith [CoList.Partial.dist_le_one' y tl]
      simp [this] at h_tl
    | nil =>
      simp [CoList.Partial.dist_def, CoList.Partial.dist] at hy
      have : ∀ y, dist y tl < ε := by
        intro y
        linarith [CoList.Partial.dist_le_one' y tl]
      simp [this] at h_tl
    | cons hd' tl' =>
      simp [CoList.Partial.dist_def, CoList.Partial.dist] at hy
      split_ifs at hy with h_if
      · subst h_if
        congr
        apply h_tl
        simp [CoList.Partial.dist_def]
        linarith
      · have : ∀ y, dist y tl < ε := by
          intro y
          linarith [CoList.Partial.dist_le_one' y tl]
        simp [this] at h_tl

instance (α : Type) :
    IsClosed (Completion.coe' '' CoList.ContainsTodo α)ᶜ where
  isOpen_compl := by
    simp
    apply IsStrictDiscreteSet.isOpen
    apply IsStrictDiscreteSet.image
    · exact CoList.ContainsTodo_isStrictDiscrete
    · exact Completion.isDenseInducing_coe

instance (α : Type) : CompleteSpace (CoList α) := IsClosed.completeSpace_coe

instance (α : Type) : BoundedSpace (CoList α) := instBoundedSpaceSubtype

-- Step 5. Define constructors & casesOn
noncomputable def CoList.nil {α : Type} : CoList α where
  val := Completion.coe' <| CoList.Partial.nil
  property := by
    simp

noncomputable def CoList.cons {α : Type} (hd : α) (tl : CoList α) : CoList α :=
  tl.map (Completion.map (CoList.Partial.cons hd)) (by
    have := map_discrete_compl_subset (@CoList.ContainsTodo_isStrictDiscrete α) (Partial.cons hd)
      ((CoList.Partial.cons_lipschitz hd).uniformContinuous)
      (by unfold Function.Injective; grind)
      (by intro x; simp)
    grind
  )

#check Stream'.Seq.recOn

#check UniformSpace.Completion.induction_on

#check UniformSpace.Completion.induction_on₃

theorem CoList.eq_nil_of_dist_lt_one {α : Type} (s : CoList α) (h : dist s nil < 1) :
    s = nil := by
  obtain ⟨s, hs⟩ := s
  rw [Subtype.ext_iff]
  rw [Subtype.dist_eq] at h
  simp [nil] at h ⊢
  clear hs
  induction s using UniformSpace.Completion.induction_on with
  | hp =>
    apply isClosed_imp
    · sorry
    · simp
  | ih p =>
    simp at h ⊢
    cases p <;> simp [CoList.Partial.dist_def, CoList.Partial.dist] at h
    rfl

theorem CoList.cons_ext_iff {α : Type} {x y : α} {xs ys : CoList α} :
    CoList.cons x xs = cons y ys ↔ x = y ∧ xs = ys := by
  refine ⟨fun h ↦ ?_, fun h ↦ by grind⟩
  obtain ⟨xs, hxs⟩ := xs
  obtain ⟨ys, hys⟩ := ys
  rw [Subtype.ext_iff] at h ⊢
  simp [cons] at h ⊢
  clear hxs hys
  -- revert xs ys
  induction xs, ys using Completion.induction_on₂ with
  | hp =>
    by_cases h : x = y <;> simp [h]
    · sorry
    · sorry
  | ih xs ys =>
    simp [UniformSpace.Completion.map_coe (CoList.Partial.cons_lipschitz _).uniformContinuous] at *
    grind


theorem CoList.nil_ne_cons {α : Type} {hd : α} {tl : CoList α} :
    nil ≠ cons hd tl := by
  simp [nil, cons]
  rw [Subtype.ext_iff]
  simp
  obtain ⟨tl, h_tl⟩ := tl
  simp
  clear h_tl
  induction tl using Completion.induction_on with
  | hp =>
    convert_to IsClosed <| (Completion.map (Partial.cons hd) ⁻¹' {Completion.coe' Partial.nil})ᶜ
    · ext tl
      grind
    simp
    apply Continuous.isOpen_preimage
    · apply UniformSpace.Completion.continuous_map
    · sorry
  | ih tl =>
    simp [UniformSpace.Completion.map_coe (CoList.Partial.cons_lipschitz _).uniformContinuous]

theorem CoList.nil_or_cons {α : Type} (s : CoList α) :
    s = nil ∨ ∃ hd tl, s = cons hd tl := by
  obtain ⟨s, hs⟩ := s
  induction s using Completion.induction_on with
  | hp =>
    conv =>
      arg 1; ext a; arg 1; ext a; ext hs; rw [Subtype.ext_iff, nil]; simp;
      arg 2; arg 1; ext hd; arg 1; ext tl; rw [Subtype.ext_iff, cons]; simp;
    simp
    apply isClosed_imp
    · sorry
    · apply IsClosed.union
      · apply isClosed_singleton
      · sorry
  | ih s =>
    induction s with
    | todo => simp at hs
    | nil => simp [nil]
    | cons hd tl ih =>
      right
      use hd
      simp at ih
      specialize ih (by simpa using hs)
      obtain ih | ⟨tl_hd, ⟨tl_tl, h_tl_tl⟩, ih⟩ := ih
      · use nil
        rw [Subtype.ext_iff] at ih ⊢
        simp [nil] at ih ⊢
        subst ih
        simp [cons]
        rw [UniformSpace.Completion.map_coe]
        apply (CoList.Partial.cons_lipschitz _).uniformContinuous
      use cons tl_hd ⟨tl_tl, h_tl_tl⟩
      rw [Subtype.ext_iff] at ih ⊢
      simp [cons] at ih ⊢
      rw [← ih]
      rw [UniformSpace.Completion.map_coe]
      apply (CoList.Partial.cons_lipschitz _).uniformContinuous

open Classical in
noncomputable def CoList.casesOn {α : Type} {motive : CoList α → Sort*}
    (nil : motive CoList.nil)
    (cons : (hd : α) → (tl : CoList α) → motive (CoList.cons hd tl)) (s : CoList α) :
    motive s :=
  if h : s = CoList.nil then
    h ▸ nil
  else
    have h' : ∃ hd tl, s = CoList.cons hd tl := by grind [CoList.nil_or_cons s]
    let hd := h'.choose
    let tl := h'.choose_spec.choose
    h'.choose_spec.choose_spec ▸ cons hd tl

theorem CoList.casesOn_nil {α : Type} {motive : CoList α → Sort*}
    {nil : motive CoList.nil}
    {cons : (hd : α) → (tl : CoList α) → motive (CoList.cons hd tl)} :
    CoList.casesOn nil cons CoList.nil = nil := by
  simp [casesOn]

theorem CoList.casesOn_cons {α : Type} {motive : CoList α → Sort*}
    {nil : motive CoList.nil}
    {cons : (hd : α) → (tl : CoList α) → motive (CoList.cons hd tl)}
    (hd : α) (tl : CoList α) :
    CoList.casesOn nil cons (CoList.cons hd tl) = cons hd tl := by
  simp [casesOn, CoList.nil_ne_cons.symm]
  generalize_proofs h2 h1 h3
  obtain ⟨h4, h5⟩ := CoList.cons_ext_iff.mp h3
  grind

/-
## Example 2: Infinite binary tree

coinductive BinTree (α : Type)
| node (label : α) (left right : BinTree α)
-/

/-
## Example 3: trees with bounded depth and unbounded branching

coinductive Tree : Nat → Type
| leaf : Tree 0
| nil (n : Nat) : Tree (n + 1)
| cons (n : Nat) (head : Tree n) (tail : Tree (n + 1)) : Tree (n + 1)
-/

/-
## Example 4: trees with countable branching and unbounded depth

coinductive Tree : Type
| leaf : Tree
| node (children : Nat → Tree)

An interesting thing is that despite unlimited branching we can still define the metric use `sup`,
because the metric is bounded.
-/

/-
## Example 5: trees with bounded branching and unbounded depth

coinductive Tree : Type
| leaf : Tree
| node (n : Nat) (children : Fin n → Tree)
-/
