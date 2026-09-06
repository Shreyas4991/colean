import Mathlib

lemma half_sup_le_sup_halves (x y z : ℝ) :
    2⁻¹ * x ≤ (2⁻¹ * y) ⊔ (2⁻¹ * z) ↔ x ≤ y ⊔ z := by
  simp

lemma half_pow_le_one {n : ℕ} : (2 : ℝ)⁻¹ ^ n ≤ 1 := by bound

lemma half_pow_le_one' {n : ℕ} {r : ℝ} (hr : r = 1) : (2 : ℝ)⁻¹ ^ n ≤ r := by bound

lemma half_pos' : (0 : ℝ) < 2⁻¹ := by norm_num

lemma half_pow_sup_eq (n m : ℕ) : (2 : ℝ)⁻¹ ^ (n ⊔ m) = 2⁻¹ ^ n ⊓ 2⁻¹ ^ m := by
  apply Antitone.map_sup
  apply pow_right_anti₀ (by norm_num) (by norm_num)

lemma half_mul_le {x : ℝ} (h : 0 ≤ x) : 2⁻¹ * x ≤ x := by
  linarith

theorem DiscreteTopology.of_all_isolated {α : Type} [PseudoMetricSpace α]
    (h : ∀ a : α, ∃ ε > 0, ∀ b, Dist.dist a b < ε → a = b) :
    DiscreteTopology α := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro a
  simp [Metric.isOpen_iff]
  specialize h a
  grind [PseudoMetricSpace.dist_comm]

theorem Dense.inter_open_infinite {X : Type*} [TopologicalSpace X] [T1Space X] {s t : Set X}
    (hs : Dense s) (ht : IsOpen t) (h_diff : (t \ s).Nonempty) :
    (s ∩ t).Infinite := by
  intro h
  obtain ⟨y, hys, hyt, hyts⟩ := hs.exists_mem_open (ht.sdiff h.isClosed) (by simpa)
  exact hyts ⟨hys, hyt⟩

theorem IsometryEquiv.uniformContinuous {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X ≃ᵢ Y) : UniformContinuous f := f.isometry.uniformContinuous

theorem isComplete_singleton {X : Type*} [UniformSpace X] {x : X} : IsComplete {x} :=
  isCompact_singleton.isComplete

-- theorem CompleteSpace.of_bijective_isometry {X Y : Type*} {f : X → Y} [CompleteSpace Y]
--     (hf : Function.Bijective f) (hf_iso : Isometry f)

-- theorem CompleteSpace_of_comp_dense {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
--     [CompleteSpace Z]
--     {f : X → Y} {g : Y → Z} (hf_dense : DenseRange f) (hf_iso : Isometry f)
--     (hgf_dense : DenseRange (g ∘ f)) (hg_iso : Isometry g) :
--     CompleteSpace Y := by
--   sorry


open UniformSpace

theorem uniformContinuous₂_dist {α : Type*} [PseudoMetricSpace α] :
    UniformContinuous₂ (@dist α _) :=
  uniformContinuous_dist

theorem AntilipschitzWith.completion_map {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {f : α → β} {K : NNReal}
    (h : AntilipschitzWith K f) (huc : UniformContinuous f) :
    AntilipschitzWith K (Completion.map f) := by
  have hmap : Continuous (Completion.map f) := Completion.continuous_map
  rw [antilipschitzWith_iff_le_mul_dist]
  intro x y
  refine Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_le continuous_dist
      (continuous_const.mul
        (continuous_dist.comp ((hmap.comp continuous_fst).prodMk (hmap.comp continuous_snd))))
  · intro a b
    simp only [Completion.map_coe huc, Completion.dist_eq]
    exact antilipschitzWith_iff_le_mul_dist.mp h a b

theorem completion_dist_ge {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {f : α → β} {b : β}
    (hf : UniformContinuous f) {C : ℝ} (h : ∀ a, C ≤ dist (f a) b)
    (a : Completion α) :
    C ≤ dist (Completion.map f a) (Completion.coe' b) := by
  have hclosed : IsClosed {a : Completion α | C ≤ dist (Completion.map f a) (↑b : Completion β)} := by
    apply isClosed_le continuous_const
    exact Continuous.dist Completion.continuous_map continuous_const
  exact Completion.induction_on a hclosed (fun x => by
    rw [Completion.map_coe hf, Completion.dist_eq]; exact h x)

theorem coe_notMem_completion_range {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {f : α → β} {b : β}
    (hf : UniformContinuous f) (h : ∀ a, 1 ≤ dist (f a) b) :
    Completion.coe' b ∉ Set.range (Completion.map f) := by
  simp
  have := completion_dist_ge hf h
  peel this with x a
  intro heq
  rw [heq, dist_self] at a
  linarith

theorem completion_dist_ge' {α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [PseudoMetricSpace γ]
    {f : α → γ} {g : β → γ}
    (hf : UniformContinuous f) (hg : UniformContinuous g)
    {C : ℝ} (h : ∀ a b, C ≤ dist (f a) (g b)) (a : Completion α) (b : Completion β) :
    C ≤ dist (Completion.map f a) (Completion.map g b) := by
  have hclosed : IsClosed {p : Completion α × Completion β |
      C ≤ dist (Completion.map f p.1) (Completion.map g p.2)} :=
    isClosed_le continuous_const
      (Continuous.dist (Completion.continuous_map.comp continuous_fst)
        (Completion.continuous_map.comp continuous_snd))
  exact Completion.induction_on₂ a b hclosed (fun x y => by
    rw [Completion.map_coe hf, Completion.map_coe hg, Completion.dist_eq]; exact h x y)

noncomputable def PseudoMetricSpace.pullProdCompletion {α β : Type} [PseudoMetricSpace α] [PseudoMetricSpace β] :
    IsometryEquiv (Completion α × Completion β) (Completion (α × β)) where
  toFun :=
    Function.uncurry (Completion.extension₂ (fun a b => (↑(a, b) : Completion (α × β))))
  invFun x :=
    (Completion.map Prod.fst x, Completion.map Prod.snd x)
  left_inv := by
    have huc₂ : UniformContinuous₂ (fun (a : α) (b : β) => (↑(a, b) : Completion (α × β))) :=
      (uniformContinuous₂_curry _).mpr (Completion.uniformContinuous_coe (α × β))
    have hc_fwd : Continuous (Function.uncurry (Completion.extension₂
        (fun (a : α) (b : β) => (↑(a, b) : Completion (α × β))))) :=
      (Completion.uniformContinuous_extension₂ _).continuous
    intro ⟨a, b⟩
    refine Completion.induction_on₂ a b ?_ ?_
    · exact isClosed_eq
        ((Completion.continuous_map.comp hc_fwd).prodMk
          (Completion.continuous_map.comp hc_fwd))
        continuous_id
    · intro x y
      simp only [Function.uncurry, Completion.extension₂_coe_coe huc₂,
        Completion.map_coe uniformContinuous_fst, Completion.map_coe uniformContinuous_snd]
  right_inv := by
    have huc₂ : UniformContinuous₂ (fun (a : α) (b : β) => (↑(a, b) : Completion (α × β))) :=
      (uniformContinuous₂_curry _).mpr (Completion.uniformContinuous_coe (α × β))
    have hc_fwd : Continuous (Function.uncurry (Completion.extension₂
        (fun (a : α) (b : β) => (↑(a, b) : Completion (α × β))))) :=
      (Completion.uniformContinuous_extension₂ _).continuous
    intro x
    refine Completion.induction_on x ?_ ?_
    · exact isClosed_eq
        (hc_fwd.comp (Completion.continuous_map.prodMk Completion.continuous_map))
        continuous_id
    · intro ⟨a, b⟩
      simp only [Function.uncurry, Completion.map_coe uniformContinuous_fst,
        Completion.map_coe uniformContinuous_snd, Completion.extension₂_coe_coe huc₂]
  isometry_toFun := by
    have huc₂ : UniformContinuous₂ (fun (a : α) (b : β) => (↑(a, b) : Completion (α × β))) :=
      (uniformContinuous₂_curry _).mpr (Completion.uniformContinuous_coe (α × β))
    apply Isometry.of_dist_eq
    intro p₁ p₂
    refine Completion.denseRange_coe₂.induction_on₂ ?_ ?_ p₁ p₂
    · have hc : Continuous (Function.uncurry (Completion.extension₂
          (fun (a : α) (b : β) => (↑(a, b) : Completion (α × β))))) :=
        (Completion.uniformContinuous_extension₂ _).continuous
      exact isClosed_eq
        (continuous_dist.comp ((hc.comp continuous_fst).prodMk (hc.comp continuous_snd)))
        (continuous_dist.comp (continuous_fst.prodMk continuous_snd))
    · intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
      simp only [Function.uncurry, Completion.extension₂_coe_coe huc₂,
        Prod.dist_eq, Completion.dist_eq]

@[simp]
theorem PseudoMetricSpace.pullProdCompletion_coe_eq {α β : Type} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (a : α) (b : β) :
    pullProdCompletion (Completion.coe' a, Completion.coe' b) = Completion.coe' (a, b) := by
  simp only [pullProdCompletion, IsometryEquiv.coe_mk, Equiv.coe_fn_mk, Function.uncurry]
  exact Completion.extension₂_coe_coe
    ((uniformContinuous₂_curry _).mpr (Completion.uniformContinuous_coe (α × β))) a b

@[simp]
theorem PseudoMetricSpace.pullProdCompletion_symm_coe_eq {α β : Type} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (ab : α × β) :
    pullProdCompletion.symm (Completion.coe' ab) = (Completion.coe' ab.1, Completion.coe' ab.2) := by
  apply_fun pullProdCompletion
  simp

noncomputable def PseudoMetricSpace.completeEquivSelf {α : Type} [PseudoMetricSpace α]
    [CompleteSpace α] [T0Space α] :
    IsometryEquiv (Completion α) α where
  toFun := Completion.extension id
  invFun := (↑·)
  left_inv := by
    intro x
    refine Completion.induction_on x ?_ ?_
    · exact isClosed_eq ((Completion.continuous_coe α).comp Completion.continuous_extension)
        continuous_id
    · intro a
      simp [Completion.extension_coe (uniformContinuous_id)]
  right_inv := by
    intro a
    simp [Completion.extension_coe (uniformContinuous_id)]
  isometry_toFun := isometry_id.completion_extension

@[simp]
theorem PseudoMetricSpace.completeEquivSelf_apply_coe {α : Type} [PseudoMetricSpace α]
    [CompleteSpace α] [T0Space α] (a : α) :
    PseudoMetricSpace.completeEquivSelf (Completion.coe' a) = a := by
  exact Completion.extension_coe uniformContinuous_id a

@[simp]
theorem PseudoMetricSpace.completeEquivSelf_symm_apply {α : Type} [PseudoMetricSpace α]
    [CompleteSpace α] [T0Space α] (a : α) :
    PseudoMetricSpace.completeEquivSelf.symm a = Completion.coe' a := rfl

def IsometryEquiv.prodCongr {α α' β β' : Type} [PseudoMetricSpace α]
    [PseudoMetricSpace α'] [PseudoMetricSpace β] [PseudoMetricSpace β']
    (iα : α ≃ᵢ α') (iβ : β ≃ᵢ β') : (α × β) ≃ᵢ (α' × β') where
  toEquiv := iα.toEquiv.prodCongr iβ.toEquiv
  isometry_toFun := iα.isometry.prodMap iβ.isometry

@[simp]
theorem IsometryEquiv.prodCongr_apply {α α' β β' : Type} [PseudoMetricSpace α]
    [PseudoMetricSpace α'] [PseudoMetricSpace β] [PseudoMetricSpace β']
    (iα : α ≃ᵢ α') (iβ : β ≃ᵢ β') (ab : α × β) :
    prodCongr iα iβ ab = (iα ab.1, iβ ab.2) :=
  rfl

@[simp]
theorem IsometryEquiv.prodCongr_symm_apply {α α' β β' : Type} [PseudoMetricSpace α]
    [PseudoMetricSpace α'] [PseudoMetricSpace β] [PseudoMetricSpace β']
    (iα : α ≃ᵢ α') (iβ : β ≃ᵢ β') (ab : α' × β') :
    (prodCongr iα iβ).symm ab = (iα.symm ab.1, iβ.symm ab.2) :=
  rfl

def IsometryEquiv.prodCongrLeft {α α' β : Type} [PseudoMetricSpace α]
    [PseudoMetricSpace α'] [PseudoMetricSpace β]
    (iα : α ≃ᵢ α') : (α × β) ≃ᵢ (α' × β) :=
  iα.prodCongr (IsometryEquiv.refl β)

@[simp]
theorem IsometryEquiv.prodCongrLeft_apply {α α' β : Type} [PseudoMetricSpace α]
    [PseudoMetricSpace α'] [PseudoMetricSpace β]
    (iα : α ≃ᵢ α') (ab : α × β) :
    prodCongrLeft iα ab = (iα ab.1, ab.2) :=
  rfl

@[simp]
theorem IsometryEquiv.prodCongrLeft_symm_apply {α α' β : Type} [PseudoMetricSpace α]
    [PseudoMetricSpace α'] [PseudoMetricSpace β]
    (iα : α ≃ᵢ α') (ab : α' × β) :
    (prodCongrLeft iα).symm ab = (iα.symm ab.1, ab.2) :=
  rfl

def IsometryEquiv.prodCongrRight {α β β' : Type} [PseudoMetricSpace α]
    [PseudoMetricSpace β] [PseudoMetricSpace β']
    (iβ : β ≃ᵢ β') : (α × β) ≃ᵢ (α × β') :=
  (IsometryEquiv.refl α).prodCongr iβ

@[simp]
theorem IsometryEquiv.prodCongrRight_apply {α β β' : Type} [PseudoMetricSpace α]
    [PseudoMetricSpace β] [PseudoMetricSpace β']
    (iβ : β ≃ᵢ β') (ab : α × β) :
    prodCongrRight iβ ab = (ab.1, iβ ab.2) :=
  rfl

@[simp]
theorem IsometryEquiv.prodCongrRight_symm_apply {α β β' : Type} [PseudoMetricSpace α]
    [PseudoMetricSpace β] [PseudoMetricSpace β']
    (iβ : β ≃ᵢ β') (ab : α × β') :
    (prodCongrRight iβ).symm ab = (ab.1, iβ.symm ab.2) :=
  rfl

open Classical in
noncomputable def discreteMetricSpace {α : Type} : MetricSpace α where
  dist x y := if x = y then 0 else 1
  dist_self x := by simp
  dist_comm x y := by simp [eq_comm]
  dist_triangle x y z := by
    split_ifs <;> simp_all
  eq_of_dist_eq_zero := by
    intro x y h
    simp at h
    exact h

open Classical in
theorem discreteMetricSpace_dist_eq {α : Type} (x y : α) :
    have : MetricSpace α := discreteMetricSpace
    dist x y = (if x = y then 0 else 1) := rfl

theorem discreteMetricSpace_discrete {α : Type} :
    have : MetricSpace α := discreteMetricSpace
    DiscreteUniformity α := by
  intro this
  rw [discreteUniformity_iff_eq_bot, UniformSpace.uniformSpace_eq_bot]
  rw [Metric.mem_uniformity_dist]
  exact ⟨1, by norm_num, fun {x y} h => by
    simp only [discreteMetricSpace_dist_eq] at h
    split_ifs at h with heq
    · exact heq ▸ rfl
    · norm_num at h⟩


-- theorem discreteMetricSpace_discrete {α : Type} :
--     have : MetricSpace α := discreteMetricSpace
--     DiscreteTopology α := by
--   intro this
--   apply DiscreteTopology.of_forall_le_dist Real.zero_lt_one
--   intro x y h
--   simp [discreteMetricSpace_dist_eq, h]

-- theorem discreteMetricSpace_complete {α : Type} :
--     have : MetricSpace α := discreteMetricSpace
--     CompleteSpace α := by exact?
