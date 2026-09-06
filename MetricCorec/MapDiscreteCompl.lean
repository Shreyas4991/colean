import Mathlib
import MetricCorec.StrictDiscrete


/- Natural language proof:
Set β := completion of α
and g : β → β := UniformSpace.Completion.map f
and B' := image of B in β (UniformSpace.Completion.coe' '' B)
Proof by contradiction. Suppose g(x) = y with y ∈ B'. We will show that x ∈ B'.
1. Take a sequence of points x_n ∈ α that tends to x.
2. Then f(x_n) tends to g(x) = y.
3. B is strict discrete so f(x_n) must stabilize at some point.
4. f is injective, thus x_n must stabilize at some value z and y = f(z).
5. f⁻¹(B) ⊆ B so z ∈ B.
6. x = z so x ∈ B'.
-/



-- theorem map_discrete_compl_subset {α : Type} [MetricSpace α] {B : Set α}
--     (hB : IsStrictDiscreteSet B) (f : α → α)
--     (hf_cont : UniformContinuous f) (hf_inj : Function.Injective f) (hfB : f ⁻¹' B ⊆ B) :
--     UniformSpace.Completion.map f '' (UniformSpace.Completion.coe' '' B)ᶜ ⊆
--       (UniformSpace.Completion.coe' '' B)ᶜ := by
--   intro x hx
--   induction x using UniformSpace.Completion.induction_on with
--   | hp =>
--     apply isClosed_imp
--     ·
--   | ih x =>
--     sorry

theorem map_discrete_compl_subset {α : Type} [MetricSpace α] {B : Set α}
    (hB : IsStrictDiscreteSet B) (f : α → α)
    (hf_cont : UniformContinuous f) (hf_inj : Function.Injective f) (hfB : f ⁻¹' B ⊆ B) :
    UniformSpace.Completion.map f '' (UniformSpace.Completion.coe' '' B)ᶜ ⊆
      (UniformSpace.Completion.coe' '' B)ᶜ := by
  rw [Set.image_subset_iff, Set.preimage_compl, Set.compl_subset_compl]
  -- Goal: (Completion.map f) ⁻¹' (coe' '' B) ⊆ coe' '' B
  have hB' : IsStrictDiscreteSet (UniformSpace.Completion.coe' '' B) :=
    hB.image UniformSpace.Completion.isDenseInducing_coe
  -- Use Dense directly (DenseRange is a def, not abbrev)
  have hdense : Dense (Set.range (UniformSpace.Completion.coe' (α := α))) :=
    UniformSpace.Completion.denseRange_coe
  intro x hx
  obtain ⟨b, hb, hfx⟩ := hx
  -- hfx : coe' b = map f x  (image membership has this direction)
  have hb_open : IsOpen ({UniformSpace.Completion.coe' b} : Set (UniformSpace.Completion α)) :=
    hB' _ ⟨b, hb, rfl⟩
  have hT_open : IsOpen ((UniformSpace.Completion.map f) ⁻¹'
      {UniformSpace.Completion.coe' b}) :=
    hb_open.preimage UniformSpace.Completion.continuous_map
  have hx_T : x ∈ (UniformSpace.Completion.map f) ⁻¹' {UniformSpace.Completion.coe' b} :=
    Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hfx.symm)
  -- By density, get a : α with coe' a ∈ T
  obtain ⟨_, ⟨a, rfl⟩, ha_T⟩ := hdense.exists_mem_open hT_open ⟨x, hx_T⟩
  -- f a = b
  have hfa : f a = b := by
    have h := Set.mem_singleton_iff.mp (Set.mem_preimage.mp ha_T)
    rw [UniformSpace.Completion.map_coe hf_cont] at h
    exact UniformSpace.Completion.coe_injective α h
  have ha_B : a ∈ B := hfB (Set.mem_preimage.mpr (hfa ▸ hb))
  -- T \ {coe' a} is open, disjoint from range coe', hence empty
  have hDiff_empty : (UniformSpace.Completion.map f ⁻¹'
      {UniformSpace.Completion.coe' b} \ {UniformSpace.Completion.coe' a}) = ∅ := by
    by_contra hne
    obtain ⟨_, ⟨a', rfl⟩, hw_diff⟩ := hdense.exists_mem_open
        (hT_open.sdiff isClosed_singleton) (Set.nonempty_iff_ne_empty.mpr hne)
    simp only [Set.mem_diff, Set.mem_preimage, Set.mem_singleton_iff] at hw_diff
    obtain ⟨ha'_T, ha'_ne⟩ := hw_diff
    have h := Set.mem_singleton_iff.mp (Set.mem_preimage.mp ha'_T)
    rw [UniformSpace.Completion.map_coe hf_cont] at h
    exact ha'_ne (congr_arg _ (hf_inj (UniformSpace.Completion.coe_injective α h |>.trans hfa.symm)))
  -- x = coe' a ∈ coe' '' B
  exact ⟨a, ha_B, (Set.mem_singleton_iff.mp (Set.diff_eq_empty.mp hDiff_empty hx_T)).symm⟩


open UniformSpace


-- theorem extension_notMem_of_discrete {α : Type} [MetricSpace α] (B : Set α) (f : α → Completion α)
--     (hB : IsStrictDiscreteSet B)
--     (hf : ∀ a ∉ B, f a ∉ Completion.coe' '' B) (hf_cont : UniformContinuous f)
--     (c : Completion α) (hc : c ∉ Completion.coe' '' B) :
--     c.extension f ∉ Completion.coe' '' B := by
--   intro ⟨y, hy_mem, hcy⟩
--   suffices Completion.extension f ⁻¹' {Completion.coe' y} \ Completion.coe' '' B = ∅ by
--     suffices c ∈ Completion.extension f ⁻¹' {Completion.coe' y} \ Completion.coe' '' B by grind
--     simp [← hcy]
--     grind
--   by_contra!
--   have := Dense.inter_open_nonempty (UniformSpace.Completion.denseRange_coe (α := α))
--     (Completion.extension f ⁻¹' {↑y} \ Completion.coe' '' B) ?_ this
--   · obtain ⟨_, ⟨ha1, ha2⟩, ⟨a, rfl⟩⟩ := this
--     simp [Completion.extension_coe hf_cont] at ha1 ha2
--     grind
--   apply IsOpen.sdiff
--   · apply IsOpen.preimage (by fun_prop)
--     sorry
--   · sorry

-- theorem extension_notMem_of_discrete_topology {α β : Type} [MetricSpace α] [DiscreteTopology α]
--     [MetricSpace β] [CompleteSpace β]
--     {B : Set α} {f : α → β}
--     (hf : ∀ a ∉ B, f a ∉ Completion.coe' '' B) (hf_cont : UniformContinuous f)
--     (hf_inj : Function.Injective f)
--     {c : Completion α} (hc : c ∉ Completion.coe' '' B) :
--     c.extension f ∉ Completion.coe' '' B := by

theorem singleton_coe_open_of_discrete_topology {α : Type} [MetricSpace α] [DiscreteTopology α]
    (a : α) : IsOpen {Completion.coe' a} := by
  have h : IsStrictDiscreteSet ({a} : Set α) := fun b _ => isOpen_discrete {b}
  have h2 := h.image Completion.isDenseInducing_coe
  rw [Set.image_singleton] at h2
  exact h2 _ rfl

theorem extension_notMem_of_discrete_topology {α : Type} [MetricSpace α] [DiscreteTopology α]
    {B : Set α} {f : α → Completion α}
    (hf : ∀ a ∉ B, f a ∉ Completion.coe' '' B) (hf_cont : UniformContinuous f)
    (hf_inj : Function.Injective f)
    {c : Completion α} (hc : c ∉ Completion.coe' '' B) :
    c.extension f ∉ Completion.coe' '' B := by
  have hB : IsStrictDiscreteSet B := fun b _ => isOpen_discrete {b}
  have hB' : IsStrictDiscreteSet (Completion.coe' '' B) :=
    hB.image Completion.isDenseInducing_coe
  have hdense : Dense (Set.range (Completion.coe' (α := α))) := Completion.denseRange_coe
  intro ⟨b, hb, hcb⟩
  have hb_open : IsOpen ({Completion.coe' b} : Set (Completion α)) := hB' _ ⟨b, hb, rfl⟩
  have hT_open : IsOpen ((Completion.extension f) ⁻¹' {Completion.coe' b}) :=
    hb_open.preimage Completion.continuous_extension
  have hc_T : c ∈ (Completion.extension f) ⁻¹' {Completion.coe' b} :=
    Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hcb.symm)
  obtain ⟨_, ⟨a, rfl⟩, ha_T⟩ := hdense.exists_mem_open hT_open ⟨c, hc_T⟩
  have hfa : f a = Completion.coe' b := by
    have h := Set.mem_singleton_iff.mp (Set.mem_preimage.mp ha_T)
    rwa [Completion.extension_coe hf_cont] at h
  have ha_B : a ∈ B := by
    by_contra ha_notB; exact hf a ha_notB ⟨b, hb, hfa.symm⟩
  have hDiff_empty : (Completion.extension f ⁻¹' {Completion.coe' b} \
      {Completion.coe' a}) = ∅ := by
    by_contra hne
    obtain ⟨_, ⟨a', rfl⟩, hw_diff⟩ := hdense.exists_mem_open
        (hT_open.sdiff isClosed_singleton) (Set.nonempty_iff_ne_empty.mpr hne)
    simp only [Set.mem_diff, Set.mem_preimage, Set.mem_singleton_iff] at hw_diff
    obtain ⟨ha'_T, ha'_ne⟩ := hw_diff
    rw [Completion.extension_coe hf_cont] at ha'_T
    exact ha'_ne (congr_arg Completion.coe' (hf_inj (ha'_T.trans hfa.symm)))
  have hc_eq : c = Completion.coe' a :=
    Set.mem_singleton_iff.mp ((Set.diff_eq_empty.mp hDiff_empty) hc_T)
  exact hc ⟨a, ha_B, hc_eq.symm⟩

/-- Generalization of `extension_notMem_of_discrete_topology` to an arbitrary complete
    metric space `β`. The role of `Completion.coe' '' B` in the original is split:
    `S` is the target set (now arbitrary, requiring `IsStrictDiscreteSet S` explicitly),
    while `B` still mediates the source condition via `hc : c ∉ Completion.coe' '' B`. -/
theorem extension_notMem_gen {α : Type} [MetricSpace α]
    {β : Type} [UniformSpace β] [CompleteSpace β] [T1Space β]
    {B : Set α} {S : Set β} {f : α → β}
    (hS : IsStrictDiscreteSet S)
    (hf : ∀ a ∉ B, f a ∉ S) (hf_cont : UniformContinuous f)
    (hf_inj : Function.Injective f)
    {c : Completion α} (hc : c ∉ Completion.coe' '' B) :
    Completion.extension f c ∉ S := by
  have hdense : Dense (Set.range (Completion.coe' (α := α))) := Completion.denseRange_coe
  intro hcs
  have hopen : IsOpen ({Completion.extension f c} : Set β) := hS _ hcs
  have hT_open : IsOpen ((Completion.extension f) ⁻¹' {Completion.extension f c}) :=
    hopen.preimage Completion.continuous_extension
  have hc_T : c ∈ (Completion.extension f) ⁻¹' {Completion.extension f c} :=
    Set.mem_preimage.mpr rfl
  obtain ⟨_, ⟨a, rfl⟩, ha_T⟩ := hdense.exists_mem_open hT_open ⟨c, hc_T⟩
  have hfa : f a = Completion.extension f c := by
    have h := Set.mem_singleton_iff.mp (Set.mem_preimage.mp ha_T)
    rwa [Completion.extension_coe hf_cont] at h
  have ha_B : a ∈ B := by
    by_contra ha_notB; exact hf a ha_notB (hfa ▸ hcs)
  have hDiff_empty : (Completion.extension f ⁻¹' {Completion.extension f c} \
      {Completion.coe' a}) = ∅ := by
    by_contra hne
    obtain ⟨_, ⟨a', rfl⟩, hw_diff⟩ := hdense.exists_mem_open
        (hT_open.sdiff isClosed_singleton) (Set.nonempty_iff_ne_empty.mpr hne)
    simp only [Set.mem_diff, Set.mem_preimage, Set.mem_singleton_iff] at hw_diff
    obtain ⟨ha'_T, ha'_ne⟩ := hw_diff
    rw [Completion.extension_coe hf_cont] at ha'_T
    exact ha'_ne (congr_arg Completion.coe' (hf_inj (ha'_T.trans hfa.symm)))
  have hc_eq : c = Completion.coe' a :=
    Set.mem_singleton_iff.mp ((Set.diff_eq_empty.mp hDiff_empty) hc_T)
  exact hc ⟨a, ha_B, hc_eq.symm⟩

-- theorem extension_uniform_continuous {α β : Type*} [UniformSpace α] [UniformSpace β] :
--     UniformContinuous (Completion.extension (α := α) (β := β)) := by
--   sorry -- don't prove for now

theorem eval_uniform_continuous {α β : Type*} [UniformSpace α] [UniformSpace β]
    (a : α) :
    UniformContinuous (fun (f : α → β) => f a) := by
  exact Pi.uniformContinuous_proj _ a
