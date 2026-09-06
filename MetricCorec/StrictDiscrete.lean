import Mathlib

variable  {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

def IsStrictDiscreteSet (X : Set α) : Prop :=
  ∀ x ∈ X, IsOpen {x}

theorem IsStrictDiscreteSet.isOpen {X : Set α} (h : IsStrictDiscreteSet X) : IsOpen X := by
  rw [← Set.biUnion_of_singleton X]
  exact isOpen_biUnion h

theorem IsStrictDiscreteSet.image {f : α → β} {X : Set α} (h : IsStrictDiscreteSet X)
    (hf : IsDenseInducing f) [T1Space β] :
    IsStrictDiscreteSet (f '' X) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  -- Get open V in β with f ⁻¹' V = {x} (from the inducing property)
  have hopen_x : IsOpen {x} := h x hx
  rw [hf.toIsInducing.isOpen_iff] at hopen_x
  obtain ⟨V, hV, hfV⟩ := hopen_x
  -- Show V = {f x}, so {f x} = V is open
  suffices heq : V = {f x} from heq ▸ hV
  ext z
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hzV
    by_contra hne
    -- V ∩ {f x}ᶜ is a nonempty open set; by density it meets range f
    have hopen' : IsOpen (V ∩ ({f x} : Set β)ᶜ) :=
      hV.inter isClosed_singleton.isOpen_compl
    have hnonempty : (V ∩ ({f x} : Set β)ᶜ).Nonempty := ⟨z, hzV, hne⟩
    -- density gives a point in (V ∩ {f x}ᶜ) ∩ range f
    obtain ⟨w, ⟨⟨hwV, hwne⟩, u, rfl⟩⟩ :=
      hf.dense.inter_open_nonempty _ hopen' hnonempty
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hwne
    apply hwne
    -- f u ∈ V means u ∈ f ⁻¹' V = {x}, so u = x, so f u = f x
    have hu : u ∈ f ⁻¹' V := Set.mem_preimage.mpr hwV
    rw [hfV] at hu
    exact congr_arg f (Set.mem_singleton_iff.mp hu)
  · rintro rfl
    rw [← Set.mem_preimage, hfV]
    exact Set.mem_singleton x
