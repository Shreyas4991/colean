import Mathlib

instance {α : Type} [PseudoMetricSpace α] [BoundedSpace α] : BoundedSpace (UniformSpace.Completion α) := by
  constructor
  rw [← DenseRange.closure_range (UniformSpace.Completion.denseRange_coe)]
  apply Bornology.IsBounded.closure
  rw [← Set.image_univ]
  exact UniformSpace.Completion.coe_isometry.lipschitz.isBounded_image BoundedSpace.bounded_univ
