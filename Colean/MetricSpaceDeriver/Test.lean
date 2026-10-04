import Colean.MetricSpaceDeriver.MetricSpace

/- 1. Lists -/

deriving instance MetricSpace for List

example : dist ([] : List Nat) [1, 2] = 1 := by
  change instDistList_metricCorec.dist _ _ = _
  simp [instDistList_metricCorec.dist]

example : dist [1, 3] [1, 2] = 2⁻¹ := by
  change instDistList_metricCorec.dist _ _ = _
  simp [instDistList_metricCorec.dist]

example : dist [1, 2] [1, 2] = 0 := by
  change instDistList_metricCorec.dist _ _ = _
  simp [instDistList_metricCorec.dist]


#check List.dist_self
#print axioms List.dist_self

#check List.dist_comm
#print axioms List.dist_comm

#check List.dist_nonneg
#print axioms List.dist_nonneg

#check List.dist_le_one
#print axioms List.dist_le_one

#check List.eq_of_dist_eq_zero
#print axioms List.eq_of_dist_eq_zero

/- 2. BinTree -/

inductive BinTree
| leaf
| node (left right : BinTree)

deriving instance MetricSpace for BinTree

example : dist BinTree.leaf (BinTree.node .leaf .leaf) = 1 := by
  change instDistBinTree.dist _ _ = _
  simp [instDistBinTree.dist]

example : dist (BinTree.node .leaf .leaf) (BinTree.node (.node .leaf .leaf) .leaf) = 1/2 := by
  change instDistBinTree.dist _ _ = _
  simp [instDistBinTree.dist]

#check BinTree.dist_self
#print axioms BinTree.dist_self

#check BinTree.dist_comm
#print axioms BinTree.dist_comm

#check BinTree.dist_nonneg
#print axioms BinTree.dist_nonneg

#check BinTree.dist_le_one
#print axioms BinTree.dist_le_one

#check BinTree.eq_of_dist_eq_zero
#print axioms BinTree.eq_of_dist_eq_zero

#check BinTree.dist_ultra
#print axioms BinTree.dist_ultra


#synth MetricSpace BinTree
#print axioms instMetricSpaceBinTree

/- Error cases. These should NOT work -/
mutual
inductive Even' | zero : Even' | succ : Odd' → Even'
inductive Odd'  | succ : Even' → Odd'
end
deriving instance MetricSpace for Even'

inductive IntVec : Nat → Type | nil : IntVec 0 | cons {n} : Int → IntVec n → IntVec (n+1)
deriving instance MetricSpace for IntVec
