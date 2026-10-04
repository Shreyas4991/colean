import Colean.MetricSpaceDeriver.Dist
import Colean.MetricSpaceDeriver.MetricSpace

/- 1. Lists-/


/- Expected:
dist : List α → List α → ℝ
| [], [] => 0
| x :: xs, y :: ys =>
  if x = y then
    2⁻¹ * dist xs ys
  else
    1
| _, _ => 1
-/
deriving instance Dist for List

example : dist ([] : List Nat) [1, 2] = 1 := by
  change instDistList_metricCorec.dist _ _ = _
  simp [instDistList_metricCorec.dist]

example : dist [1, 3] [1, 2] = 2⁻¹ := by
  change instDistList_metricCorec.dist _ _ = _
  simp [instDistList_metricCorec.dist]

example : dist [1, 2] [1, 2] = 0 := by
  change instDistList_metricCorec.dist _ _ = _
  simp [instDistList_metricCorec.dist]


/- 2. BinTree -/

inductive BinTree
| leaf
| node (left right : BinTree)

/- Expected:
dist : BinTree → BinTree → ℝ
| .leaf, .leaf => 0
| .node l1 r1, .node l2 r2 =>
  1/2 * (dist l1 l2 ⊔ dist r1 r2)
| _, _ => 1
-/
deriving instance Dist for BinTree

example : dist BinTree.leaf (BinTree.node .leaf .leaf) = 1 := by
  change instDistBinTree.dist _ _ = _
  simp [instDistBinTree.dist]

example : dist (BinTree.node .leaf .leaf) (BinTree.node (.node .leaf .leaf) .leaf) = 1/2 := by
  change instDistBinTree.dist _ _ = _
  simp [instDistBinTree.dist]


/- 3. Even/Odd -/

mutual

inductive Even'
| zero : Even'
| succ : Odd' → Even'

inductive Odd'
| succ : Even' → Odd'

end

deriving instance Dist for Even'

/- 4. Vector -/

inductive IntVector : Nat → Type
| nil : IntVector 0
| cons {n : Nat} : Int → IntVector n → IntVector (n + 1)

deriving instance Dist for IntVector

example : dist (IntVector.cons 1 (.cons 2 .nil)) (IntVector.cons 1 (.cons 3 .nil)) = 2⁻¹ := by
  change instDistIntVector.dist _ _ = _
  simp [instDistIntVector.dist]

/- 5. Strange vector -/

inductive StrangeVector : Nat → Type
| nil : StrangeVector 0
| cons {n : Nat} : Int → StrangeVector n → StrangeVector n

deriving instance Dist for StrangeVector

/- 6. Stranger vector -/

inductive StrangerVector : Nat → Type
| nil : StrangerVector 0
| nil2 : StrangerVector 0
| cons {n : Nat} : Int → StrangerVector n → StrangerVector (n + 1)

deriving instance Dist for StrangerVector

example : dist StrangerVector.nil StrangerVector.nil2 = 1 := by
  change instDistStrangerVector.dist _ _ = _
  simp [instDistStrangerVector.dist]
