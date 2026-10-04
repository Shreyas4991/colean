import Colean.Subtypes.CodataCmd

/-! Colists of naturals: a constructor of arity zero and one of arity one. -/

namespace CodataTest

noncomputable section

codata CoList
  | nil
  | cons (n : Nat) (s : CoList)

example (n : Nat) : CoList.dtor (CoList.cons n CoList.nil) = .cons n CoList.nil := by simp

example (n : Nat) (s : CoList) : CoList.nil ≠ CoList.cons n s := by simp

end

end CodataTest
