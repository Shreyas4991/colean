import Colean.MutualCmd

/-! # Test: types named like generated declarations

Inside the namespace of `T`, a generated `T.T` would shadow the type. -/

universe u

namespace NamesTest

codata B (α : Type u)
  | cons (a : α) (tail : B α)

#check @B.cons
#check @B.corec
#check @B.B'.cons_tail

data F
  | leaf
  | node (l r : F)

#check @F.node
#check @F.rec
#check @F.F'.map

codata Shape : Nat → Type
  | mk {n : Nat} (s : Shape (n + 1)) : Shape n

#check @Shape.mk
#check @Shape.bisim

end NamesTest
