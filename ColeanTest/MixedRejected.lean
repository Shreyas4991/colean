import Colean.MutualCmd

/-! # Test: the rejected forms of mixed blocks -/

universe u

namespace RejectedTest

noncomputable section

/--
error: a `mutual` block may not mix `data` and `codata` declarations: the block is a nested fixpoint and the nesting order is a choice; use `mixed_mutual … end`, which nests the declarations in the order written, the first outermost
-/
#guard_msgs in
mutual
data A (α : Type u)
  | nil
  | cons (b : B α) (a : A α)
codata B (α : Type u)
  | mk (a : A α)
end

/--
error: in a `mixed_mutual` block, a declaration may mention, among the runs outside its own, only the adjacent one (`C'` mentions `A'`, two or more runs outside): a reference to a run further outside needs an occurrence structure in several parameters, which is not supported yet
-/
#guard_msgs in
mixed_mutual
codata A' (α : Type u)
  | mk (b : B' α)
data B' (α : Type u)
  | nil
  | cons (c : C' α) (b : B' α)
codata C' (α : Type u)
  | mk (a : A' α) (c : C' α)
end

/--
warning: all declarations of this `mixed_mutual` block are `codata`; use `mutual`
-/
#guard_msgs in
mixed_mutual
codata E (α : Type u)
  | mk (a : α) (f : F α)
codata F (α : Type u)
  | mk (e : E α)
end

#check @E.mk

end

end RejectedTest
