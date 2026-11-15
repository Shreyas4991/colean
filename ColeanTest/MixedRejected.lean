import Colean.MutualCmd

/-! # Test: the rejected forms of mixed blocks, and the failures

A plain `mutual` block may not mix `datatype` and `codatatype`; a `mixed_mutual` block of one kind
is a `mutual` block, with a warning. The other blocks here fail at the instances of an open run
(step 5): the outer run nests through the open type in its parameter for the outer types, and no
instance is generated for it when that parameter is a family (an outer run with indices, or a
block), occurs in a field without an occurrence structure in it (a function domain), or in a
field together with the type itself without a structure in both (`Two (Tree α) (Forest α)`, the
two in two arguments of a type constructor). A failed block declares nothing. -/

universe u

namespace RejectedTest

noncomputable section

/--
error: a `mutual` block may not mix `datatype` and `codatatype` declarations: the block is a nested fixpoint and the nesting order is a choice; use `mixed_mutual … end`, which nests the declarations in the order written, the first outermost
-/
#guard_msgs in
mutual
datatype A (α : Type u)
  | nil
  | cons (b : B α) (a : A α)
codatatype B (α : Type u)
  | mk (a : A α)
end

/--
warning: all declarations of this `mixed_mutual` block are `codatatype`; use `mutual`
-/
#guard_msgs in
mixed_mutual
codatatype E (α : Type u)
  | mk (a : α) (f : F α)
codatatype F (α : Type u)
  | mk (e : E α)
end

#check @E.mk
#check @E_F.corec

/-! ### Failures at the instances of an open run -/

-- An outer run with indices: the open forests' parameter is a family over the index.
/--
error: `VForest` cannot be nested through in this `mixed_mutual` block: no `Codata.PolyIso` instance was generated for `VForest.Open`, the open form that `VTree` nests through.
its parameter `X`, standing for `VTree`, is a family over the index of `VTree`: nesting through it needs `Codata.IPolyIso` instances, which are not generated
-/
#guard_msgs in
mixed_mutual
codatatype VTree (α : Type u) : Nat → Type u
  | node {n : Nat} (a : α) (children : VForest α n) : VTree α n
datatype VForest (α : Type u) : Nat → Type u
  | nil : VForest α 0
  | cons {n : Nat} (t : VTree α n) (f : VForest α n) : VForest α (n + 1)
end

-- An outer block: the parameter is a family over the block's index.
/--
error: `Forest₂` cannot be nested through in this `mixed_mutual` block: no `Codata.PolyIso` instance was generated for `Forest₂.Open`, the open form that `Tree₂` nests through.
its parameter `X`, standing for `Tree₂`, is a family over the index of `Tree₂`: nesting through it needs `Codata.IPolyIso` instances, which are not generated
-/
#guard_msgs in
mixed_mutual
codatatype Tree₂ (α : Type u)
  | node (a : α) (children : Forest₂ α)
codatatype Str₂ (α : Type u)
  | cons (hd : Tree₂ α) (tl : Str₂ α)
datatype Forest₂ (α : Type u)
  | nil
  | cons (t : Tree₂ α) (s : Str₂ α) (f : Forest₂ α)
end

datatype Two (α β : Type u)
  | mk (a : α) (b : β)

-- An outer type in a field with the run's own type, in two arguments of a type constructor: the
-- field has no structure in both (`List (Tree α ⊕ Forest α)` has one,
-- `ColeanTest/NestGaps3.lean`).
/--
error: `Forest₃` cannot be nested through in this `mixed_mutual` block: no `Codata.PolyIso` instance was generated for `Forest₃.Open`, the open form that `Tree₃` nests through.
its parameter `X`, standing for `Tree₃`, cannot vary: it occurs in a field without an occurrence structure in it, or together with the type itself in a field without a structure in both, as in two arguments of a type constructor
-/
#guard_msgs in
mixed_mutual
codatatype Tree₃ (α : Type u)
  | node (a : α) (children : Forest₃ α)
datatype Forest₃ (α : Type u)
  | nil
  | cons (p : Two (Tree₃ α) (Forest₃ α))
end

-- An outer type in a function domain.
/--
error: `Forest₄` cannot be nested through in this `mixed_mutual` block: no `Codata.PolyIso` instance was generated for `Forest₄.Open`, the open form that `Tree₄` nests through.
its parameter `X`, standing for `Tree₄`, cannot vary: it occurs in a field without an occurrence structure in it, or together with the type itself in a field without a structure in both, as in two arguments of a type constructor
-/
#guard_msgs in
mixed_mutual
codatatype Tree₄ (α : Type u)
  | node (a : α) (children : Forest₄ α)
datatype Forest₄ (α : Type u)
  | nil
  | cons (k : Tree₄ α → Nat) (f : Forest₄ α)
end

-- Nothing of a failed block is declared, the open types of the runs inside neither.
open Lean in
run_cmd do
  for n in [`RejectedTest.VTree, `RejectedTest.VForest.Open, `RejectedTest.Forest₂.Open,
      `RejectedTest.Tree₂_Str₂.Ix, `RejectedTest.Forest₃.Open, `RejectedTest.Forest₄.Open] do
    if (← getEnv).contains n then throwError "unexpected declaration `{n}`"

end

end RejectedTest
