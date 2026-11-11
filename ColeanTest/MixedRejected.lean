import Colean.MutualCmd

/-! # Test: the rejected forms of mixed blocks, and the failures

A plain `mutual` block may not mix `data` and `codata`; a `mixed_mutual` block of one kind is a
`mutual` block, with a warning. The other blocks here fail at the instances of an open run
(step 5): the outer run nests through the open type in its parameter for the outer types, and no
instance is generated for it when that parameter is a family (an outer run with indices, or a
block) or occurs in a field together with the type itself or another varying parameter (a
field `Tree α × Forest α`, or a run passing an outer type on to a run further inside). A failed
block declares nothing. -/

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
#check @E_F.corec

/-! ### Failures at the instances of an open run -/

-- An outer run with indices: the open forests' parameter is a family over the index.
/--
error: `VForest` cannot be nested through in this `mixed_mutual` block: no `Codata.PolyIso` instance was generated for `VForest.Open`, the open form that `VTree` nests through.
its parameter `X`, standing for `VTree`, is a family over the index of `VTree`: nesting through it needs `Codata.IPolyIso` instances, which are not generated
-/
#guard_msgs in
mixed_mutual
codata VTree (α : Type u) : Nat → Type u
  | node {n : Nat} (a : α) (children : VForest α n) : VTree α n
data VForest (α : Type u) : Nat → Type u
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
codata Tree₂ (α : Type u)
  | node (a : α) (children : Forest₂ α)
codata Str₂ (α : Type u)
  | cons (hd : Tree₂ α) (tl : Str₂ α)
data Forest₂ (α : Type u)
  | nil
  | cons (t : Tree₂ α) (s : Str₂ α) (f : Forest₂ α)
end

-- A field with an outer type and the open type itself.
/--
error: `Forest₃` cannot be nested through in this `mixed_mutual` block: no `Codata.PolyIso` instance was generated for `Forest₃.Open`, the open form that `Tree₃` nests through.
its parameter `X`, standing for `Tree₃`, cannot vary: it occurs in a field together with another parameter that varies or with the type itself, or in a field without an occurrence structure in it
-/
#guard_msgs in
mixed_mutual
codata Tree₃ (α : Type u)
  | node (a : α) (children : Forest₃ α)
data Forest₃ (α : Type u)
  | nil
  | cons (p : Tree₃ α × Forest₃ α)
end

-- A distant mention: `C'` mentions `A'`, so `B'` passes its parameter for `A'` on to `C'`, in a
-- field with the block's parameter (`c : C'.Open α X`).
/--
error: `B'` cannot be nested through in this `mixed_mutual` block: no `Codata.PolyIso` instance was generated for `B'.Open`, the open form that `A'` nests through.
its parameter `X`, standing for `A'`, cannot vary: it occurs in a field together with another parameter that varies or with the type itself, or in a field without an occurrence structure in it
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

-- Nothing of a failed block is declared, the open types of the runs inside neither.
open Lean in
run_cmd do
  for n in [`RejectedTest.VTree, `RejectedTest.VForest.Open, `RejectedTest.Forest₂.Open,
      `RejectedTest.Tree₂_Str₂.Ix, `RejectedTest.Forest₃.Open, `RejectedTest.C'.Open,
      `RejectedTest.B'.Open] do
    if (← getEnv).contains n then throwError "unexpected declaration `{n}`"

end

end RejectedTest
