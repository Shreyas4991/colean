import Colean.CodataCmd

/-! Trees of naturals with leaves: a constructor of arity two. -/

namespace CodataTest

noncomputable section

codata Tree
  | leaf
  | node (a : Nat) (l r : Tree)

/-- The full binary tree. -/
def Tree.full (a : Nat) : Tree := Tree.corec (fun _ => .node a () ()) ()

example (a : Nat) : Tree.dtor (Tree.full a) = .node a (Tree.full a) (Tree.full a) :=
  Tree.dtor_corec _ _

example (a : Nat) : Tree.full a = Tree.node a (Tree.full a) (Tree.full a) := Tree.corec_eq _ _

example (a b : Nat) (l r l' r' : Tree) :
    Tree.node a l r = Tree.node b l' r' ↔ a = b ∧ l = l' ∧ r = r' := by simp

end

end CodataTest
