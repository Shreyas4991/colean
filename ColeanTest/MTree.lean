import Colean.MutualCmd

/-! # Test: a mutual `codata` block, trees and forests of infinite depth and width

The block-level interface: one state family over `Tree_Forest.Ix`, one coalgebra, one relation.
The interface per type (a state, a step and a relation per type) is `ColeanTest/MutualCorec.lean`.
-/

universe u

namespace CodataTest.Mutual

noncomputable section

mutual
codata Tree (α : Type u)
  | node (a : α) (children : Forest α)
codata Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

#check @Tree_Forest.Ix
#check @Tree_Forest.F.cons
#check @Tree.node
#check @Forest.cons
#check @Tree_Forest.dtor
#check @Tree.corec
#check @Tree_Forest.bisim
#check @Tree.casesOn
#check @Forest.casesOn
#check @Forest.cons_ne_nil

/-- One coalgebra for the block: every node is labelled `a` and has one child. -/
def fullCoalg {α : Type u} (a : α) : ∀ m, Unit → Tree_Forest.F α (fun _ => Unit) m
  | .Tree, _ => .node a ()
  | .Forest, _ => .cons () ()

def Tree.full {α : Type u} (a : α) : Tree α := Tree_Forest.corec (fullCoalg a) (m := .Tree) ()
def Forest.full {α : Type u} (a : α) : Forest α :=
  Tree_Forest.corec (fullCoalg a) (m := .Forest) ()

/-- The block's `dtor` (`(Tree.full a).dtor` is `Tree.dtor`, into the layer per type). -/
@[simp] theorem Tree.dtor_full {α : Type u} (a : α) :
    Tree_Forest.dtor (Tree.full a) = .node a (Forest.full a) := by
  simp [Tree.full, Forest.full, Tree_Forest.dtor_corec, fullCoalg]

@[simp] theorem Forest.dtor_full {α : Type u} (a : α) :
    Tree_Forest.dtor (Forest.full a) = .cons (Tree.full a) (Forest.full a) := by
  simp [Tree.full, Forest.full, Tree_Forest.dtor_corec, fullCoalg]

/-- The unfolding equations, through `ctor_dtor`. -/
theorem Tree.full_eq {α : Type u} (a : α) : Tree.full a = Tree.node a (Forest.full a) := by
  conv => lhs; rw [← Tree_Forest.ctor_dtor (Tree.full a), Tree.dtor_full]
  rfl

theorem Forest.full_eq {α : Type u} (a : α) :
    Forest.full a = Forest.cons (Tree.full a) (Forest.full a) := by
  conv => lhs; rw [← Tree_Forest.ctor_dtor (Forest.full a), Forest.dtor_full]
  rfl

/-- Case analysis per type: a forest is empty or a cons. -/
example {α : Type u} (f : Forest α) : f = .nil ∨ ∃ t f', f = .cons t f' := by
  cases f with
  | nil => exact Or.inl rfl
  | cons t f' => exact Or.inr ⟨t, f', rfl⟩

/-- A coalgebra with a counter that is never looked at. -/
def natCoalg {α : Type u} (a : α) : ∀ m, Nat → Tree_Forest.F α (fun _ => Nat) m
  | .Tree, k => .node a (k + 1)
  | .Forest, k => .cons (k + 1) (k + 1)

/-- Bisimulation over the block: both coalgebras give the same trees and forests. -/
example {α : Type u} (a : α) (n : Nat) :
    Tree.full a = Tree_Forest.corec (natCoalg a) (m := .Tree) n := by
  refine Tree_Forest.bisim (fun _ x y => x = Tree_Forest.corec (fullCoalg a) () ∧
    ∃ k, y = Tree_Forest.corec (natCoalg a) k) ?_ ⟨rfl, n, rfl⟩
  rintro m _ _ ⟨rfl, k, rfl⟩
  cases m
  · simp only [Tree_Forest.dtor_corec, fullCoalg, natCoalg, Tree_Forest.F.map_node]
    exact .node _ _ _ ⟨rfl, _, rfl⟩
  · simp only [Tree_Forest.dtor_corec, fullCoalg, natCoalg, Tree_Forest.F.map_cons]
    exact .cons _ _ _ _ ⟨rfl, _, rfl⟩ ⟨rfl, _, rfl⟩

end

end CodataTest.Mutual
