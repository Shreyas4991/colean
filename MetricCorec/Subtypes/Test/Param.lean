import MetricCorec.Subtypes.DataCmd

/-! # Test: declared types as containers in their parameter

A `data` or `codata` whose last parameter is a type `α` used only at parameter positions (as the
type of a field, under a function type, or in a container) is a container in `α`: the command
declares the erased shapes `T.Shape₀`, the parameter positions `T.P`, the shapes `T.Sh` (the
erased trees) and positions `T.Pos` of the container, and the instance
`Container (fun α => T params α idx) T.Sh T.Pos`. Nested occurrences may then go through declared
types, which covers the mixed inductive/coinductive blocks. -/

universe u

namespace ParamTest

noncomputable section

-- Finite lists as a container: the erased shapes are the lengths.
data Forest (X : Type u)
  | nil
  | cons (t : X) (f : Forest X)

#check @Forest.Shape₀.cons
#check @Forest.P.cons_t
#check @Forest.shapeEquiv
#check @Forest.Sh
#check @Forest.Pos
#synth Codata.Container Forest _ _

/-- The sum of a forest of numbers, by the fold. -/
def Forest.sum (f : Forest Nat) : Nat :=
  Forest.fold (S := Nat) (fun | .nil => 0 | .cons t f => t + f) f

-- An inductive type nesting through a declared inductive type: the induction hypothesis holds
-- at the positions of the forest.
data Rose (α : Type u)
  | node (a : α) (children : Forest (Rose α))

#check @Rose.rec
#synth Codata.Container Rose _ _

def Rose.size {α : Type u} (t : Rose α) : Nat :=
  Rose.fold (S := Nat) (fun | .node _ cs => cs.sum + 1) t

theorem Rose.size_node {α : Type u} (a : α) (cs : Forest (Rose α)) :
    (Rose.node a cs).size = Forest.sum (Codata.Container.map (G' := Forest) Rose.size cs) + 1 := by
  rw [Rose.size, Rose.fold_node]
  rfl

theorem Rose.size_pos {α : Type u} (t : Rose α) : 0 < t.size := by
  cases t with
  | node a cs => rw [Rose.size_node]; exact Nat.succ_pos _

-- A coinductive type nesting through a declared inductive type: finitely branching trees of
-- infinite depth, the branching given by `Forest`. This is the mixed block `Tree`/`Forest`.
codata Tree (α : Type u)
  | node (a : α) (children : Forest (Tree α))

#check @Tree.node
#check @Tree.B.node_children
#check @Tree.dtor
#synth Codata.Container Tree _ _

def Tree.leaf {α : Type u} (a : α) : Tree α := Tree.node a Forest.nil

@[simp] theorem Tree.dtor_leaf {α : Type u} (a : α) : (Tree.leaf a).dtor = .node a Forest.nil := by
  simp [Tree.leaf]

/-- The tree whose every node has two children, corecursively. -/
def Tree.bin {α : Type u} (a : α) : Tree α :=
  Tree.corec (S := Unit) (fun _ => .node a (Forest.cons () (Forest.cons () Forest.nil))) ()

theorem Tree.dtor_bin {α : Type u} (a : α) :
    (Tree.bin a).dtor = .node a (Codata.Container.map (fun _ => Tree.bin a)
      (Forest.cons () (Forest.cons () Forest.nil))) := by
  rw [Tree.bin, Tree.dtor_corec]
  rfl

-- Parameter positions under a function type and through a container.
data Node (α : Type u)
  | leaf (f : Bool → α)
  | branch (as : List α) (l r : Node α)

#check @Node.P.leaf_f
#check @Node.P.branch_as
#check @Node.Shape₀.branch
#synth Codata.Container Node _ _

-- Indexed: the instance is at every index.
data Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

#check @Vec.Sh
#check @Vec.Pos
#synth Codata.Container (fun α => Vec α 2) _ _

-- The parameter in a negative position is not a parameter position: the type is declared as
-- before, without the instance.
data Neg (α : Type u)
  | mk (f : α → Nat) (n : Neg α)
  | stop

#check @Neg.mk

open Lean in
run_cmd do
  if (← getEnv).contains `ParamTest.Neg.Sh then throwError "unexpected container for `Neg`"

end

end ParamTest
