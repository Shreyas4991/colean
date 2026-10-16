import Colean.DataCmd

/-! # Test: declared types as occurrence structures in their parameter

A `data` or `codata` whose last parameter is a type `α` used only at parameter positions (as the
type of a field, under a function type, or nested) has an occurrence structure in `α`: the
command declares the erased shapes `T.Shape₀`, the parameter positions `T.P`, the shapes `T.Sh`
(the erased trees) and positions `T.Pos` of the structure, the structure
`T.occ : Occ T.Sh T.Pos (fun α => T params α idx)` registered as a leaf, and the constructor-level
lemmas `T.map_c` (`Occ.map T.occ T.occ f` on a constructor application) and `T.rel_c`
(`Occ.Rel T.occ T.occ R` on two constructor applications from `R` and `Rel R` on their
arguments). Nested occurrences may then go through declared types, which covers the mixed
inductive/coinductive blocks. -/

universe u

namespace ParamTest

noncomputable section

-- Finite lists: the erased shapes are the lengths.
data Forest (X : Type u)
  | nil
  | cons (t : X) (f : Forest X)

#check @Forest.Shape₀.cons
#check @Forest.P.cons_t
#check @Forest.shapeEquiv
#check @Forest.Sh
#check @Forest.Pos
#check @Forest.occ
#check @Forest.map_cons
#check @Forest.rel_cons

/-- The sum of a forest of numbers, by the fold. -/
def Forest.sum (f : Forest Nat) : Nat :=
  Forest.fold (S := Nat) (fun | .nil => 0 | .cons t f => t + f) f

-- An inductive type nesting through a declared inductive type: the induction hypothesis holds
-- at the positions of the forest.
data Rose (α : Type u)
  | node (a : α) (children : Forest (Rose α))

#check @Rose.rec
#check @Rose.occ

def Rose.size {α : Type u} (t : Rose α) : Nat :=
  Rose.fold (S := Nat) (fun | .node _ cs => cs.sum + 1) t

theorem Rose.size_node {α : Type u} (a : α) (cs : Forest (Rose α)) :
    (Rose.node a cs).size = Forest.sum (Codata.Occ.map Forest.occ Forest.occ Rose.size cs) + 1 := by
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
#check @Tree.occ
#check @Tree.map_node
#check @Tree.rel_node

def Tree.leaf {α : Type u} (a : α) : Tree α := Tree.node a Forest.nil

@[simp] theorem Tree.dtor_leaf {α : Type u} (a : α) : (Tree.leaf a).dtor = .node a Forest.nil := by
  simp [Tree.leaf]

/-- The tree whose every node has two children, corecursively. -/
def Tree.bin {α : Type u} (a : α) : Tree α :=
  Tree.corec (S := Unit) (fun _ => .node a (Forest.cons () (Forest.cons () Forest.nil))) ()

theorem Tree.dtor_bin {α : Type u} (a : α) :
    (Tree.bin a).dtor = .node a (Codata.Occ.map Forest.occ Forest.occ (fun _ => Tree.bin a)
      (Forest.cons () (Forest.cons () Forest.nil))) := by
  rw [Tree.bin, Tree.dtor_corec]
  rfl

-- Parameter positions under a function type and nested in a list.
data Node (α : Type u)
  | leaf (f : Bool → α)
  | branch (as : List α) (l r : Node α)

#check @Node.P.leaf_f
#check @Node.P.branch_as
#check @Node.Shape₀.branch
#check @Node.occ
#check @Node.map_leaf
#check @Node.map_branch
#check @Node.rel_branch

-- Indexed: the instance is at every index.
data Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

#check @Vec.Sh
#check @Vec.Pos
#check @Vec.occ
#synth Codata.OccLeaf (fun α => Vec α 2) _ _
#check @Vec.map_cons
#check @Vec.rel_cons

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
