import Colean.DataCmd

/-! # Test: declared types nested through in their parameter

A `datatype` or `codatatype` whose parameter `α` is used only at parameter positions (as the type of
a field, under a function type, or nested) gets `PolyIso` and `PolyMap` instances in `α` (step 5,
`T.Poly.*`), with the `simp` lemmas `T.Poly.map_c` and `T.Poly.mem_c`, so that later
declarations nest through it. This is what a `mixed_mutual` block does for its runs inside, with
the parameter standing for the outer types (`Mixed.lean`): here the trees through the forests,
by hand. -/

universe u

namespace ParamTest

open Codata

noncomputable section

-- Finite lists.
datatype Forest (X : Type u)
  | nil
  | cons (t : X) (f : Forest X)

#check @Forest.Poly.instPolyIso
#check @Forest.Poly.instPolyIsoEta
#check @Forest.Poly.map_cons
#check @Forest.Poly.mem_cons

/-- The sum of a forest of numbers, by the fold. -/
def Forest.sum (f : Forest Nat) : Nat :=
  Forest.fold (S := Nat) (fun | .nil => 0 | .cons t f => t + f) f

-- An inductive type nesting through a declared inductive type: the induction hypothesis holds
-- at the members of the forest.
datatype Rose (α : Type u)
  | node (a : α) (children : Forest (Rose α))

/--
info: @Rose.rec : {α : Type u_2} →
  {motive : Rose α → Sort u_1} →
    ((a : α) →
        (children : Forest (Rose α)) →
          ((t : Rose α) → PolyIso.Mem (fun X => Forest X) t children → motive t) → motive (Rose.node a children)) →
      (t : Rose α) → motive t
-/
#guard_msgs in #check @Rose.rec

def Rose.size {α : Type u} (t : Rose α) : Nat :=
  Rose.fold (S := Nat) (fun | .node _ cs => cs.sum + 1) t

example {α : Type u} (a b : α) : (Rose.node a (.cons (.node b .nil) .nil)).size = 2 := by
  simp [Rose.size, Forest.sum]

theorem Rose.size_pos {α : Type u} (t : Rose α) : 0 < t.size := by
  cases t with
  | node a cs => simp [Rose.size]

-- A coinductive type nesting through a declared inductive type: finitely branching trees of
-- infinite depth, the branching given by `Forest`. This is the mixed block `Tree`/`Forest`.
codatatype Tree (α : Type u)
  | node (a : α) (children : Forest (Tree α))

/-- The tree whose every node has two children, corecursively. -/
def Tree.bin {α : Type u} (a : α) : Tree α :=
  Tree.corec (S := Unit) (fun _ => .node a (.cons () (.cons () .nil))) ()

theorem Tree.bin_eq {α : Type u} (a : α) :
    Tree.bin a = .node a (.cons (.bin a) (.cons (.bin a) .nil)) := by
  conv_lhs => rw [← Tree.ctor_dtor (Tree.bin a), Tree.bin, Tree.dtor_corec]
  simp [Tree.bin]

-- Parameter positions under a function type and nested in a list.
datatype Node (α : Type u)
  | leaf (f : Bool → α)
  | branch (as : List α) (l r : Node α)

#check @Node.Poly.instPolyIso
#check @Node.Poly.map_branch

-- Indexed: the instance is at every index.
datatype Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

#synth PolyIso (fun α : Type => Vec α 2) _ _
#check @Vec.Poly.map_cons

-- The parameter in a negative position is not a parameter position: the type is declared as
-- before, without the instance.
datatype Neg (α : Type u)
  | mk (f : α → Nat) (n : Neg α)
  | stop

#check @Neg.mk

open Lean in
run_cmd do
  if (← getEnv).contains `ParamTest.Neg.Poly.instPolyIso then
    throwError "unexpected instance for `Neg`"

end

end ParamTest
