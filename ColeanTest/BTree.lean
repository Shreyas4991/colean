import Mathlib.Basic.Real.Basic
import Colean.CodataCmd

/-! Trees branching over an arbitrary type: a recursive argument under a function type whose
domain is a parameter. -/

universe u v w

namespace CodataTest

noncomputable section

codatatype BTree (I : Type u) (α : Type v)
  | node (a : α) (children : I → BTree I α)

#check @BTree.corec
#check @BTree.F.Rel.node
#check @BTree.node
#check @BTree.B.node_children

/-- The constant tree. -/
def BTree.const {I : Type u} {α : Type v} (a : α) : BTree I α :=
  BTree.corec (fun _ => .node a fun _ => ()) ()

example {I : Type u} {α : Type v} (a : α) :
    (BTree.const (I := I) a).dtor = .node a fun _ => BTree.const a := BTree.dtor_corec _ _

/-- A tree with a child for every real number: the label at path `[r₁, …, rₙ]` is the sum. -/
noncomputable def BTree.sums : BTree ℝ ℝ := BTree.corec (fun x => .node x fun r => x + r) 0

/-- Map on labels, by corecursion; `map id = id` by bisimulation and `cases`. -/
def BTree.map {I : Type u} {α : Type v} {β : Type w} (f : α → β) (t : BTree I α) : BTree I β :=
  BTree.corec (fun t => match t.dtor with | .node a c => .node (f a) c) t

example {I : Type u} {α : Type v} (t : BTree I α) : BTree.map id t = t := by
  refine BTree.bisim (fun x y => x = BTree.map id y) ?_ rfl
  rintro _ y rfl
  cases y with
  | node a c =>
    simp [BTree.map, BTree.dtor_corec]

-- Plain and functional recursive arguments together.
codatatype Mixed (I : Type u)
  | leaf
  | node (t : Mixed I) (f : I → Mixed I)

example {I : Type u} (t t' : Mixed I) (f f' : I → Mixed I) :
    Mixed.node t f = Mixed.node t' f' ↔ t = t' ∧ f = f' := by simp

example {I : Type u} (t : Mixed I) (f : I → Mixed I) : Mixed.leaf ≠ Mixed.node t f := by simp

end

end CodataTest
