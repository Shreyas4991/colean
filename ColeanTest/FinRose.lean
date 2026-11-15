import Colean.DataCmd

/-! # Test: nested occurrences, inductively

Finite rose trees, with the induction hypothesis for the children by membership in the list,
and a binary tree with optional subtrees. -/

universe u

namespace DataTest

noncomputable section

datatype Rose (α : Type u)
  | node (a : α) (children : List (Rose α))

#check @Rose.rec
#check @Rose.rec_node
#check @Rose.fold_node

-- Through a composite: the induction hypothesis by membership in the composite, a member of
-- an option in the list.
datatype Rose₂ (α : Type u)
  | node (a : α) (children : List (Option (Rose₂ α)))

#check @Rose₂.rec

/-- The number of nodes, by the fold: the children are already folded. -/
def Rose.size {α : Type u} (t : Rose α) : Nat :=
  Rose.fold (S := Nat) (fun | .node _ cs => cs.sum + 1) t

@[simp] theorem Rose.size_node {α : Type u} (a : α) (cs : List (Rose α)) :
    (Rose.node a cs).size = (cs.map Rose.size).sum + 1 := by
  rw [Rose.size, Rose.fold_node, Codata.Occ.map_list]
  rfl

theorem Rose.size_pos {α : Type u} (t : Rose α) : 0 < t.size := by
  cases t with
  | node a cs => simp

/-- Mirror: reverse the children at every node. -/
def Rose.mirror {α : Type u} (t : Rose α) : Rose α :=
  Rose.fold (S := Rose α) (fun | .node a cs => .node a cs.reverse) t

@[simp] theorem Rose.mirror_node {α : Type u} (a : α) (cs : List (Rose α)) :
    (Rose.node a cs).mirror = .node a (cs.map Rose.mirror).reverse := by
  simp [Rose.mirror]

/-- Induction with a nested list: the hypothesis holds at every member of the list, which
`PolyIso.mem_list` turns into the list's own membership. -/
theorem Rose.mirror_mirror {α : Type u} (t : Rose α) : t.mirror.mirror = t := by
  induction t with
  | node a cs ih =>
    have ih' : ∀ x ∈ cs, x.mirror.mirror = x := fun x hx =>
      ih x ((Codata.PolyIso.mem_list x cs).mpr hx)
    simp only [Rose.mirror_node, List.map_reverse, List.reverse_reverse, List.map_map]
    exact congrArg (Rose.node a) ((List.map_congr_left fun x hx => ih' x hx).trans (List.map_id cs))

-- Binary trees with optional subtrees.
datatype BinTree (α : Type u)
  | node (a : α) (l r : Option (BinTree α))

#check @BinTree.rec

def BinTree.size {α : Type u} (t : BinTree α) : Nat :=
  BinTree.fold (S := Nat) (fun | .node _ l r => l.getD 0 + r.getD 0 + 1) t

@[simp] theorem BinTree.size_node {α : Type u} (a : α) (l r : Option (BinTree α)) :
    (BinTree.node a l r).size = (l.map BinTree.size).getD 0 + (r.map BinTree.size).getD 0 + 1 := by
  rw [BinTree.size, BinTree.fold_node, Codata.Occ.map_option, Codata.Occ.map_option]
  rfl

example {α : Type u} (a : α) : (BinTree.node a none none).size = 1 := by simp

end

end DataTest
