import Colean.MutualCmd

/-! # Test: mixed `data`/`codata` blocks

A `mixed_mutual` block nests its declarations in the order written, the first outermost. Here
the coinductive types come first: the `data` types take the coinductive family as an extra
parameter, and the `codata` types nest through them. -/

universe u

namespace MixedTest

noncomputable section

-- One coinductive type without indices: the parameter is a type.
mixed_mutual
codata Tree (α : Type u)
  | node (a : α) (children : Forest α)
data Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

-- Binary trees with labeled right edges: the inductive type first, so the labeled edges are
-- inside the finite trees (`LabeledEdge α X` for any `X`, `BinTree.cons : Tree α →
-- LabeledEdge α (BinTree α) → BinTree α`).
mixed_mutual
data BinTree (α : Type u)
  | nil
  | cons (left : Tree α) (right : LabeledEdge α)
codata LabeledEdge (α : Type u)
  | mk (a : α) (node : BinTree α)
end

#check @BinTree.cons
#check @LabeledEdge.mk

#check @Forest.nil
#check @Forest.cons
#check @Tree.node
#check @Tree.F.node
#check @Tree.dtor
#check @Forest.rec
#check Tree.corec
#check Tree.bisim
#check @Forest.occ
#check @Forest.map_cons
#check @Forest.rel_cons
#check @LabeledEdge.map_mk
#check @LabeledEdge.rel_mk

def Tree.leaf {α : Type u} (a : α) : Tree α := Tree.node a Forest.nil

@[simp] theorem Tree.dtor_leaf {α : Type u} (a : α) : (Tree.leaf a).dtor = .node a Forest.nil := by
  simp [Tree.leaf]

/-- The number of trees in a forest, by the fold of the parameterised type. -/
def Forest.size {α : Type u} (f : Forest α (Tree α)) : Nat :=
  Forest.fold (S := Nat) (fun | .nil => 0 | .cons _ n => n + 1) f

theorem Forest.size_cons {α : Type u} (t : Tree α) (f : Forest α (Tree α)) :
    (Forest.cons t f).size = f.size + 1 := by
  rw [Forest.size, Forest.fold_cons]
  rfl

/-- The tree with two copies of itself as children, corecursively. -/
def Tree.bin {α : Type u} (a : α) : Tree α :=
  Tree.corec (S := Unit) (fun _ => .node a (Forest.cons () (Forest.cons () Forest.nil))) ()

theorem Tree.dtor_bin {α : Type u} (a : α) :
    (Tree.bin a).dtor = .node a (Codata.Occ.map (Forest.occ α) (Forest.occ α) (fun _ => Tree.bin a)
      (Forest.cons () (Forest.cons () Forest.nil))) := by
  rw [Tree.bin, Tree.dtor_corec]
  rfl

/-- The unfolding of `Tree.bin`, with the constructor-level lemmas `Forest.map_cons`,
`Forest.map_nil` computing the map on the forest of states. -/
example : Tree.bin 0 = .node 0 (.cons (.bin 0) <| .cons (.bin 0) .nil) := by
  conv_lhs => rw [← Tree.ctor_dtor (Tree.bin 0), Tree.dtor_bin]
  rw [Forest.map_cons, Forest.map_cons, Forest.map_nil]
  rfl

example {α : Type u} (t : Tree α) : ∃ a cs, t = Tree.node a cs := by
  cases t with
  | node a cs => exact ⟨a, cs, rfl⟩

/-! Equality of trees by bisimulation. The children of a node form a forest of trees, so the
bisimulation step has to relate two *forests*: `Tree.F.Rel.node` asks for
`Occ.Rel R cs cs'`, the forests having the same shape (the same erased forest) and
`R`-related trees at all positions, and `Occ.rel_map` provides it when both forests are
images of one forest. This is where coinduction sees through the inductive part. -/

/-- One step of relabelling: the next states are the children themselves. -/
def Tree.relabelStep {α : Type u} (h : α → α) (t : Tree α) : Tree.F α (Tree α) :=
  match t.dtor with
  | .node a cs => .node (h a) cs

/-- Relabel every node, corecursively, with the tree as the state. -/
def Tree.relabel {α : Type u} (h : α → α) : Tree α → Tree α := Tree.corec (Tree.relabelStep h)

theorem Tree.relabel_id {α : Type u} (t : Tree α) : Tree.relabel id t = t := by
  refine Tree.bisim (fun x y => x = Tree.relabel id y) ?_ rfl
  rintro _ y rfl
  rw [Tree.relabel, Tree.dtor_corec]
  simp only [Tree.relabelStep]
  rcases hy : y.dtor with ⟨a, cs⟩
  simp only [Tree.F.map_node]
  refine .node _ _ _ ?_
  have h := Codata.Occ.rel_map (Forest.occ α) (Forest.occ α) (Forest.occ α)
    (fun x y => x = Tree.relabel id y) (Tree.corec (Tree.relabelStep id)) (fun x => x) cs
    fun _ => rfl
  rwa [Codata.Occ.map_id] at h

theorem Tree.relabel_comp {α : Type u} (g f : α → α) (t : Tree α) :
    Tree.relabel g (Tree.relabel f t) = Tree.relabel (g ∘ f) t := by
  refine Tree.bisim (fun x y => ∃ t, x = Tree.relabel g (Tree.relabel f t) ∧
    y = Tree.relabel (g ∘ f) t) ?_ ⟨t, rfl, rfl⟩
  rintro _ _ ⟨t, rfl, rfl⟩
  simp only [Tree.relabel, Tree.dtor_corec, Tree.relabelStep]
  rcases ht : t.dtor with ⟨a, cs⟩
  simp only [Tree.F.map_node, Codata.Occ.map_map, Function.comp_apply]
  exact .node _ _ _ (Codata.Occ.rel_map _ _ _ _ _ _ cs fun x => ⟨x, rfl, rfl⟩)

/-! The mirror: coinduction inside induction. A function on forests of trees, by the fold,
whose step relabels a tree corecursively; the proof that relabelling by `id` is the identity on
forests is by induction on the forest, and its `cons` case proves the equality of two trees by
a bisimulation. The bisimulation does not use the induction hypothesis (it is about the tree
`t`, not the forest), and the induction hypothesis is not used inside the bisimulation. -/

/-- Relabel the trees of a forest: the fold, with a corecursive function in its step. -/
def Forest.relabelAll {α : Type u} (h : α → α) (fo : Forest α (Tree α)) : Forest α (Tree α) :=
  Forest.fold (S := Forest α (Tree α))
    (fun | .nil => .nil | .cons t fo' => .cons (Tree.relabel h t) fo') fo

theorem Forest.relabelAll_id {α : Type u} (fo : Forest α (Tree α)) :
    Forest.relabelAll id fo = fo := by
  induction fo with
  | nil => rw [Forest.relabelAll, Forest.fold_nil]
  | cons t fo ih =>
    -- The inductive step: the fold computes one `cons`, the tail is the induction hypothesis.
    rw [Forest.relabelAll, Forest.fold_cons]
    show Forest.cons (Tree.relabel id t) (Forest.relabelAll id fo) = Forest.cons t fo
    rw [ih]
    -- The head is a tree: a bisimulation, inside the inductive step (this is `Tree.relabel_id`
    -- proved in place).
    congr 1
    refine Tree.bisim (fun x y => x = Tree.relabel id y) ?_ rfl
    rintro _ y rfl
    rw [Tree.relabel, Tree.dtor_corec]
    simp only [Tree.relabelStep]
    rcases hy : y.dtor with ⟨a, cs⟩
    simp only [Tree.F.map_node]
    refine .node _ _ _ ?_
    have h := Codata.Occ.rel_map (Forest.occ α) (Forest.occ α) (Forest.occ α)
      (fun x y => x = Tree.relabel id y) (Tree.corec (Tree.relabelStep id)) (fun x => x) cs
      fun _ => rfl
    rwa [Codata.Occ.map_id] at h

example {α : Type u} (f : Forest α (Tree α)) : f = Forest.nil ∨ ∃ t f', f = Forest.cons t f' := by
  cases f with
  | nil => exact Or.inl rfl
  | cons t f' => exact Or.inr ⟨t, f', rfl⟩

-- Two coinductive types: the parameter is a family over their enumeration.
mixed_mutual
codata Tree₂ (α : Type u)
  | node (a : α) (children : Forest₂ α)
codata Str₂ (α : Type u)
  | cons (hd : Tree₂ α) (tl : Str₂ α)
data Forest₂ (α : Type u)
  | nil
  | cons (t : Tree₂ α) (s : Str₂ α) (f : Forest₂ α)
end

#check @Forest₂.cons
#check @Forest₂.map_cons
#check @Forest₂.rel_cons
#check @Tree₂.node
#check @Str₂.cons
#check @Tree₂_Str₂.F.node
#check @Tree₂_Str₂.F.Rel.node
#check @Tree₂.corec
#check @Forest₂.occ

-- One coinductive type with an index: the parameter is a family over the index.
mixed_mutual
codata VTree (α : Type u) : Nat → Type u
  | node {n : Nat} (a : α) (children : VForest α n) : VTree α n
data VForest (α : Type u) : Nat → Type u
  | nil : VForest α 0
  | cons {n : Nat} (t : VTree α n) (f : VForest α n) : VForest α (n + 1)
end

#check @VForest.cons
#check @VForest.map_cons
#check @VForest.rel_cons
#check @VTree.node
#check @VTree.dtor
#check @VTree.F.Rel.node

/-- A forest of `n` units. -/
def VForest.units {α : Type u} : (n : Nat) → VForest α (fun _ => Unit) n
  | 0 => .nil
  | n + 1 => .cons () (VForest.units n)

/-- The tree of depth `n` with `n` children of depth `n`, and so on, corecursively: the state
at index `n` is a unit. -/
def VTree.full {α : Type u} (a : α) {n : Nat} : VTree α n :=
  VTree.corec (S := fun _ => Unit) (fun n _ => .node a (VForest.units n)) ()

theorem VTree.dtor_full {α : Type u} (a : α) (n : Nat) :
    (VTree.full a (n := n)).dtor = VTree.F.map (fun _ _ => VTree.full a) (.node a (VForest.units n)) := by
  rw [VTree.full, VTree.dtor_corec]
  rfl

end

end MixedTest
