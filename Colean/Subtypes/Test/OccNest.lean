import Colean.Subtypes.MutualCmd

/-! # Test: nested occurrences through the combinators

The occurrence structure of an argument type is built by recursion on its syntax: products,
sums, functions and dependent pairs over constant types, and named type constructors (leaves).
Here the shapes that no single container instance covered: `T × T`, `A → List T`,
`Option (T × T)`, `T ⊕ A`, `(n : ℕ) × (Fin n → T)`, a function from a proposition, occurrences
at different indices in one argument, and a declared type whose parameter occurs as `α × α`,
nested through. -/

universe u

namespace OccTest

noncomputable section

/-! ### `T × T` -/

data BinTree
  | leaf
  | node (children : BinTree × BinTree)

#check @BinTree.node
#check @BinTree.Shape.node
#check @BinTree.B.node_children
#check @BinTree.rec
#check @BinTree.fold_node

def BinTree.size (t : BinTree) : Nat :=
  BinTree.fold (S := Nat) (fun | .leaf => 1 | .node p => p.1 + p.2 + 1) t

/-- The fold computes through the product: `map_prod` and `map_hole`. -/
theorem BinTree.size_node (l r : BinTree) :
    (BinTree.node (l, r)).size = l.size + r.size + 1 := by
  rw [BinTree.size, BinTree.fold_node]
  simp only [Codata.Occ.map_prod, Codata.Occ.map_hole]
  rfl

/-- Induction: the hypotheses at the two positions, through `forall_toC_prod` and
`forall_toC_hole`. -/
theorem BinTree.size_pos (t : BinTree) : 0 < t.size := by
  induction t with
  | leaf => rw [BinTree.size, BinTree.fold_leaf]; exact Nat.one_pos
  | node p ih =>
    obtain ⟨l, r⟩ := p
    rw [BinTree.size_node]
    exact Nat.succ_pos _

/-! ### The same coinductively, with bisimulation through the product -/

codata Bin (α : Type u)
  | node (a : α) (children : Bin α × Bin α)

#check @Bin.node
#check @Bin.F.Rel.node
#check @Bin.dtor_corec

def Bin.const {α : Type u} (a : α) : Bin α :=
  Bin.corec (S := Unit) (fun _ => .node a ((), ())) ()

@[simp] theorem Bin.dtor_const {α : Type u} (a : α) :
    (Bin.const a).dtor = .node a (Bin.const a, Bin.const a) := by
  rw [Bin.const, Bin.dtor_corec]
  simp only [Bin.F.map_node, Codata.Occ.map_prod, Codata.Occ.map_hole]

/-- Two corecursions with different states are equal: the relation is passed through the pair
by `rel_prod_intro` and `rel_hole_intro`. -/
example {α : Type u} (a : α) : Bin.const a = Bin.corec (S := Nat) (fun n => .node a (n + 1, n + 2)) 0 := by
  refine Bin.bisim (fun x y => x = Bin.const a ∧ ∃ n, y = Bin.corec (fun n => .node a (n + 1, n + 2)) n)
    ?_ ⟨rfl, 0, rfl⟩
  rintro _ _ ⟨rfl, n, rfl⟩
  simp only [Bin.dtor_const, Bin.dtor_corec, Bin.F.map_node, Codata.Occ.map_prod, Codata.Occ.map_hole]
  exact .node _ _ _ (Codata.Occ.rel_prod_intro _ _ _ _ (Codata.Occ.rel_hole_intro ⟨rfl, _, rfl⟩)
    (Codata.Occ.rel_hole_intro ⟨rfl, _, rfl⟩))

/-! ### A function into a list, an option of a pair, a sum, a dependent pair -/

codata Proc (α : Type u)
  | act (k : α → List (Proc α))
  | choice (c : Option (Proc α × Proc α))
  | stop

#check @Proc.act
#check @Proc.B.act_k
#check @Proc.B.choice_c
#check @Proc.F.map_act
#check @Proc.F.Rel.choice

def Proc.loop {α : Type u} : Proc α := Proc.corec (S := Unit) (fun _ => .act fun _ => [(), ()]) ()

theorem Proc.dtor_loop {α : Type u} :
    (Proc.loop : Proc α).dtor = .act fun _ => [Proc.loop, Proc.loop] := by
  rw [Proc.loop, Proc.dtor_corec]
  simp only [Proc.F.map_act, Codata.Occ.map_pi, Codata.Occ.map_list, List.map_cons, List.map_nil]

data Tm (α : Type u)
  | var (a : α)
  | app (f : Tm α ⊕ α) (arg : Tm α)

#check @Tm.app
#check @Tm.B.app_f
#check @Tm.rec

data Rose
  | node (children : (n : Nat) × (Fin n → Rose))

#check @Rose.node
#check @Rose.B.node_children
#check @Rose.rec

/-! ### A function from a proposition -/

data Guarded
  | mk (n : Nat) (k : 0 < n → List Guarded)

#check @Guarded.mk
#check @Guarded.B.mk_k

/-! ### Occurrences at two indices in one argument -/

data Chain : Nat → Type
  | zero : Chain 0
  | link {n : Nat} (p : Chain n × Chain (n + 1)) : Chain (n + 2)

#check @Chain.link
#check @Chain.B.link_p
#check @Chain.idx
#check @Chain.rec

/-! ### A declared type whose parameter occurs as a pair, nested through -/

data Two (α : Type u)
  | mk (p : α × α)

#check @Two.occ
#check @Two.map_mk
#check @Two.rel_mk

data Tree
  | leaf
  | node (c : Two Tree)

#check @Tree.node
#check @Tree.rec

def Tree.size (t : Tree) : Nat :=
  Tree.fold (S := Nat) (fun | .leaf => 1 | .node c => Two.fold (fun | .mk p => p.1 + p.2) c + 1) t

theorem Tree.size_node (l r : Tree) : (Tree.node (Two.mk (l, r))).size = l.size + r.size + 1 := by
  rw [Tree.size, Tree.fold_node, Two.map_mk]
  simp only [Codata.Occ.map_prod, Codata.Occ.map_hole]
  rw [Two.fold_mk]
  rfl

end

end OccTest
