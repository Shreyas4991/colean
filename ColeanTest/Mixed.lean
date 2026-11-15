import Colean.MutualCmd

/-! # Test: mixed `datatype`/`codatatype` blocks

A `mixed_mutual` block nests its declarations in the order written, the first outermost. Here
the coinductive type comes first: the finitely branching infinite trees. The forests are
declared open in the trees (`Forest.Open α X`), the trees nest through `Forest.Open α (Tree α)`,
and `Forest α` is that type, with the whole interface of a `datatype` declaration. -/

universe u

namespace MixedTest

open Codata

noncomputable section

mixed_mutual
codatatype Tree (α : Type u)
  | node (a : α) (children : Forest α)
datatype Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

/-! ### What the user sees

The trees as a single `codatatype` declaration with `Forest α` for its children; the forests as a
single `datatype` declaration with `Tree α` for its trees. -/

/-- info: @Tree.node : {α : Type u_1} → α → Forest α → Tree α -/
#guard_msgs in #check @Tree.node
/-- info: @Forest.cons : {α : Type u_1} → Tree α → Forest α → Forest α -/
#guard_msgs in #check @Forest.cons
/-- info: @Forest.nil : {α : Type u_1} → Forest α -/
#guard_msgs in #check @Forest.nil
/--
info: @Tree.corec : {α : Type u_2} → {S : Type u_1} → (S → Tree.F α S) → S → Tree α
-/
#guard_msgs in #check @Tree.corec
/--
info: @Tree.bisim : ∀ {α : Type u_1} (R : Tree α → Tree α → Prop),
  (∀ (x y : Tree α), R x y → Tree.F.Rel R x.dtor y.dtor) → ∀ {x y : Tree α}, R x y → x = y
-/
#guard_msgs in #check @Tree.bisim
/--
info: @Tree.casesOn : {α : Type u_2} →
  {motive : Tree α → Sort u_1} →
    (t : Tree α) → ((a : α) → (children : Forest α) → motive (Tree.node a children)) → motive t
-/
#guard_msgs in #check @Tree.casesOn
/--
info: @Forest.rec : {α : Type u_2} →
  {motive : Forest α → Sort u_1} →
    motive Forest.nil →
      ((t : Tree α) → (f : Forest α) → motive f → motive (Forest.cons t f)) → (t : Forest α) → motive t
-/
#guard_msgs in #check @Forest.rec
/--
info: @Forest.fold : {α : Type u_2} → {S : Type u_1} → (Forest.F α S → S) → Forest α → S
-/
#guard_msgs in #check @Forest.fold
/--
info: @Forest.casesOn : {α : Type u_2} →
  {motive : Forest α → Sort u_1} →
    (t : Forest α) → motive Forest.nil → ((t : Tree α) → (f : Forest α) → motive (Forest.cons t f)) → motive t
-/
#guard_msgs in #check @Forest.casesOn
/-- info: @Forest.F.cons : {α : Type u_1} → {X : Type u_2} → Tree α → X → Forest.F α X -/
#guard_msgs in #check @Forest.F.cons
/--
info: @Forest.fold_cons : ∀ {α : Type u_2} {S : Type u_1} (a : Forest.F α S → S) (t : Tree α) (f : Forest α),
  Forest.fold a (Forest.cons t f) = a (Forest.F.cons t (Forest.fold a f))
-/
#guard_msgs in #check @Forest.fold_cons
/--
info: @Forest.contract : {α : Type u_1} → Data.Contract (fun p => Forest α) fun X p => Forest.F α (X ())
-/
#guard_msgs in #check @Forest.contract
/--
info: @Forest.cons_inj : ∀ {α : Type u_1} (t : Tree α) (f : Forest α) (t' : Tree α) (f' : Forest α),
  Forest.cons t f = Forest.cons t' f' ↔ t = t' ∧ f = f'
-/
#guard_msgs in #check @Forest.cons_inj
/-- info: @Forest.cons_ne_nil : ∀ {α : Type u_1} (t : Tree α) (f : Forest α), Forest.cons t f ≠ Forest.nil -/
#guard_msgs in #check @Forest.cons_ne_nil
/--
info: @Forest.mem_cons : ∀ {α : Type u_1} (t : Tree α) (f : Forest α) (x : Tree α), x ∈ Forest.cons t f ↔ x = t ∨ x ∈ f
-/
#guard_msgs in #check @Forest.mem_cons

/-! The functor of the trees has the forests at its state, the open forests: corecursion builds
a forest of states, with the constructors of `Forest.Open`, which dot notation finds. -/

/--
info: @Tree.F.node : {α : Type u_1} → {X : Type u_2} → α → Forest.Open α X → Tree.F α X
-/
#guard_msgs in #check @Tree.F.node

/-! ### Corecursion on trees -/

def Tree.leaf {α : Type u} (a : α) : Tree α := Tree.node a Forest.nil

@[simp] theorem Tree.dtor_leaf {α : Type u} (a : α) : (Tree.leaf a).dtor = .node a Forest.nil := by
  simp [Tree.leaf]

/-- The tree with two copies of itself as children, corecursively. -/
def Tree.bin {α : Type u} (a : α) : Tree α :=
  Tree.corec (S := Unit) (fun _ => .node a (.cons () (.cons () .nil))) ()

/-- The unfolding of `Tree.bin`, one step: `simp` maps the forest of states through the instance
of the open forests (`Forest.Open.Poly.map_cons`). -/
theorem Tree.bin_eq {α : Type u} (a : α) :
    Tree.bin a = .node a (.cons (.bin a) (.cons (.bin a) .nil)) := by
  conv_lhs => rw [← Tree.ctor_dtor (Tree.bin a), Tree.bin, Tree.dtor_corec]
  simp [Tree.bin]

example {α : Type u} (t : Tree α) : ∃ a cs, t = Tree.node a cs := by
  cases t with
  | node a cs => exact ⟨a, cs, rfl⟩

/-! ### Folds and induction on forests -/

/-- The number of trees in a forest. -/
def Forest.size {α : Type u} (f : Forest α) : Nat :=
  Forest.fold (S := Nat) (fun | .nil => 0 | .cons _ n => n + 1) f

@[simp] theorem Forest.size_nil {α : Type u} : (Forest.nil : Forest α).size = 0 := by
  simp [Forest.size]

@[simp] theorem Forest.size_cons {α : Type u} (t : Tree α) (f : Forest α) :
    (Forest.cons t f).size = f.size + 1 := by
  simp [Forest.size]

example {α : Type u} (a : α) : (Tree.bin a).dtor = .node a (.cons (.bin a) (.cons (.bin a) .nil)) := by
  conv_lhs => rw [Tree.bin_eq]
  simp

/-- The children of `Tree.bin a`, by cases on the tree. -/
def Tree.children {α : Type u} (t : Tree α) : Forest α := Tree.casesOn t fun _ cs => cs

example {α : Type u} (a : α) : (Tree.bin a).children.size = 2 := by
  rw [Tree.bin_eq]
  simp [Tree.children]

/-- Membership in a forest is the trees in it: `mem_cons`, `mem_nil`. -/
theorem Forest.mem_size {α : Type u} (f : Forest α) (t : Tree α) (h : t ∈ f) : 0 < f.size := by
  induction f with
  | nil => simp at h
  | cons t' f ih => simp

example {α : Type u} (f : Forest α) : f = Forest.nil ∨ ∃ t f', f = Forest.cons t f' := by
  cases f with
  | nil => exact Or.inl rfl
  | cons t f' => exact Or.inr ⟨t, f', rfl⟩

/-- The recursor, at a dependent motive. -/
def Forest.trees {α : Type u} (f : Forest α) : List (Tree α) :=
  Forest.rec (motive := fun _ => List (Tree α)) [] (fun t _ l => t :: l) f

example {α : Type u} (t : Tree α) (f : Forest α) :
    (Forest.cons t f).trees = t :: f.trees := by
  simp [Forest.trees]

/-! ### Bisimulation on trees

The children of a node are a forest of trees, so a bisimulation step relates two forests
(`Tree.F.Rel.node`), at the open forests of the functor; `Tree.F.rel_map` provides it for the
images of one layer. -/

/-- One step of relabelling: the next states are the children themselves. -/
def Tree.relabelStep {α : Type u} (h : α → α) (t : Tree α) : Tree.F α (Tree α) :=
  match t.dtor with
  | .node a cs => .node (h a) cs

/-- Relabel every node, corecursively, with the tree as the state. -/
def Tree.relabel {α : Type u} (h : α → α) : Tree α → Tree α := Tree.corec (Tree.relabelStep h)

theorem Tree.relabelStep_id {α : Type u} (t : Tree α) : Tree.relabelStep id t = t.dtor := by
  unfold Tree.relabelStep
  cases t.dtor
  rfl

theorem Tree.relabel_id {α : Type u} (t : Tree α) : Tree.relabel id t = t := by
  refine Tree.bisim (fun x y => x = Tree.relabel id y) ?_ rfl
  rintro _ y rfl
  rw [Tree.relabel, Tree.dtor_corec, Tree.relabelStep_id]
  conv => arg 3; rw [← Tree.F.map_id y.dtor]
  exact Tree.F.rel_map _ _ _ _ fun _ => rfl

/-! Coinduction inside induction: a function on forests by the fold, whose step relabels a tree
corecursively. -/

/-- Relabel the trees of a forest. -/
def Forest.relabelAll {α : Type u} (h : α → α) (fo : Forest α) : Forest α :=
  Forest.fold (S := Forest α) (fun | .nil => .nil | .cons t fo' => .cons (Tree.relabel h t) fo') fo

theorem Forest.relabelAll_id {α : Type u} (fo : Forest α) : Forest.relabelAll id fo = fo := by
  induction fo with
  | nil => simp [Forest.relabelAll]
  | cons t fo ih =>
    simp only [Forest.relabelAll, Forest.fold_cons] at ih ⊢
    rw [ih, Tree.relabel_id]

end

end MixedTest
