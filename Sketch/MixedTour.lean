import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Forall2
import Colean.MutualCmd

/-!
# A tour of mixed blocks

What the `mixed_mutual` command does with a block of `datatype` and `codatatype` declarations, and
what it does not do yet. Read it top to bottom. Part I (sections 1 to 11) is what works, Part II
(section 12) what does not work yet but could, and Part III (sections 13 and 14) what looks like a
bug of the command rather than a limit.

How the file is checked:

* an example without an error on it works;
* the failures of Parts II and III are left as they are, so they show as errors in the infoview;
* a failed block declares nothing, not even the open types of its runs inside, and every example
  has a namespace of its own, so names do not clash.

Uniform blocks, all `datatype` or all `codatatype`, are in `Sketch/MutualTour.lean`, and nesting
through other types in `Sketch/NestingTour.lean`. A mixed block uses both: its runs are uniform
blocks or single types, and they nest through each other.
-/

universe u v

namespace MixedTour

noncomputable section

open Codata

/-! ## Part I: what works -/

/-! ### 1. The idea

A block with both kinds is a nested fixpoint, not a single one. A cyclic system such as trees and
forests has two nested solutions: with the trees outside, the forests are a least fixpoint inside
each tree, and the trees are infinite but finitely branching; with the forests outside, the trees
are finite and each forest may be infinite. The block says which one it means: *the textual order
is the nesting order, the first declaration outermost*.

A *run* is a maximal sequence of adjacent declarations of the same kind. A run is declared as one
type, or as one `mutual` block. The runs are declared from the innermost out. A run inside the
first one is declared *open*: under an internal name, `Forest.Open`, with one more parameter `X`
for the outer types it mentions. The outer run then nests through the open type at its own types,
`Forest.Open α (Tree α)`, by the instances that every declared type gets (`NestingTour.lean`,
section 4). Last, `Forest α` is declared as that type, and the whole interface of the inner run is
restated at it, under the names the user wrote.

A plain `mutual` block refuses to mix kinds, since it would have to choose an order. A
`mixed_mutual` block of one kind is a `mutual` block, with a warning. -/

/-! ### 2. Infinite trees, finite forests

The trees come first, so they are outside: a tree never ends, and each node has a finite forest of
children. This is the classic type of finitely branching infinite trees. -/

namespace Classic

mixed_mutual
codatatype Tree (α : Type u)
  | node (a : α) (children : Forest α)
datatype Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

#print Tree.F

-- What the user sees: two types, each with the interface of its kind.
#check @Tree.node
#check @Forest.nil
#check @Forest.cons
#check @Forest.casesOn
#check @Forest.fold
#check @Forest.rec
#check @Tree.casesOn
#check @Tree.corec
#check @Tree.bisim
-- Trees are members of forests, and `simp` computes membership on the constructors.
#check @Forest.mem_cons

/-- The tree with two copies of itself as children, by corecursion. The step gives a forest of
states, here two `()`; such a forest is an open one (section 4), and dot notation finds its
constructors. -/
def Tree.bin {α : Type u} (a : α) : Tree α :=
  Tree.corec (S := Unit) (fun _ => .node a (.cons () (.cons () .nil))) ()

/-- One step of unfolding: `simp` maps the forest of states to a forest of trees. -/
theorem Tree.bin_eq {α : Type u} (a : α) :
    Tree.bin a = .node a (.cons (.bin a) (.cons (.bin a) .nil)) := by
  conv_lhs => rw [← Tree.ctor_dtor (Tree.bin a), Tree.bin, Tree.dtor_corec]
  simp [Tree.bin]

/-- The number of trees in a forest, by its fold. -/
def Forest.size {α : Type u} (f : Forest α) : Nat :=
  Forest.fold (S := Nat) (fun | .nil => 0 | .cons _ n => n + 1) f

@[simp] theorem Forest.size_cons {α : Type u} (t : Tree α) (f : Forest α) :
    (Forest.cons t f).size = f.size + 1 := by
  simp [Forest.size]

/-- The children of a tree, by cases. -/
def Tree.children {α : Type u} (t : Tree α) : Forest α := Tree.casesOn t fun _ cs => cs

example {α : Type u} (a : α) : (Tree.bin a).children.size = 2 := by
  rw [Tree.bin_eq]
  simp [Tree.children, Forest.size]

/-- The trees of a forest as a list, by the recursor. -/
def Forest.trees {α : Type u} (f : Forest α) : List (Tree α) :=
  Forest.rec (motive := fun _ => List (Tree α)) [] (fun t _ l => t :: l) f

/-- Induction on forests: membership is that of the list of trees. -/
theorem Forest.mem_trees {α : Type u} (f : Forest α) (t : Tree α) : t ∈ f.trees ↔ t ∈ f := by
  induction f with
  | nil => simp [Forest.trees]
  | cons t' f ih => simp [Forest.trees] at ih ⊢; rw [ih]

/-- A forest with a tree in it is not empty: induction, with a membership hypothesis. -/
theorem Forest.size_pos {α : Type u} (f : Forest α) (t : Tree α) (h : t ∈ f) : 0 < f.size := by
  induction f with
  | nil => simp at h
  | cons t' f ih => simp

/-! Bisimulation relates the children of two nodes as forests: `Tree.F.Rel` relates them through
the open forests, and `Tree.F.rel_fmap` gives it for the images of one layer. -/

/-- Relabel every node, with the tree itself as the state. -/
def Tree.relabel {α : Type u} (h : α → α) : Tree α → Tree α :=
  Tree.corec fun t => match t.dtor with | .node a cs => .node (h a) cs

theorem Tree.relabel_id {α : Type u} (t : Tree α) : Tree.relabel id t = t := by
  refine Tree.bisim (fun x y => x = Tree.relabel id y) ?_ rfl
  rintro _ y rfl
  rw [Tree.relabel, Tree.dtor_corec]
  have : (match y.dtor with | .node a cs => Tree.F.node (id a) cs) = y.dtor := by
    cases y.dtor; rfl
  rw [this]
  conv => arg 3; rw [← Tree.F.fmap_id y.dtor]
  exact Tree.F.rel_fmap _ _ _ _ fun _ => rfl

end Classic

/-! ### 3. Finite trees, infinite forests

The same declarations in the other order: the trees are now finite, and a forest may go on
forever. The recursor of the trees has its hypothesis at the members of the forest of children,
`∀ t, t ∈ cs → motive t`, however long the forest is. -/

namespace Other

mixed_mutual
datatype Tree (α : Type u)
  | node (a : α) (cs : Forest α)
codatatype Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

#check @Tree.rec
#check @Forest.corec
#check @Forest.mem_cons

/-- `s` is a child of `t`. -/
def Tree.Child {α : Type u} (s t : Tree α) : Prop := ∃ a cs, t = .node a cs ∧ s ∈ cs

/-- The trees are finite: there is no infinite chain of children, although a node may have
infinitely many. Induction, with the hypothesis at the members of the children. -/
theorem Tree.acc {α : Type u} (t : Tree α) : Acc Tree.Child t := by
  induction t with
  | node a cs ih =>
    refine Acc.intro _ fun s ⟨a', cs', h, hs⟩ => ?_
    obtain ⟨rfl, rfl⟩ := (Tree.node_inj _ _ _ _).mp h
    exact ih s hs

/-- A fold of the trees: the step sees a forest of results, an open forest, here the depth along
the first children. -/
def Tree.leftDepth {α : Type u} (t : Tree α) : Nat :=
  Tree.fold (S := Nat) (fun | .node _ cs => Forest.Open.casesOn cs 0 fun n _ => n + 1) t

example {α : Type u} (a : α) (f : Forest α) :
    (Tree.node a (.cons (.node a .nil) f)).leftDepth = 1 := by
  simp [Tree.leftDepth]

end Other

/-! ### 4. Behind the scenes: the open types

The inner run exists in an open form, `Forest.Open α X`, with `X` for the trees, and `Forest α` is
an abbreviation of `Forest.Open α (Tree α)`. Users meet the open form in one place: the functor of
the outer run at a state `X` has the forests at that state, `Tree.F.node : α → Forest.Open α X →
Tree.F α X`. So a step of `Tree.corec` builds a forest of states, with the constructors and the
functions of `Forest.Open`. -/

namespace Classic

#check @Forest.Open
#print Forest
#check @Forest.Open.cons
#check @Tree.F.node

/-- `n` copies of a state, as an open forest. -/
def rep {α : Type u} {X : Type v} (x : X) : Nat → Forest.Open α X
  | 0 => .nil
  | n + 1 => .cons x (rep x n)

/-- The node labelled `n` has `n` children, each labelled `n + 1`. -/
def Tree.fan (n : Nat) : Tree Nat :=
  Tree.corec (fun n => .node n (rep (n + 1) n)) n

/-- The map of the open forests, which `simp` computes on their constructors. -/
theorem map_rep {α : Type u} {X Y : Type v} (g : X → Y) (x : X) (n : Nat) :
    (Occ.ofIso (Forest.Open α)).map (Occ.ofIso (Forest.Open α)) g (rep x n) = rep (g x) n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp [rep, ih]

theorem Tree.dtor_fan (n : Nat) : (Tree.fan n).dtor = .node n (rep (Tree.fan (n + 1)) n) := by
  rw [Tree.fan, Tree.dtor_corec, Tree.F.fmap_node, map_rep]
  rfl

end Classic

/-! ### 5. Three runs

Processes offer a finite menu, the entries of a menu are a process and an infinite trace, and a
trace ticks forever through menus. The traces are open in the menus, `Trace.Open α X`, the menus
open in the processes and nesting through `Trace.Open α (Menu.Open α X)`, and the processes nest
through both. Then `Menu α := Menu.Open α (Proc α)` and `Trace α := Trace.Open α (Menu α)`. -/

namespace Runs

mixed_mutual
codatatype Proc (α : Type u)
  | step (a : α) (menu : Menu α) (t : Trace α)
datatype Menu (α : Type u)
  | nil
  | cons (p : Proc α) (t : Trace α) (rest : Menu α)
codatatype Trace (α : Type u)
  | tick (m : Menu α) (next : Trace α)
end

#check @Proc.step
#check @Menu.cons
#check @Trace.tick
-- The menus' recursor looks into the traces of an entry by membership of menus in them.
#check @Menu.rec
-- The processes of a menu are those of its entries, directly or through their traces.
#check @Menu.mem_cons
-- The processes' functor has both inner runs open at the state.
#check @Proc.F.step

/-- A trace that ticks through the same menu forever. -/
def Trace.idle {α : Type u} (m : Menu α) : Trace α :=
  Trace.corec (S := Unit) (fun _ => .tick m ()) ()

theorem Trace.idle_eq {α : Type u} (m : Menu α) : Trace.idle m = .tick m (.idle m) := by
  conv_lhs => rw [← Trace.ctor_dtor (Trace.idle m), Trace.idle, Trace.dtor_corec]
  simp [Trace.idle]

/-- The processes of a menu, by its recursor: the traces are not looked into. -/
def Menu.procs {α : Type u} (m : Menu α) : List (Proc α) :=
  Menu.rec (motive := fun _ => List (Proc α)) [] (fun p _ _ _ l => p :: l) m

example {α : Type u} (p : Proc α) (t : Trace α) : (Menu.cons p t .nil).procs = [p] := by
  simp [Menu.procs]

end Runs

/-! ### 6. An inner run of two types

Two adjacent `datatype` declarations form one run, declared as one open block `Rose_Forest.Open`
over the index `Rose_Forest.Ix`. Closed, `Rose_Forest`, `Rose` and `Forest` have the interface of a
`mutual` block: per-type constructors, `casesOn`, and recursors with a motive per type. -/

namespace InnerBlock

mixed_mutual
codatatype T (α : Type u)
  | node (a : α) (r : Rose α)
datatype Rose (α : Type u)
  | node (t : T α) (f : Forest α)
datatype Forest (α : Type u)
  | nil
  | cons (r : Rose α) (f : Forest α)
end

#check @Rose.rec
#check @Rose_Forest.Ix.Rose
-- The trees in a rose, and in a forest.
#check @Rose.mem_node
#check @Forest.mem_cons

/-- The number of roses in a rose, by the recursors per type. -/
def Rose.size {α : Type u} (r : Rose α) : Nat :=
  Rose.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ _ n => n + 1) 0 (fun _ _ a b => a + b) r

example {α : Type u} (t : T α) : (Rose.node t (.cons (.node t .nil) .nil)).size = 2 := by
  simp [Rose.size]

/-- A tree whose rose holds the tree twice; the states go into the open roses and forests. -/
def T.twice {α : Type u} (a : α) : T α :=
  T.corec (S := Unit) (fun _ => .node a (.node () (.cons (.node () .nil) .nil))) ()

theorem T.twice_eq {α : Type u} (a : α) :
    T.twice a = .node a (.node (.twice a) (.cons (.node (.twice a) .nil) .nil)) := by
  conv_lhs => rw [← T.ctor_dtor (T.twice a), T.twice, T.dtor_corec]
  simp [T.twice]

end InnerBlock

/-! In the other order an inner block of `codatatype`: the recursor of the outer `datatype` has its
hypothesis by membership in the closed types of the block. -/

namespace InnerCoBlock

mixed_mutual
datatype D (α : Type u)
  | leaf (a : α)
  | node (s : S α)
codatatype S (α : Type u)
  | cons (d : D α) (s : S α) (o : O α)
codatatype O (α : Type u)
  | none
  | some (d : D α)
end

#check @D.rec
#check @S.mem_cons

end InnerCoBlock

/-! ### 7. Inner runs with indices

An inner run may be a family: the open family gets its instances at every index, and the outer run
nests through it at the index of each field. Here infinite trees whose children are vectors of the
length the node says. -/

namespace InnerIdx

mixed_mutual
codatatype Tree (α : Type u)
  | node (a : α) (n : Nat) (cs : Vec α n)
datatype Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (t : Tree α) (f : Vec α n) : Vec α (n + 1)
end

#check @Vec.rec

def Vec.length {α : Type u} {n : Nat} (f : Vec α n) : Nat :=
  Vec.fold (S := fun _ => Nat) (fun _ y => match y with | .nil => 0 | .cons _ k => k + 1) f

theorem Vec.length_eq {α : Type u} {n : Nat} (f : Vec α n) : f.length = n := by
  induction f with
  | nil => simp [Vec.length]
  | cons t f ih => simp_all [Vec.length]

def Tree.bin {α : Type u} (a : α) : Tree α :=
  Tree.corec (S := Unit) (fun _ => .node a 2 (.cons () (.cons () .nil))) ()

theorem Tree.bin_eq {α : Type u} (a : α) :
    Tree.bin a = .node a 2 (.cons (.bin a) (.cons (.bin a) .nil)) := by
  conv_lhs => rw [← Tree.ctor_dtor (Tree.bin a), Tree.bin, Tree.dtor_corec]
  simp [Tree.bin]

end InnerIdx

-- The other order: finite trees through coinductive families of trees.
namespace InnerCoIdx

mixed_mutual
datatype Tree (α : Type u)
  | node (a : α) (n : Nat) (cs : Vec α n)
codatatype Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (t : Tree α) (f : Vec α n) : Vec α (n + 1)
end

#check @Tree.rec
#check @Vec.mem_cons

end InnerCoIdx

/-! ### 8. Parameters and section variables

The declarations share their parameters, names included, as in `mutual`; a parameter may be used in
one run only. The open types take one more, for the outer types, at a universe of its own. -/

namespace Params

mixed_mutual
codatatype Tree (α : Type u) (β : Type v)
  | node (a : α) (children : Forest α β)
datatype Forest (α : Type u) (β : Type v)
  | nil (b : β)
  | cons (t : Tree α β) (f : Forest α β)
end

#check @Forest.fold
#check Forest.Open

/-! A section variable that any declaration uses is a parameter of all of them, as with
`inductive`. -/

section

variable {γ : Type u}

mixed_mutual
datatype Box
  | mk (c : Stream)
codatatype Stream
  | cons (g : γ) (b : Box) (s : Stream)
end

end

#check @Box.mk
#check @Box.rec

/-! Implicit binders, in the constructors and among the parameters. As with `datatype`, an implicit
parameter is explicit in the types: `LabList ι f`. -/

mixed_mutual
codatatype Lab {ι : Type} (f : ι → Nat)
  | node {i : ι} (n : Fin (f i)) (cs : LabList f)
datatype LabList {ι : Type} (f : ι → Nat)
  | nil
  | cons (t : Lab f) (rest : LabList f)
end

#check @Lab.node

end Params

/-! ### 9. `simp` through the nesting

Two kinds of rules let `simp` see through the nesting. The membership rules `Forest.mem_cons`
compute `x ∈ c` on the constructors of the inner types, through all the runs between. The map rules
of the open types, `Forest.Open.Colean.Poly.map_cons` and the like, compute the map that the rules
of the outer run apply to their children (`Tree.dtor_corec`, `Tree.fold_node`); they are the reason
the unfoldings of sections 2 to 7 are a `simp` call. -/

namespace Classic

example {α : Type u} (s t : Tree α) : t ∈ Forest.cons s (.cons t .nil) := by simp

end Classic

namespace Runs

-- A process in the menu of a trace of an entry.
example {α : Type u} (p q : Proc α) (t : Trace α) :
    p ∈ Menu.cons q (.tick (.cons p t .nil) t) .nil := by
  simp

end Runs

namespace Other

-- The fold of the trees maps through the forest of children; `simp` computes it two levels down.
#check @Tree.fold_node

example {α : Type u} (a : α) (f : Forest α) :
    (Tree.node a (.cons (.node a (.cons (.node a .nil) .nil)) f)).leftDepth = 2 := by
  simp [Tree.leftDepth]

end Other

/-! ### 10. An outer type in a field with the recursion

A field `p : Tree α × Forest α` becomes `p : X × Forest.Open α X` in the open forests: the
parameter for the trees sits in the same field as the forests' own recursion. Step 5 splits such a
field through its products and sums (`NestingTour.lean`, section 9), so `X` varies, and the
membership of the trees is that of the components. -/

namespace Pair

mixed_mutual
codatatype Tree (α : Type u)
  | node (a : α) (children : Forest α)
datatype Forest (α : Type u)
  | nil
  | cons (p : Tree α × Forest α)
end

#check @Forest.mem_cons

/-- The tree with two copies of itself as children. -/
def Tree.bin {α : Type u} (a : α) : Tree α :=
  Tree.corec (S := Unit) (fun _ => .node a (.cons ((), .cons ((), .nil)))) ()

theorem Tree.bin_eq {α : Type u} (a : α) :
    Tree.bin a = .node a (.cons (.bin a, .cons (.bin a, .nil))) := by
  conv_lhs => rw [← Tree.ctor_dtor (Tree.bin a), Tree.bin, Tree.dtor_corec]
  simp [Tree.bin]

example {α : Type u} (s t : Tree α) : t ∈ Forest.cons (s, .cons (t, .nil)) := by simp

end Pair

/-! Inside a named type constructor the split stops: `List (Tree α × Forest α)` becomes
`List (X × Forest.Open α X)`, with positions of both kinds in one field. The field has an
occurrence structure in two variables (`NestingTour.lean`, section 9), so `X` varies here too,
and the membership of the trees is that of the pairs in the list. -/

namespace ListPair

mixed_mutual
codatatype Tree (α : Type u)
  | node (a : α) (children : Forest α)
datatype Forest (α : Type u)
  | nil
  | cons (p : List (Tree α × Forest α))
end

#check @Forest.mem_cons

/-- The tree with one copy of itself as its child. -/
def Tree.loop {α : Type u} (a : α) : Tree α :=
  Tree.corec (S := Unit) (fun _ => .node a (.cons [((), .nil)])) ()

theorem Tree.loop_eq {α : Type u} (a : α) : Tree.loop a = .node a (.cons [(.loop a, .nil)]) := by
  conv_lhs => rw [← Tree.ctor_dtor (Tree.loop a), Tree.loop, Tree.dtor_corec]
  simp [Tree.loop]

example {α : Type u} (s t : Tree α) : t ∈ Forest.cons [(s, .nil), (t, .nil)] := by simp

end ListPair

/-! Across a sum inside the named type constructor too: `List (Tree α ⊕ Forest α)` becomes
`List (X ⊕ Forest.Open α X)`, whose members in each variable `simp` computes through the sum
(`NestingTour.lean`, section 9). -/

namespace ListSum

mixed_mutual
codatatype Tree (α : Type u)
  | node (a : α) (children : Forest α)
datatype Forest (α : Type u)
  | nil
  | cons (p : List (Tree α ⊕ Forest α))
end

#check @Forest.mem_cons

example {α : Type u} (s t : Tree α) : t ∈ Forest.cons [.inl s, .inr (.cons [.inl t])] := by simp

end ListSum

/-! ### 11. A run that mentions a run two levels out, with a parameter

`C` mentions `A`, so `B`, between them, takes a parameter `X` for `A` and passes it on: its field
`c : C α` becomes `c : C.Open α X`, which mentions two parameters, `α` and `X`. Step 5 lets a field
mention several parameters, each at its premise (`NestingTour.lean`, section 5), and keeps the
first ones constant when they cannot vary with the others: only `X` needs to vary. The membership
instances of such a block are not the right ones, though (section 14). -/

namespace Distant

mixed_mutual
codatatype A (α : Type u)
  | mk (b : B α)
datatype B (α : Type u)
  | nil
  | cons (c : C α) (b : B α)
codatatype C (α : Type u)
  | mk (a : A α) (c : C α)
end

#check @B.cons
#check @C.mk

end Distant

-- `α` is a function domain in `C`: it is constant in `C.Open` and `B.Open`, and `X` still varies.
namespace DistantDomain

mixed_mutual
codatatype A (α : Type)
  | mk (b : B α)
datatype B (α : Type)
  | nil
  | cons (c : C α) (b : B α)
codatatype C (α : Type)
  | mk (a : α → A α) (c : C α)
end

end DistantDomain

/-! ## Part II: what does not work yet

What should stay refused is not listed: the declarations share their parameters and universe, as
in `mutual`, a plain `mutual` block does not mix kinds, and the names a block declares must be
free, its internal ones (`Forest.Open`) included, which is checked before anything is declared.

The outer runs nest through the open types of the runs inside by the instances generated for them
(`NestingTour.lean`, section 4), in the parameter for the outer types. The blocks below need
instances that are not generated, and stop with the error for the run inside; nothing is
declared. -/

/-! ### 12. An outer run with indices, or an outer block

When the outer run is a family or a block, the open type's parameter for it is a family too, over
the run's index. Nesting through a functor on families needs `IPolyIso` instances, which are not
generated yet; generating them, as `PolyIso` is generated, would make both blocks work. -/

namespace OuterIdx

mixed_mutual
codatatype VTree (α : Type u) : Nat → Type u
  | node {n : Nat} (a : α) (children : VForest α n) : VTree α n
datatype VForest (α : Type u) : Nat → Type u
  | nil : VForest α 0
  | cons {n : Nat} (t : VTree α n) (f : VForest α n) : VForest α (n + 1)
end

end OuterIdx

namespace OuterBlock

mixed_mutual
codatatype Tree (α : Type u)
  | node (a : α) (children : Forest α)
codatatype Str (α : Type u)
  | cons (hd : Tree α) (tl : Str α)
datatype Forest (α : Type u)
  | nil
  | cons (t : Tree α) (s : Str α) (f : Forest α)
end

end OuterBlock

/-! ## Part III: what looks like a bug

Each of these either deserves a clear error or should simply work. -/

/-! ### 13. Internal names that show

A constructor named `Open` in an inner run was lost without a word: its name is that of the open
type, `Ival.Open`, so the closed constructor was never declared. The command now refuses the name
before declaring anything, as it refuses every constructor named like a generated declaration. -/

namespace CtorOpen

/--
error: constructor `Open` clashes with the generated declaration `MixedTour.CtorOpen.Ival.Open`; rename the constructor
-/
#guard_msgs in
mixed_mutual
codatatype Tree
  | node (cs : Ival)
datatype Ival
  | Open (t : Tree)
  | Closed
end

end CtorOpen

/-! ### 14. Membership with a run two levels out

The block of section 11 is accepted, here without its parameter. Its membership instances are
not the right ones. They are generated for the runs that reach a run inside, here `B` in `C`, while what
`C` holds are the members of the runs it takes a parameter for, here `A`. So `B` in `C` is always
false (`C.mem_mk`, with `False` on the right), and there is no instance for `A` in `C`: `B.mem_cons`
falls back to `PolyIso.Mem C.Open`. -/

namespace DistantMem

mixed_mutual
codatatype A
  | mk (b : B)
datatype B
  | nil
  | cons (c : C) (b : B)
codatatype C
  | mk (a : A) (c : C)
end

#check @B.mem_cons
#check @C.mem_mk

end DistantMem

end

end MixedTour
