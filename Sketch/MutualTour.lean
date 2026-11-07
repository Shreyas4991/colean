import Colean.MutualCmd

/-!
# A walk through uniform blocks

A uniform block is a `mutual … end` of `data` declarations, or of `codata` declarations, with the
same parameters. It is one family over an inductive `Ix`, with a constructor per type whose
arguments are the indices of that type, so nothing new is involved: `Even`/`Odd` is one `data`
with one index.

Read it top to bottom. Part I (sections 1 to 5) is what works, Part II (sections 6 and 7) what is
refused with a clear message, Part III (section 8) what looks like a bug, and Part IV (section 9)
`mixed_mutual` blocks that need no nesting.

Nesting is left out on purpose. Fields here are plain members, constants or functions into
members; `×`, `⊕`, `List` and other leaves are not used. The failures with those, and the cyclic
`mixed_mutual` blocks, are in `Sketch/NestingTour.lean` (sections 14 and 16).

How the file is checked:

* an example without an error on it works;
* failures are left as they are, so they show as errors in the infoview;
* Part III reports many errors per declaration: the first one is the real one, the others follow
  from it, and the broken declarations stay, so every example has a namespace of its own.
-/

universe u v

namespace MutualTour

noncomputable section

open Codata

/-! ## Part I: what works -/

/-! ### 1. The smallest block, and what it declares

The block is named after its types, joined by `_`. Each type is that family at one constructor
of `Ix`, and keeps its own constructors. -/

namespace Basic

mutual
data Even
  | zero
  | succ (o : Odd)
data Odd
  | succ (e : Even)
end

-- The block: one family over `Ix`, with its functor and the contract of a single type.
#check @Even_Odd
#check @Even_Odd.Ix.Even
#check @Even_Odd.F
#check @Even_Odd.ctor
#check @Even_Odd.fold
#check @Even_Odd.fold_ctor
#check @Even_Odd.rec

-- Per type: constructors, case analysis, the fold, the computation rules, disjointness.
#check @Even.zero
#check @Even.succ
#check @Odd.succ
#check @Even.casesOn
#check @Even.fold
#check @Even.fold_succ
#check @Even.rec_succ
#check @Even.succ_ne_zero

-- `succ` is in both types, so the block's functor qualifies it. The types keep the plain name.
#check @Even_Odd.F.Even_succ
#check @Even_Odd.F.Odd_succ

end Basic

/-! ### 2. `data`: folds and induction

One algebra serves the whole block: it says what to do at every constructor of `Ix`. `T.fold` restricts it to
a type. -/

namespace Finite

mutual
data Rose (α : Type u)
  | node (a : α) (children : Forest α)
data Forest (α : Type u)
  | nil
  | cons (t : Rose α) (f : Forest α)
end

def sizeAlg {α : Type u} : ∀ m, Rose_Forest.F α (fun _ => Nat) m → Nat
  | .Rose, .node _ n => n + 1
  | .Forest, .nil => 0
  | .Forest, .cons n k => n + k

def Rose.size {α : Type u} (t : Rose α) : Nat := Rose.fold sizeAlg t
def Forest.size {α : Type u} (f : Forest α) : Nat := Forest.fold sizeAlg f

@[simp] theorem Rose.size_node {α : Type u} (a : α) (c : Forest α) :
    (Rose.node a c).size = c.size + 1 := by
  simp [Rose.size, Forest.size, sizeAlg]

@[simp] theorem Forest.size_nil {α : Type u} : (Forest.nil : Forest α).size = 0 := by
  simp [Forest.size, sizeAlg]

@[simp] theorem Forest.size_cons {α : Type u} (t : Rose α) (f : Forest α) :
    (Forest.cons t f).size = t.size + f.size := by
  simp [Rose.size, Forest.size, sizeAlg]

/-- Induction is over the block, with a motive over `Ix`. As with Lean's mutual inductives, the
statement for one type comes by restricting. -/
def Pos {α : Type u} : ∀ m, Rose_Forest α m → Prop
  | .Rose, t => 0 < Rose.size t
  | .Forest, _ => True

theorem pos {α : Type u} (m : Rose_Forest.Ix α) (x : Rose_Forest α m) : Pos m x := by
  induction x with
  | node a c ih => simp [Pos]
  | nil => simp [Pos]
  | cons t f iht ihf => simp [Pos]

theorem Rose.size_pos {α : Type u} (t : Rose α) : 0 < t.size := pos .Rose t

/-- Case analysis is per type, with only the constructors of that type. -/
example {α : Type u} (f : Forest α) : f = .nil ∨ ∃ t g, f = .cons t g := by
  cases f with
  | nil => exact Or.inl rfl
  | cons t g => exact Or.inr ⟨t, g, rfl⟩

end Finite

/-! ### 3. `codata`: corecursion and bisimulation

A state is a family over `Ix`, and one coalgebra serves the block. -/

namespace Infinite

mutual
codata Tree (α : Type u)
  | node (a : α) (children : Forest α)
codata Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

def fullCoalg {α : Type u} (a : α) : ∀ m, Unit → Tree_Forest.F α (fun _ => Unit) m
  | .Tree, _ => .node a ()
  | .Forest, _ => .cons () ()

def Tree.full {α : Type u} (a : α) : Tree α := Tree.corec (fullCoalg a) ()
def Forest.full {α : Type u} (a : α) : Forest α := Forest.corec (fullCoalg a) ()

@[simp] theorem Tree.dtor_full {α : Type u} (a : α) :
    (Tree.full a).dtor = .node a (Forest.full a) := by
  simp [Tree.full, Forest.full, Tree_Forest.dtor_corec, fullCoalg]

/-- The unfolding equation, through `ctor_dtor`. -/
theorem Tree.full_eq {α : Type u} (a : α) : Tree.full a = Tree.node a (Forest.full a) := by
  conv => lhs; rw [← Tree_Forest.ctor_dtor (Tree.full a), Tree.dtor_full]
  rfl

def natCoalg {α : Type u} (a : α) : ∀ m, Nat → Tree_Forest.F α (fun _ => Nat) m
  | .Tree, k => .node a (k + 1)
  | .Forest, k => .cons (k + 1) (k + 1)

/-- Bisimulation over the block: the relation is a family over `Ix` too, and the proof looks at
each type in turn. -/
example {α : Type u} (a : α) (n : Nat) : Tree.full a = Tree.corec (natCoalg a) n := by
  refine Tree_Forest.bisim (fun _ x y => x = Tree_Forest.corec (fullCoalg a) () ∧
    ∃ k, y = Tree_Forest.corec (natCoalg a) k) ?_ ⟨rfl, n, rfl⟩
  rintro m _ _ ⟨rfl, k, rfl⟩
  cases m
  · simp only [Tree_Forest.dtor_corec, fullCoalg, natCoalg, Tree_Forest.F.map_node]
    exact .node _ _ _ ⟨rfl, _, rfl⟩
  · simp only [Tree_Forest.dtor_corec, fullCoalg, natCoalg, Tree_Forest.F.map_cons]
    exact .cons _ _ _ _ ⟨rfl, _, rfl⟩ ⟨rfl, _, rfl⟩

end Infinite

/-! ### 4. Indices

The indices of a type are the arguments of its constructor of `Ix`, so a pattern over the block
matches the type and its indices at once. -/

namespace Indexed

mutual
data Even : Nat → Type
  | zero : Even 0
  | succ {n : Nat} (o : Odd n) : Even (n + 1)
data Odd : Nat → Type
  | succ {n : Nat} (e : Even n) : Odd (n + 1)
end

-- Case analysis refines the index.
example (o : Odd 0) : False := by cases o

example (e : Even 0) : e = Even.zero := by
  cases e with
  | zero => rfl

def Par : ∀ i, Even_Odd i → Prop
  | .Even n, _ => n % 2 = 0
  | .Odd n, _ => n % 2 = 1

theorem par (i : Even_Odd.Ix) (x : Even_Odd i) : Par i x := by
  induction x with
  | zero => simp [Par]
  | Even_succ o ih => simp [Par] at *; omega
  | Odd_succ e ih => simp [Par] at *; omega

end Indexed

-- `codata`, with the index growing along a field.
namespace IndexedCo

mutual
codata Pa : Nat → Type
  | mk {n : Nat} (q : Qa (n + 1)) : Pa n
codata Qa : Nat → Type
  | stop : Qa 0
  | mk {n : Nat} (p : Pa n) : Qa n
end

#check @Pa_Qa.corec
#check @Pa_Qa.bisim

end IndexedCo

-- A parameter together with an index.
namespace ParamIndex

mutual
data Ev (α : Type u) : Nat → Type u
  | zero : Ev α 0
  | succ {n : Nat} (a : α) (o : Od α n) : Ev α (n + 1)
data Od (α : Type u) : Nat → Type u
  | succ {n : Nat} (a : α) (e : Ev α n) : Od α (n + 1)
end

end ParamIndex

-- An index type that depends on a parameter.
namespace IndexOnParam

mutual
data Pa (α : Type) : List α → Type
  | nil : Pa α []
  | mk {a : α} {l : List α} (q : Qa α l) : Pa α (a :: l)
data Qa (α : Type) : List α → Type
  | mk {l : List α} (p : Pa α l) : Qa α l
end

end IndexOnParam

-- A later index that depends on an earlier one.
namespace Telescope

mutual
data Pa : (n : Nat) → Fin n → Type
  | mk {n : Nat} (i : Fin n) (q : Qa n i) : Pa n i
data Qa : (n : Nat) → Fin n → Type
  | stop {n : Nat} (i : Fin n) : Qa n i
  | mk {n : Nat} (i : Fin n) (p : Pa n i) : Qa n i
end

end Telescope

-- Types as indices: a parameter that varies, at a universe's cost.
namespace TypeIndex

mutual
data Pa : Type → Type 1
  | nil {α : Type} : Pa α
  | mk {α : Type} (q : Qa (α × α)) : Pa α
data Qa : Type → Type 1
  | mk {α : Type} (a : α) (p : Pa α) : Qa α
end

end TypeIndex

-- An index given by an explicit binder.
namespace ExplicitIndex

mutual
data Pa : Nat → Type
  | mk (n : Nat) (q : Qa n) : Pa n
  | nil (n : Nat) : Pa n
data Qa : Nat → Type
  | mk (n : Nat) (p : Pa n) : Qa n
end

#check @Pa_Qa.rec

end ExplicitIndex

-- Different indices: each type has its own.
namespace Indices

mutual
data Pa : Nat → Type
  | nil : Pa 0
  | mk {n : Nat} (q : Qa true) : Pa (n + 1)
data Qa : Bool → Type
  | mk (p : Pa 3) : Qa true
end

#check @Pa_Qa.Ix.Pa
#check @Pa_Qa.rec

example (q : Qa false) : False := by cases q

end Indices

-- One type indexed and the other not.
namespace OneIndexed

mutual
data Pa : Nat → Type
  | nil : Pa 0
  | mk {n : Nat} (q : Qa) : Pa (n + 1)
data Qa
  | mk (p : Pa 3)
end

end OneIndexed

-- No index, one, and two that depend on each other, with a parameter in the index.
namespace ManyIndices

mutual
codata Pa (α : Type u) : List α → Type u
  | nil (l : List α) (q : Qa α) : Pa α l
codata Qa (α : Type u)
  | mk (r : Ra α 2 1)
codata Ra (α : Type u) : (n : Nat) → Fin n → Type u
  | go {n : Nat} {i : Fin n} (l : List α) (p : Pa α l) : Ra α n i
end

#check @Pa_Qa_Ra.corec
#check @Ra.bisim

end ManyIndices

-- Indices are not compared, so the spelling does not matter, nor does a missing sort.
namespace Spelling

mutual
data Pa : Nat → Type
  | nil : Pa 0
  | mk {n : Nat} (q : Qa n) : Pa (n + 1)
data Qa : (k : ℕ) → Type
  | mk {n : Nat} (p : Pa n) : Qa n
end

mutual
data Ra : Type
  | nil
  | mk (s : Sa)
data Sa
  | mk (r : Ra)
end

end Spelling

/-! ### 5. Shapes of blocks and of fields -/

-- One type: a block all the same, and it comes out as a plain `data`.
namespace One

mutual
data Solo
  | nil
  | mk (s : Solo)
end

#check @Solo.fold

end One

-- A type that nobody mentions, and one without constructors.
namespace Loose

mutual
data Pa
  | nil
  | mk (p : Pa)
data Qa
  | one
end

mutual
data Ra
  | mk (s : Sa)
data Sa
end

end Loose

-- Three types in a cycle, and a type mentioning itself as well as others.
namespace Cycle

mutual
codata X1
  | mk (y : X2)
codata X2
  | mk (z : X3)
codata X3
  | stop
  | mk (x : X1)
end

mutual
data Pa
  | nil
  | self (a : Pa) (b : Qa)
data Qa
  | mk (a : Pa) (b : Qa)
end

end Cycle

-- Functions into members, the own type included, and dependent ones.
namespace Functions

mutual
data Pa
  | nil
  | fn (k : Nat → Pa)
  | dep (n : Nat) (h : 0 < n) (k : Fin n → Qa)
data Qa
  | mk (p : Pa)
end

mutual
codata Ra : Nat → Type
  | mk {n : Nat} (k : (m : Nat) → Sa (n + m)) : Ra n
codata Sa : Nat → Type
  | mk {n : Nat} (r : Ra n) : Sa n
end

end Functions

-- Binders named like the generator's own variables.
namespace Binders

mutual
data Pa
  | nil
  | mk (m : Nat) (X : Nat) (i : Nat) (f : Qa)
data Qa
  | mk (s : Pa) (y : Nat)
end

end Binders

-- Dotted type names.
namespace Dotted

mutual
data Foo.Pa
  | nil
  | mk (q : Foo.Qa)
data Foo.Qa
  | mk (p : Foo.Pa)
end

#check @Foo.Pa.mk

end Dotted

/-! ## Part II: what is refused, with a clear message

Each of these could be lifted. What should stay refused is not listed: the types of a block share
their parameters, names included, and their universe, as in Lean, and a `mutual` block is all
`data` or all `codata`. -/

/-! ### 6. Spellings the commands do not take

These are the same for a single type. -/

-- A constructor must name its fields: an arrow type is not read.
namespace Arrow

mutual
data Pa
  | mk : Pa
data Qa
  | mk : Pa → Qa
end

end Arrow

-- An implicit parameter cannot be left out at an occurrence, and it cannot be given by name.
namespace ImplicitParam

mutual
data Pa {α : Type u} (β : Type v)
  | nil
  | mk (b : β) (q : Qa β)
data Qa {α : Type u} (β : Type v)
  | mk (p : Pa β)
end

end ImplicitParam

namespace NamedParam

mutual
data Pa {α : Type u} (β : Type v)
  | nil
  | mk (a : α) (b : β) (q : Qa (α := α) β)
data Qa {α : Type u} (β : Type v)
  | mk (p : Pa (α := α) β)
end

end NamedParam

-- An instance binder among the parameters.
namespace InstParam

mutual
data Pa (α : Type u) [Inhabited α]
  | nil
  | mk (q : Qa α)
data Qa (α : Type u) [Inhabited α]
  | mk (p : Pa α)
end

end InstParam

/-! ### 7. Recursors per type

`fold` and `corec` have aliases per type, the recursor does not, and `induction` does not reach
the block from a value of one type. The way that works is section 2. -/

namespace PerType

mutual
data Pa
  | nil
  | mk (q : Qa)
data Qa
  | mk (p : Pa)
end

#check @Pa.rec

example (p : Pa) : True := by
  induction p with
  | nil => trivial
  | mk q ih => trivial

end PerType

/-! ## Part III: what looks like a bug

Each of these either deserves a clear error or should simply work, and instead the generators fail
with a flood of errors, or say nothing at all. -/

/-! ### 8. Failures inside the generators -/

/-! Types of a block named like what the block generates: `B`, `F`, `Shape`, `Ix` and `S`. A
single type is protected from this, its generated name gets a prime (`ColeanTest/Names.lean`), but
a block is not. -/

namespace NameB

mutual
data B
  | nil
  | mk (q : Qa)
data Qa
  | mk (b : B)
end

end NameB

namespace NameF

mutual
data F
  | nil
  | mk (q : Qa)
data Qa
  | mk (f : F)
end

end NameF

namespace NameShape

mutual
data Shape
  | nil
  | mk (q : Qa)
data Qa
  | mk (s : Shape)
end

end NameShape

namespace NameIx

mutual
data Ix
  | nil
  | mk (q : Qa)
data Qa
  | mk (w : Ix)
end

end NameIx

namespace NameS

mutual
data S
  | nil
  | mk (q : Qa)
data Qa
  | mk (s : S)
end

end NameS

/-! The name of the block is taken. It is a name the user never wrote, and it deserves a clear
error at least. -/

namespace BlockName

def Pa_Qa := Nat

mutual
data Pa
  | nil
  | mk (q : Qa)
data Qa
  | mk (p : Pa)
end

end BlockName

/-! A constructor named like its type, which `inductive` accepts. A single type fails likewise. -/

namespace CtorName

mutual
data Pa
  | Pa (q : Qa)
  | nil
data Qa
  | Qa (p : Pa)
end

end CtorName

/-! A result index that the pattern matcher cannot invert. `!b` is a function of `b`, and the
generated proofs do a `cases` on the index. A single type fails likewise. -/

namespace ResultIndex

mutual
data Pa : Bool → Type
  | nil : Pa true
  | mk {b : Bool} (q : Qa b) : Pa (!b)
data Qa : Bool → Type
  | mk {b : Bool} (p : Pa b) : Qa b
end

end ResultIndex

/-! A declared sort of `Prop` is ignored without a word: both types are in `Type`. A single type
behaves the same. -/

namespace PropSort

mutual
data Pa : Prop
  | nil
  | mk (q : Qa)
data Qa : Prop
  | mk (p : Pa)
end

#check Pa

end PropSort

/-! ## Part IV: `mixed_mutual` without nesting

A mixed block is a nested fixpoint, and the textual order is the nesting order, the first
declaration outermost. A cycle between `data` and `codata` needs nesting, so it is in
`Sketch/NestingTour.lean`, section 14. Without a cycle the block passes. -/

/-! ### 9. Blocks without a cycle

An inner type mentioning an outer one takes it as a parameter `X`. So it is not closed:
`Inner α X`, to be used at `Inner α (Outer α)`. Neighbours of one kind form one uniform block. -/

namespace MixedInner

mixed_mutual
codata Ou (α : Type u)
  | mk (a : α) (o : Ou α)
data In₁ (α : Type u)
  | nil
  | cons (o : Ou α) (i : In₂ α)
data In₂ (α : Type u)
  | mk (i : In₁ α)
end

#check @In₁.cons
#check @Ou.mk

end MixedInner

-- The outer type mentions the inner one, which does not mention it back: a plain field.
namespace MixedOuter

mixed_mutual
data Ou (α : Type u)
  | nil
  | mk (s : In α) (o : Ou α)
codata In (α : Type u)
  | mk (a : α) (i : In α)
end

#check @Ou.mk

end MixedOuter

-- Indices may differ, between kinds and within a kind.
namespace MixedIndices

mixed_mutual
codata Ou : Nat → Type
  | mk {n : Nat} (o : Ou (n + 1)) : Ou n
data In : Bool → Type
  | nil : In true
  | cons {b : Bool} (i : In b) : In b
end

#check @In.cons

mixed_mutual
codata Ou₂ (α : Type u)
  | mk (a : α) (o : Ou₂ α)
data In₁ (α : Type u) : Nat → Type _
  | nil : In₁ α 0
  | cons {n : Nat} (o : Ou₂ α) (i : In₂ α) : In₁ α (n + 1)
data In₂ (α : Type u)
  | mk (i : In₁ α 3)
end

#check @In₁.cons

end MixedIndices

-- A block outside: the family parameter of the inner type is over its `Ix`.
namespace MixedOuterBlock

mixed_mutual
codata O₁ (α : Type u)
  | mk (a : α) (o : O₂ α)
codata O₂ (α : Type u)
  | mk (o : O₁ α)
data In (α : Type u)
  | nil
  | cons (o : O₁ α) (i : In α)
end

#check @In.cons

end MixedOuterBlock

-- A block of one kind passes, with a warning that it is a plain `mutual`.
namespace MixedOneKind

mixed_mutual
data Pa
  | nil
  | mk (q : Qa)
data Qa
  | mk (p : Pa)
end

end MixedOneKind

end

end MutualTour
