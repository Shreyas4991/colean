import Colean.MutualCmd

/-!
# A walk through mutual blocks

A uniform block is a `mutual … end` of `data` declarations, or of `codata` declarations, with the
same parameters. It is one family over an inductive `Ix`, with a constructor per type whose
arguments are the indices of that type, so nothing new is involved: `Even`/`Odd` is one `data`
with one index. Blocks that mix both kinds, `mixed_mutual … end`, are in `Sketch/MixedTour.lean`.

Read it top to bottom. Part I (sections 1 to 7) is what works, Part II what does not work yet but
could, and Part III what looks like a bug; there is nothing in either at the moment.

Nesting is left out on purpose. Fields here are plain members, constants or functions into
members; `×`, `⊕`, `List` and other leaves are not used. Blocks with nesting are in
`Sketch/NestingTour.lean`: what works in section 6, what does not in sections 11 and 12.

How the file is checked:

* an example without an error on it works;
* failures are left as they are, so they show as errors in the infoview;
* a failed block declares nothing of its types, and every example has a namespace of its own, so
  names do not clash.
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
#check @Even_Odd.rec_Even_succ

-- Per type: constructors, case analysis, the fold, the recursor, the computation rules,
-- disjointness.
#check @Even.zero
#check @Even.succ
#check @Odd.succ
#check @Even.casesOn
#check @Even.fold
#check @Even.rec
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

/-- Induction over the block, with a motive over `Ix`: the statement for one type comes by
restricting. Induction per type, with a motive per type, is section 7. -/
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

-- A result index that is not a pattern, `!b`, as `inductive` accepts. The generated proofs never
-- invert it. Case analysis on a value at such an index (`p : Pa (!b)`) cannot, as with
-- `inductive`; at a variable index it can.
namespace ResultIndex

mutual
data Pa : Bool → Type
  | nil : Pa true
  | mk {b : Bool} (q : Qa b) : Pa (!b)
data Qa : Bool → Type
  | mk {b : Bool} (p : Pa b) : Qa b
end

def Pa.len {b : Bool} (p : Pa b) : Nat :=
  Pa.rec (motive_2 := fun _ _ => Nat) 0 (fun _ k => k + 1) (fun _ k => k + 1) p

example {b : Bool} (q : Qa b) : (Pa.mk q).len = Qa.rec (motive_1 := fun _ _ => Nat) 0
    (fun _ k => k + 1) (fun _ k => k + 1) q + 1 := by
  rw [Pa.len, Pa.rec_mk]

example {b : Bool} (p : Pa b) : p.len = 0 → b = true := by
  cases p with
  | nil => intro; rfl
  | mk q => simp [Pa.len]

end ResultIndex

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

/-! ### 6. Spellings and names

Each of these failed until the generators moved to `Expr`. -/

-- A constructor given by its type, with arrows instead of named fields.
namespace Arrow

mutual
data Pa
  | mk : Pa
data Qa
  | mk : Pa → Qa
end

#check @Qa.mk

end Arrow

-- An implicit parameter given by name at an occurrence. Leaving it out is refused, as by Lean's
-- `inductive`.
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

-- Types named like what the block generates: `B`, `F`, `Shape`, `Ix` and `S`.
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

-- A constructor named like its type, which `inductive` accepts. A linter warns about the name, as
-- it does for `inductive`, so it is turned off here.
namespace CtorName

set_option linter.dupNamespace false in
mutual
data Pa
  | Pa (q : Qa)
  | nil
data Qa
  | Qa (p : Pa)
end

#check @Pa.Pa

end CtorName

/-! ### 7. Recursors per type

Each type of a `data` block has its recursor in the shape of Lean's mutual inductives: a motive
per type (`motive_1`, `motive_2` in block order), the minor premises of every constructor of the
block, with the block's names for shared ones, and the type's own indices. `induction … using`
takes it, the other motives given by name. As with Lean, plain `induction` on a value of one type
does not apply: it takes the value apart as the subtype it is. The rules `Tₘ.rec_cᵢ` are simp
lemmas; those of the block-level recursor are `Blk.rec_cᵢ`. -/

namespace PerType

mutual
data Pa
  | nil
  | mk (q : Qa)
data Qa
  | mk (p : Pa)
end

#check @Pa.rec
#check @Pa.rec_mk
#check @Pa_Qa.rec_Pa_mk

example (p : Pa) : True := by
  induction p using Pa.rec (motive_2 := fun _ => True) with
  | nil => trivial
  | Pa_mk q ih => trivial
  | Qa_mk p ih => trivial

-- With indices: parity as in section 4, without a motive over the block.
example {n : Nat} (e : Indexed.Even n) : n % 2 = 0 := by
  induction e using Indexed.Even.rec (motive_2 := fun n _ => n % 2 = 1) with
  | zero => rfl
  | Even_succ o ih => omega
  | Odd_succ e ih => omega

-- A function by the recursor of one type, computed by the rules.
def Pa.depth (p : Pa) : Nat :=
  Pa.rec (motive_2 := fun _ => Nat) 0 (fun _ k => k + 1) (fun _ k => k + 1) p

example : (Pa.mk (.mk .nil)).depth = 2 := by simp [Pa.depth]

end PerType

/-! The hypothesis of a nested argument is by membership, at the motive of the type of its
members: `∀ t, PolyIso.Mem (fun X => List X) t fs → motive_2 t` for a list of forests. When the
positions of an argument are at several types of the block, through a product or a sum, it is
by `IPolyIso.Mem` at the block's index, one hypothesis per type of the argument. -/

namespace NestedPerType

mutual
data Tr
  | node (n : Nat) (fs : List Fo)
data Fo
  | mk (t : Tr) (next : Option Fo)
end

/--
info: @Tr.rec : {motive_1 : Tr → Sort u_1} →
  {motive_2 : Fo → Sort u_1} →
    ((n : ℕ) →
        (fs : List Fo) → ((t : Fo) → PolyIso.Mem (fun X => List X) t fs → motive_2 t) → motive_1 (Tr.node n fs)) →
      ((t : Tr) →
          (next : Option Fo) →
            motive_1 t → ((t : Fo) → PolyIso.Mem (fun X => Option X) t next → motive_2 t) → motive_2 (Fo.mk t next)) →
        (t : Tr) → motive_1 t
-/
#guard_msgs in
#check @Tr.rec

-- The sum of the labels, by the recursors; `List.attach` gives the members of the list with
-- their memberships.
def Tr.sum : Tr → Nat :=
  Tr.rec (motive_2 := fun _ => Nat)
    (fun n fs ih => n + (fs.attach.map fun x => ih x.1 ((PolyIso.mem_list _ _).mpr x.2)).sum)
    (fun _ next t ih =>
      t + (next.attach.map fun x => ih x.1 ((PolyIso.mem_option _ _).mpr x.2)).getD 0)

example : (Tr.node 1 [.mk (.node 2 []) none]).sum = 3 := by
  simp [Tr.sum, List.map_attach_eq_pmap]

end NestedPerType

/-! Blocks that mix `data` and `codata`, `mixed_mutual … end`, are in `Sketch/MixedTour.lean`. -/

/-! ## Part II: what does not work yet

Nothing at the moment. What should stay refused is not listed: the types of a block share their
parameters, names included, and their universe, as in Lean, a universe written must be the one of
the block's encoding (so not `Prop`), an implicit parameter cannot be left out at an occurrence,
as in Lean, and a `mutual` block is all `data` or all `codata`. -/

/-! ## Part III: what looks like a bug

Nothing at the moment. The two that were here are clear errors now, given before the types are
declared: a block whose name, made of its types' names, is taken, and a declared sort `Prop`,
which was ignored without a word. -/

end

end MutualTour
