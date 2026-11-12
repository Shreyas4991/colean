# Colean

Coinductive types for Lean 4, and inductive ones with more freedom than `inductive` allows.

Lean has no coinductive types. Colean adds a `codata` command that declares them, and a `data`
command for inductive types that `inductive` rejects, such as types nested through a
coinductive type. You write a declaration that looks like an `inductive` one, and you get a
type with its constructors, its eliminators and their lemmas:

- for `codata`: the destructor `dtor`, primitive corecursion `corec`, coinduction `bisim`, and
  case analysis `casesOn` (also through the `cases` tactic);
- for `data`: the recursor `rec` (also through the `induction` tactic), `fold`, and `casesOn`;
- for both: injectivity and disjointness of the constructors, as `simp` lemmas.

It covers parameters, indexed families, `mutual` blocks of one kind, nesting through other
types (`List`, `Option`, `Array`, products, sums, functions, dependent pairs, your own
types), and, as best effort, `mixed_mutual` blocks of `data` and `codata` types. An opt-in
attribute gives a `codata` type an order for Lean's `partial_fixpoint`, so you can write
corecursive definitions directly.

The types are definitions in Lean's logic, not axioms: everything is checked by the kernel and
uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Installation

Colean builds with Lean `v4.34.1` and depends on Mathlib. In your `lakefile.toml`:

```toml
[[require]]
name = "Colean"
git = "https://github.com/vasnesterov/colean"
rev = "main"
```

Then `import Colean`.

## Examples

The examples below assume `import Colean`, `noncomputable section` and `universe u`. Every
generated declaration is noncomputable, so are the definitions using them. They are checked
in [`ColeanTest/Readme.lean`](ColeanTest/Readme.lean).

### Streams: corecursion and coinduction

```lean
codata Strm (α : Type u)
  | cons (head : α) (tail : Strm α)

/-- `a, f a, f (f a), …`: the state is the next element. -/
def Strm.iterate {α : Type u} (f : α → α) (a : α) : Strm α :=
  Strm.corec (fun x => .cons x (f x)) a

def Strm.map {α β : Type u} (f : α → β) : Strm α → Strm β :=
  Strm.corec fun s => match s.dtor with | .cons a t => .cons (f a) t

@[simp] theorem Strm.dtor_iterate {α : Type u} (f : α → α) (a : α) :
    (Strm.iterate f a).dtor = .cons a (Strm.iterate f (f a)) := by
  simp [Strm.iterate, Strm.dtor_corec]

@[simp] theorem Strm.map_cons {α β : Type u} (f : α → β) (a : α) (s : Strm α) :
    (Strm.cons a s).map f = .cons (f a) (s.map f) := by
  rw [← Strm.ctor_dtor (Strm.map f _), Strm.map, Strm.dtor_corec]
  simp

/-- By coinduction: relate the two sides at every `b`, and show one step. -/
theorem Strm.map_iterate {α : Type u} (f : α → α) (a : α) :
    (Strm.iterate f a).map f = Strm.iterate f (f a) := by
  refine Strm.bisim (fun x y => ∃ b, x = (Strm.iterate f b).map f ∧
    y = Strm.iterate f (f b)) ?_ ⟨a, rfl, rfl⟩
  rintro _ _ ⟨b, rfl, rfl⟩
  rw [← Strm.ctor_dtor (Strm.iterate f b)]
  simp only [Strm.dtor_iterate, Strm.ctor_cons, Strm.map_cons, Strm.dtor_cons]
  exact .cons _ _ _ ⟨f b, rfl, rfl⟩
```

The corecursion step returns one layer, a value of the functor `Strm.F α S` over the states, so
its constructors are those of `Strm.F` (`.cons x (f x)`). The coinduction step shows that
related streams unfold to the same constructor with related tails, which is the relation
`Strm.F.Rel` and its constructor `.cons`.

### Indexed families

```lean
data Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

def Vec.toList {α : Type u} {n : Nat} (v : Vec α n) : List α :=
  Vec.rec (motive := fun _ _ => List α) [] (fun a _ l => a :: l) v

theorem Vec.length_toList {α : Type u} {n : Nat} (v : Vec α n) : v.toList.length = n := by
  induction v with
  | nil => simp [Vec.toList]
  | cons a v ih => simp_all [Vec.toList]

example {α : Type u} (v : Vec α 0) : v = .nil := by
  cases v with
  | nil => rfl
```

Indices may be anything, also when they depend on the constructor's arguments
(`Vec α (n + 1)`), and `codata` families work the same way.

### Mutual blocks

```lean
mutual
data Tree
  | node (n : Nat) (cs : Forest)
data Forest
  | nil
  | cons (t : Tree) (f : Forest)
end

def Tree.size (t : Tree) : Nat :=
  Tree.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ _ k => k + 1) 0 (fun _ _ a b => a + b) t

theorem Tree.size_pos (t : Tree) : 0 < t.size := by
  induction t using Tree.rec (motive_2 := fun _ => True) with
  | node n cs ih => simp [Tree.size]
  | nil => trivial
  | cons t f iht ihf => trivial
```

The recursors per type have the shape of Lean's mutual recursors, a motive per type. A
`mutual` block of `codata` types works the same way, with `corec` and `bisim` over the whole
block.

### Nesting

```lean
data Rose (α : Type u)
  | node (a : α) (cs : List (Rose α))

def Rose.size {α : Type u} (t : Rose α) : Nat :=
  Rose.fold (S := Nat) (fun | .node _ cs => cs.sum + 1) t

def Rose.labels {α : Type u} (t : Rose α) : List α :=
  Rose.fold (S := List α) (fun | .node a ls => a :: ls.flatten) t

@[simp] theorem Rose.size_node {α : Type u} (a : α) (cs : List (Rose α)) :
    (Rose.node a cs).size = (cs.map Rose.size).sum + 1 := by
  simp [Rose.size, Rose.fold_node]; rfl

@[simp] theorem Rose.labels_node {α : Type u} (a : α) (cs : List (Rose α)) :
    (Rose.node a cs).labels = a :: (cs.map Rose.labels).flatten := by
  simp [Rose.labels, Rose.fold_node]; rfl

/-- The induction hypothesis holds at every member of the list of children. -/
theorem Rose.length_labels {α : Type u} (t : Rose α) : t.labels.length = t.size := by
  induction t with
  | node a cs ih =>
    simp only [Codata.PolyIso.mem_list] at ih
    simp [List.length_flatten, Function.comp_def, List.map_congr_left ih]
```

A type can be nested through `List`, `Option`, `Array`, products, sums, functions, dependent
pairs, any type declared with `data` or `codata` (also families and types of a block), and your
own types, given instances that present them as polynomial functors (`Codata.PolyIso`). The
induction hypothesis of a nested argument is stated for its members, which `simp` turns into
the container's own membership (`t ∈ cs` for a list).

### Mixed blocks: infinite trees with finite forests

```lean
mixed_mutual
codata Tree (α : Type u)
  | node (a : α) (children : Forest α)
data Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

/-- An infinite binary tree: the corecursion builds a finite forest of states. -/
def Tree.bin {α : Type u} (a : α) : Tree α :=
  Tree.corec (S := Unit) (fun _ => .node a (.cons () (.cons () .nil))) ()

theorem Tree.bin_eq {α : Type u} (a : α) :
    Tree.bin a = .node a (.cons (.bin a) (.cons (.bin a) .nil)) := by
  conv_lhs => rw [← Tree.ctor_dtor (Tree.bin a), Tree.bin, Tree.dtor_corec]
  simp [Tree.bin]

def Forest.length {α : Type u} (f : Forest α) : Nat :=
  Forest.fold (S := Nat) (fun | .nil => 0 | .cons _ n => n + 1) f
```

A block mixing `data` and `codata` has several solutions, so the order of the declarations is
the nesting order: the first one is outermost. Here the trees are infinite and every forest is
finite; in the other order, the trees are finite and a forest may be infinite. Each type gets
the interface of its kind.

### Corecursion by `partial_fixpoint`

```lean
@[with_ccpo]
codata CoList (α : Type u)
  | nil
  | cons (a : α) (t : CoList α)

def CoList.nats (n : Nat) : CoList Nat := .cons n (nats (n + 1))
partial_fixpoint

def CoList.map {α β : Type u} (f : α → β) (s : CoList α) : CoList β :=
  match s.dtor with
  | .nil => .nil
  | .cons a t => .cons (f a) (map f t)
partial_fixpoint

/-- Not productive: the least fixpoint is the bottom, `nil`. -/
def CoList.stuck : CoList Nat := stuck
partial_fixpoint

example {α β : Type u} (f : α → β) (a : α) (t : CoList α) :
    (CoList.cons a t).map f = .cons (f a) (t.map f) := by
  rw [CoList.map]; simp

open Lean.Order in
example : CoList.stuck = .nil := by
  have h : CoList.stuck ⊑ .nil :=
    CoList.stuck.fixpoint_induct _ (Codata.admissible_rel _) fun _ h => h
  exact PartialOrder.rel_antisymm h (CoList.bot_eq ▸ bot_le _)
```

`with_ccpo` takes a constructor without arguments as the least element (the first one, or the
one named: `attribute [with_ccpo nil] CoList`), and orders the type by approximation: `nil`
is below everything, and two values with the same constructor are related when their
arguments are. Every chain has a least upper bound, so `partial_fixpoint` accepts
definitions whose recursive calls are arguments of constructors, also after a `match` on
`dtor`, and gives their equations and an induction principle. A recursive call through a
function of your own needs a monotonicity lemma for that function. The idea follows
[ISTA-PLV/coinductive](https://github.com/ISTA-PLV/coinductive).

More examples, with what works and what does not yet, are in the walkthroughs
[`Sketch/MutualTour.lean`](Sketch/MutualTour.lean),
[`Sketch/NestingTour.lean`](Sketch/NestingTour.lean),
[`Sketch/MixedTour.lean`](Sketch/MixedTour.lean) and
[`Sketch/CCPOTour.lean`](Sketch/CCPOTour.lean).

## How it works, and why you can trust it

Most of this project's code was written with heavy use of AI. For a library that declares
types, this raises a fair question: how do you know that the type you get is the type you mean
when you write a `codata` or `data` declaration? The question is fair whoever wrote the
implementation, a person or a model, since the construction behind each type is long and
intricate. The answer does not ask you to read it. A (co)inductive type has a short
mathematical specification, and Colean proves that specification for every type it declares.

A declaration is processed in four steps.

1. **The functor.** The constructors define a functor `T.F`: the same constructors with every
   occurrence of `T` replaced by a variable `X`, and its action on functions `T.F.map`. This is
   a small piece of code, [`Colean/Gen/Functor.lean`](Colean/Gen/Functor.lean), and its
   output is an ordinary `inductive` that you can read:

   ```
   #print Strm.F
   -- Strm.F.cons : {α : Type} → {X : Type u_1} → α → X → Strm.F α X
   #print Strm.F.map
   -- fun f a => Strm.F.casesOn a fun head tail => Strm.F.cons head (f tail)
   ```

2. **The type.** `T` is built as a subtype of a general carrier, a least or greatest fixpoint
   of an encoding of `T.F`. This is the large and heavy part, and nobody needs to review it,
   because of the next step.

3. **The contract.** Colean proves `T.contract : Codata.Contract T T.F` (or
   `Data.Contract` for `data`), defined in [`Colean/Framework.lean`](Colean/Framework.lean).
   For `codata`, the contract asks for a destructor `dtor : T → T.F T`, a corecursor with its
   computation rule `dtor (corec c s) = T.F.map (corec c) (c s)`, and the coinduction principle
   for the relation lifting `Rel`. `Rel` is defined once in the same file from `map` alone: it
   is not something the generator can choose. This says exactly that `T` is the final
   coalgebra of `T.F`. Any two types with a contract for the same functor are isomorphic
   (`Codata.Contract.corec_corec`). Dually, `Data.Contract` asks for a constructor, a fold with
   its computation rule, and induction, and says that `T` is the initial algebra of `T.F`.

4. **The interface.** Everything else is derived from the contract.
   - [`Colean/Framework.lean`](Colean/Framework.lean) holds the general theorems: the
     constructor as the inverse of the destructor (Lambek's lemma), injectivity, and uniqueness
     of `corec` and `fold`.
   - [`Colean/Gen/Framework.lean`](Colean/Gen/Framework.lean) instantiates them for `T` and
     contains no proofs of its own.
   - [`Colean/Gen/Surface.lean`](Colean/Gen/Surface.lean) builds the user-facing declarations
     from these pieces. A constructor is the contract's constructor at the functor's
     constructor (`#print Strm.cons` shows `Strm.ctor (Strm.F.cons head tail)`), and
     `casesOn` is case analysis on `dtor`.

   The dependent recursor `T.rec` of a `data` type is built on the encoding, but its type and
   its computation rules `T.rec_cᵢ`, which are theorems, say what it is.

So a skeptic needs to review three short pieces: the functor extraction, the definition of the
contract, and the derivation of the interface. Then, for each declared type, check its functor
and its contract:

```
#print T.F            -- your constructors, with `T` replaced by `X`
#print T.F.map        -- the obvious action on functions
#check @T.contract    -- a `Codata.Contract T T.F` or a `Data.Contract T T.F`
#print T.contract     -- its `map` is `T.F.map`
#print axioms T.contract
```

A `mutual` block is one family indexed by which type you mean, `Tree_Forest.Ix`, with one
contract for the block, and each type is that family at its index
(`#print Tree` shows `Tree_Forest Tree_Forest.Ix.Tree`). In a `mixed_mutual` block, an inner
type is first declared with the outer types as a parameter (`Forest.Open α X`), with its own
contract, and the closed type is that one at the outer type (`Forest α := Forest.Open α (Tree α)`).

Colean does not handle every declaration you can write: it supports most of the types that are
useful in practice, and it may reject some it could in principle accept. When it cannot build
a type or prove its contract, the command fails with an error and declares nothing. It never produces a
type that does not satisfy its contract, because every declaration and every proof is checked
by Lean's kernel. Bug reports and feature requests are welcome in the
[issues](https://github.com/vasnesterov/colean/issues).

The contracts are described in more detail in [`contract.md`](contract.md), and the steps and
files in [`architecture.md`](architecture.md).

## Limitations

- **`mixed_mutual` is best effort.** It is supported only partly. An outer type with indices
  or an outer `mutual` block is not supported, and some blocks fail with errors that are hard
  to read. See Part II of [`Sketch/MixedTour.lean`](Sketch/MixedTour.lean).
- **No `match` on the declared types.** The types are subtypes and their constructors are
  definitions, so `match`, `rcases` patterns, structural recursion and the equation compiler
  cannot see them. Use `casesOn`, `rec`, `fold`, `corec`, the `cases` and `induction` tactics
  (which use the generated eliminators), or `match t.dtor with`, which is a match on the
  functor, an ordinary inductive type. Lean's
  [RFC: custom recursors (lean4#2716)](https://github.com/leanprover/lean4/issues/2716) would
  lift this restriction.
- **Computation rules are theorems.** `rec`, `fold` and `corec` compute on constructors by
  `simp` lemmas (`T.rec_cᵢ`, `T.fold_cᵢ`, `T.dtor_corec`), not by definitional unfolding, so
  `rfl` and `decide` do not evaluate them. Everything generated is noncomputable.
- **No coinduction tactic and no general corecursion.** Coinduction is by applying `T.bisim`
  with a relation you write. Corecursion is primitive, through `T.corec`, or through
  `partial_fixpoint` for a type with `with_ccpo`. There is nothing like Isabelle's
  `coinduction` proof method or its framework for corecursion up to friendly operations.
