# Colean

(Co)inductive types for Lean 4.

Lean's type theory has no coinductive types. 
Colean adds the `codata` command that declares them, with `inductive`-like syntax.

```lean
/-- Potentially infinite lists -/
codata CoList (α : Type)
  | nil
  | cons (head : α) (tail : CoList α)
```

## Installation

Add to your `lakefile.toml`:

```toml
[[require]]
name = "Colean"
git = "https://github.com/vasnesterov/colean"
rev = "main"
```

Then `import Colean`.

## Examples

### Corecursion, coinduction, case analysis

```lean
codata Strm (α : Type)
  | cons (head : α) (tail : Strm α)

-- Corecursion: one step from a state. Here the state is the next element.
noncomputable def Strm.iterate {α : Type} (f : α → α) (a : α) : Strm α :=
  Strm.corec (fun x => .cons x (f x)) a

noncomputable def Strm.const {α : Type} (a : α) : Strm α :=
  Strm.corec (fun _ => .cons a ()) ()

-- Coinduction: related streams have equal heads and related tails.
theorem Strm.iterate_id {α : Type} (a : α) : Strm.iterate id a = Strm.const a := by
  refine Strm.bisim (fun x y => x = .iterate id a ∧ y = .const a) ?_ ⟨rfl, rfl⟩
  rintro _ _ ⟨rfl, rfl⟩
  simp only [Strm.iterate, Strm.const, Strm.dtor_corec, Strm.F.map_cons, id]
  exact .cons _ _ _ ⟨rfl, rfl⟩

-- Case analysis, by `casesOn` or the `cases` tactic.
noncomputable def Strm.head {α : Type} (s : Strm α) : α := s.casesOn fun a _ => a

example {α : Type} (a : α) (s : Strm α) : (Strm.cons a s).head = a := by simp [Strm.head]
```

### Inductive types and families

```lean
-- `data` declares inductive types, here an indexed family.
data Vec (α : Type) : Nat → Type
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

noncomputable def Vec.toList {α : Type} {n : Nat} (v : Vec α n) : List α :=
  Vec.rec (motive := fun _ _ => List α) [] (fun a _ l => a :: l) v

-- Induction, by `rec` or the `induction` tactic.
theorem Vec.length_toList {α : Type} {n : Nat} (v : Vec α n) : v.toList.length = n := by
  induction v with
  | nil => simp [Vec.toList]
  | cons a v ih => simp_all [Vec.toList]
```

### Mutual blocks

```lean
mutual
data Tree
  | node (n : Nat) (cs : Forest)
data Forest
  | nil
  | cons (t : Tree) (f : Forest)
end

-- One motive per type, as for Lean's mutual inductives.
noncomputable def Tree.size (t : Tree) : Nat :=
  Tree.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ _ k => k + 1) 0 (fun _ _ a b => a + b) t
```

### Nesting

```lean
-- Nesting through `List`, `Option`, products, functions, other `data`/`codata` types, ...
data Rose (α : Type)
  | node (a : α) (children : List (Rose α))

-- Infinite trees, each node with a finite list of children.
codata Tree (α : Type)
  | node (a : α) (children : List (Tree α))

-- `fold` gets the children already folded.
noncomputable def Rose.size {α : Type} (t : Rose α) : Nat :=
  Rose.fold (S := Nat) (fun | .node _ cs => cs.sum + 1) t
```

### Mixed blocks (best effort)

```lean
-- `data` and `codata` in one block: the first declaration is outermost.
-- Here trees are infinite, and every forest is finite.
mixed_mutual
codata Tree (α : Type)
  | node (a : α) (children : Forest α)
data Forest (α : Type)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

noncomputable def Tree.bin {α : Type} (a : α) : Tree α :=
  Tree.corec (S := Unit) (fun _ => .node a (.cons () (.cons () .nil))) ()
```

### Corecursion by `partial_fixpoint`

```lean
-- With `with_ccpo`, corecursive functions can be written directly, by `partial_fixpoint`.
@[with_ccpo]
codata CoList (α : Type)
  | nil
  | cons (head : α) (tail : CoList α)

noncomputable def CoList.map {α β : Type} (f : α → β) (s : CoList α) : CoList β :=
  match s.dtor with
  | .nil => .nil
  | .cons a t => .cons (f a) (map f t)
partial_fixpoint

noncomputable def CoList.nats (n : Nat) : CoList Nat := .cons n (nats (n + 1))
partial_fixpoint

example {α β : Type} (f : α → β) (a : α) (t : CoList α) :
    (CoList.cons a t).map f = .cons (f a) (t.map f) := by
  rw [CoList.map]; simp
```

More examples, with what works and what does not yet, are in
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
by Lean's kernel. The types are definitions, not axioms, and use only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. Bug reports and feature requests are welcome in the
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
