# Contract for `codatatype`

```
codatatype T
  | ctor₁ …
  | ctor₂ …
```

The constructor list defines a functor `F`, the sum of the constructors' argument types with `T`
replaced by a variable. `F.fmap` is its action on functions (generated as `T.F.fmap`, the field
`map` of the contract `T.contract`), with the functor laws `F.fmap id = id` and
`F.fmap (g ∘ f) = F.fmap g ∘ F.fmap f`. Its lifting to relations is *defined* from `F.fmap`:
`F.Rel R a b` holds when `a` and `b` are the two projections of one value over `R`-related pairs,

```
F.Rel R a b := ∃ z : F {p : X × Y // R p.1 p.2}, F.fmap (·.1.1) z = a ∧ F.fmap (·.1.2) z = b
```

which for the generated `F` means: same constructor, equal non-recursive fields, related
recursive fields. The command produces:

1. The type `T`.
2. Destructor `dtor : T → F T`.
3. Corecursor `corec : (S → F S) → S → T`.
4. `dtor_corec : ∀ c x, dtor (corec c x) = F.fmap (corec c) (c x)`.
5. `bisim : (∀ x y, R x y → F.Rel R (dtor x) (dtor y)) → ∀ {x y}, R x y → x = y`.

This is the minimal interface, and it is tight: `F.Rel` is not a parameter of it, so `bisim` is
Park's coinduction principle for `F` and nothing looser, and `(T, dtor)` is a final coalgebra of
`F`. Constructors
`ctor : F T → T` with `dtor_ctor` and `corec_eq : corec c x = ctor (F.fmap (corec c) (c x))`
will be provided later, derived from `dtor` and `dtor_corec` (`ctor := corec (F.fmap dtor)`).


# Indexed families

```
codatatype T : I → Type u
  | ctor₁ … : T idx₁
  | ctor₂ … : T idx₂
```

Everything is read over families `I → Type u`, for an index type `I : Type w`. The constructor
list defines a functor `F` on families, `F X : I → Type u`: at index `i`, the sum of the
constructors whose result index is `i`, with `T idx` replaced by `X idx` in their argument
types. `F.fmap` is its action on functions of families, with the functor laws, and `F.Rel` is
defined from it as in the plain case, indexwise:

```
F.fmap : (∀ j, X j → Y j) → ∀ {i}, F X i → F Y i
F.Rel R a b := ∃ z : F (fun j => {p : X j × Y j // R j p.1 p.2}) i,
  F.fmap (fun _ p => p.1.1) z = a ∧ F.fmap (fun _ p => p.1.2) z = b
```

The command produces:

1. The family `T : I → Type u`.
2. Destructor `dtor : ∀ {i}, T i → F T i`.
3. Corecursor `corec : (∀ i, S i → F S i) → ∀ {i}, S i → T i`, for any family `S : I → Type v`,
   in any universe `v`.
4. `dtor_corec : ∀ c {i} (x : S i), dtor (corec c x) = F.fmap (fun _ x => corec c x) (c i x)`.
5. `bisim : (∀ i x y, R i x y → F.Rel R (dtor x) (dtor y)) → ∀ {i x y}, R i x y → x = y`,
   for any `R : ∀ i, T i → T i → Prop`.

This is the plain contract in the category of families over `I`: `(T, dtor)` is a final
coalgebra of `F` there. The index is implicit wherever an argument determines it, and explicit
in the families of functions and relations. A plain type is the case `I = Unit`. Derived as
before: `ctor : ∀ {i}, F T i → T i` with `dtor_ctor`, and `corec_eq`. With several indices
`(i₁ : I₁) → I₂ → Type u`, `I` is their `PSigma` and every statement above is curried.

Universes: the encoding stores the index in the tree, so the family lives in the universe of its
encoding, the largest of those of `I` and of the constructors' data, `u = max w …`; `inductive`
has no such constraint, and accepts any `u` large enough. A universe written in the declared sort
must be that one: otherwise the command fails before declaring anything, with an error at the
sort that gives the right universe (a declared `Prop` too, since the commands define types).
`Type _`, or no sort, leaves the universe to the command.


# Inductive types

```
datatype T
  | ctor₁ …
  | ctor₂ …
```

The same functor `F`, with `F.fmap` and the functor laws. Its lifting to predicates is *defined*
from `F.fmap`: `F.All P a` holds when `a` is the projection of a value over elements satisfying
`P`,

```
F.All P a := ∃ z : F {x : X // P x}, F.fmap (·.1) z = a
```

which for the generated `F` means: every recursive field satisfies `P`. The command produces:

1. The type `T`.
2. Constructor `ctor : F T → T`.
3. Fold `fold : (F S → S) → T → S`, for any `S : Type v`, in any universe `v`.
4. `fold_ctor : ∀ a y, fold a (ctor y) = a (F.fmap (fold a) y)`.
5. `induction : (∀ y, F.All motive y → motive (ctor y)) → ∀ t, motive t`, for any
   `motive : T → Prop`.

This is the dual of the coinductive contract and tight in the same way: `F.All` is not a
parameter, so `induction` is the induction principle for `F` and nothing weaker, and `(T, ctor)`
is an initial algebra of `F`. Derived from the contract alone: `dtor : T → F T`
(`dtor := fold (F.fmap ctor)`) with `dtor_ctor` and `ctor_dtor`, `fold_eq : fold a t =
a (F.fmap (fold a) (dtor t))`, uniqueness of `fold`, and the isomorphism between any two
implementations. Indexed families are read over `I → Type u` exactly as in the previous section:
`fold : (∀ i, F S i → S i) → ∀ {i}, T i → S i` and `induction` for `motive : ∀ i, T i → Prop`,
with the same universe remarks.

Nested occurrences change nothing in the contracts. A constructor argument whose type mentions
`T` other than plainly or under arrows, `List (T idx)`, `T i × T j`, `A → List (T idx)`,
`Option (T idx × T idx)`, `(n : ℕ) × (Fin n → T idx)`, …, has an *occurrence structure*: an
equivalence `G X ≃ Σ sh, Pos sh → X` between the argument type as a function `G` of the
occurrence and a shape with contents at its positions (`Codata.Occ`, `Codata.IOcc` when the
positions carry an index of the family). It is built by recursion on the elaborated type, from
a constant, the occurrence, products, sums, functions and dependent pairs over constant types,
and named type constructors, whatever their spelling. `F` keeps the argument type as a field, `F.fmap` acts on it
through the structure, and the canonical `F.Rel` relates nested fields with the same shape and
related contents (`Occ.Rel`).

A named type constructor `G` is the user's part of the contract (`PolyIso.lean`):

1. `PolyIso G Sh Pos`: `G` is presented as a polynomial functor, `G X ≃ Σ sh : Sh, (Pos sh → X)`
   for every `X`.
2. `PolyMap G G'`: the intended action `G X → G' Y` on functions, between two instantiations of
   `G`, with the naturality of the presentation.

Together they are an isomorphism of functors. The action is a class on two instantiations
because the state of `corec` lives in any universe, so `F.fmap` crosses universes, which Lean's
`Functor` cannot state, and naturality in each universe separately does not determine the map
between them. The command requires both instances. It follows that the map on such a field is
the intended one (`Occ.map_ofIso`): `List.map` on lists (`Occ.map_list`), and componentwise on
pairs and the other built-in forms (`Occ.map_prod`, …). For a functor on families the classes
are `IPolyIso` and `IPolyMap`, with `G X ≃ Σ sh, (q : Pos sh) → X (pidx sh q)`.

A declared type gets these instances when it can, in a separate step after its declaration
(`Gen/Derive.lean`): for `fun X => T (H₁ X) … (Hₙ X)` over the parameters that may vary, with the
`Hᵢ` themselves instances, so that one instance covers every use, constants and the identity
being instances too; the `PolyMap` instance from `PolyMap` instances of the `Hᵢ`, so that it is
the map between two instantiations of one functor only, as for the built-in forms. A parameter
may vary when its fields have an occurrence structure in it, also with other parameters
(`p : α × β`) or with the type itself, through products and sums (`p : α × T α`,
`f : T α ⊕ α`), and under a named type constructor or a function too, where the field has a
structure in both, the parameter and the type (`p : List (α × T α)`, `k : Nat → α × T α`,
`p : List (α ⊕ T α)`; `Occ₂`, and for a family or a block `IOcc₂`, whose positions in the type
carry its index: `p : List (α × T n)`). In a block, a field with the block's types inside a named
type constructor has such a structure too when its positions are at one type after cases on them
(`p : List (A α × Nat)`). When the parameters of a field cannot vary together, the fewest are
constant, the first ones first. If that step fails, it logs a warning with a short reason and
leaves no trace: the type is declared as usual and can still be given instances by hand; when no
parameter may vary because of a field, an info says why. The step works from the contract:
a value is a tree of shapes with the contents of its slots (`Model/Poly.lean`), and the map on
the parameter is the structural one (`PolyFix.d_map`). A family gets them at every index,
`fun X => T (H X) idx`, and so do the types of a block, at their index of the block
(`IPolyFix.d_map`).


# Corecursion by `partial_fixpoint`

```
codatatype CoList (α : Type u)
  | nil
  | cons (a : α) (t : CoList α)

attribute [with_ccpo] CoList     -- or `@[with_ccpo] codatatype CoList …`, or `with_ccpo (bot := nil)`

def map (f : α → β) (s : CoList α) : CoList β :=
  match s.dtor with
  | .nil => .nil
  | .cons a t => .cons (f a) (map f t)
partial_fixpoint
```

Off by default. The attribute `with_ccpo`, optionally naming a constructor without arguments,
`with_ccpo (bot := c)` (by default the first one; an error if there is none), orders a `codatatype` by *approximation*, the
named constructor at the bottom, `⊥ := ctor e` for its layer `e`:

```
x ⊑ y  :=  greatest relation with  x ⊑ y → x = ⊥ ∨ F.Rel (⊑) (dtor x) (dtor y)
```

that is: `x` is the bottom, or `x` and `y` have the same constructor and data and related recursive
arguments. It is a chain-complete partial order: antisymmetric by `bisim`, the supremum of a chain
is `⊥` if every element is, otherwise the common constructor and data of the others with the
suprema of the chains of their children, by `corec`. This is Lean's `Lean.Order.CCPO`, which
`partial_fixpoint` needs on the result type of a definition; the definition is then the least
fixpoint of its equation, which it gets as `f.eq_1`, with the induction principle
`f.fixpoint_induct`. A definition that is not productive is the bottom where it does not produce
(`def bad : CoList Nat := bad` is `nil`, `filter` of nothing is `nil`). The attribute generates:

1. `T.instCCPO : Lean.Order.CCPO (T params)`.
2. `T.approx_iff : x ⊑ y ↔ x = T.c₀ ∨ T.F.Rel (· ⊑ ·) x.dtor y.dtor`.
3. `T.approx_coind`: a relation `R` with `R x y → x ⊑ y ∨ T.F.Rel (R ∪ ⊑) x.dtor y.dtor` is
   contained in `⊑` (coinduction up to the order, for the monotonicity of the user's functions).
4. `T.bot_eq : Lean.Order.bot = T.c₀` (`simp`).
5. `T.monotone_c : monotone t → monotone fun x => T.c a (t x)` for each constructor with a
   recursive argument, tagged `@[partial_fixpoint_monotone]`: an argument under a function is
   ordered pointwise, a nested one through a leaf (`List T`) by its structure (`Occ.order`, through
   which `List.map`, `Option.map` and `Array.map` are monotone); other arguments are fixed.

The theory is one proof for all types (`Model/CCPO.lean`), from the contract and the presentation
of `F` as a container that every generated type has. For a family the bottom is a constructor at
every index, `| stop {n : Nat} : T n`, and the order is at every index. Not supported: several
indices, the types of `mutual` and `mixed_mutual` blocks (but the outer `codatatype` of a mixed
block).


# Mutual blocks

```
mutual
datatype Even : Nat → Type
  | zero : Even 0
  | succ {n : Nat} (o : Odd n) : Even (n + 1)
datatype Odd : Nat → Type
  | succ {n : Nat} (e : Even n) : Odd (n + 1)
end
```

A block of `datatype` declarations, or of `codatatype` declarations, is one family `Even_Odd` over
the inductive `Even_Odd.Ix`, with a constructor per type whose arguments are the indices of that
type (`Ix.Even n`, `Ix.Odd n`), so the contract is the one of indexed families, over `I = Ix`. The
types are `Even n := Even_Odd (.Even n)`. All types of a block have the same parameters, on which
`Ix` may depend. Their indices may differ, and a type may have none. As for any family, the family
lives in a universe at least that of `Ix`, so the largest index of the block counts for every type,
and a universe written in a type's sort must be the block's. The block declares its name and
`Even_Odd.Ix`, made of the types' names: these must be free, as the types' own names, and no type
may occur twice; the command checks this before declaring anything.


# Mixed blocks

```
mixed_mutual
codatatype Tree (α : Type u)
  | node (a : α) (children : Forest α)
datatype Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end
```

A block with `datatype` and `codatatype` declarations is a nested fixpoint, and a cyclic system has
several nested solutions (the trees outside the forests are the finitely branching infinite
trees, the forests outside the trees the finite ones), so the block states the order: the
textual order is the nesting order, the first declaration outermost. A plain `mutual` block may
not mix the two kinds. The declarations share their parameters, names included, and their
universe where it is written, as in `mutual`.

A *run*, a maximal sequence of adjacent declarations of the same kind, is a single declaration
or a uniform block, and has the uniform contract of its kind, with the runs outside it as
parameters. For runs `R₁ ⊃ R₂ ⊃ … ⊃ Rₖ`:

1. Each run `Rᵢ` with `i > 1` is declared *open*: with one more parameter `X` for each run
   outside it that it needs (a type `X` for a run of one type without indices, a family over the
   run's index otherwise), every occurrence of a type of that run replaced by `X`. Its contract
   is that of a `datatype` or `codatatype` declaration (or block) with these parameters:
   `Forest.Open α X` with `Forest.Open.fold`, `Forest.Open.rec`, … for any `X`. A run further
   inside occurs as its open type at the families of the runs it needs, a nested occurrence.
2. The outer types nest through the open types of the runs inside at their own types:
   `Tree` is the `codatatype` declaration whose children are `Forest.Open α (Tree α)`. This needs
   the open types to be polynomial in their extra parameters, `PolyIso (fun X => Forest.Open α X)`,
   which the command generates as for any declared type (step 5).
3. The closed types are the open ones at the outer types, `Forest α := Forest.Open α (Tree α)`,
   from the outermost run in: each run's types at the closed types of the runs it needs. Each
   closed type has the contract of a standalone declaration, the open one at these families:
   `Forest.F α S := Forest.Open.F α (Tree α) S`, `Forest.fold`, `Forest.rec`, `Forest.dtor`, …,
   and the outer types' are stated with the closed types: `Tree.node : α → Forest α → Tree α`.

The functor of a run at its state has the open types of the runs inside at that state:
`Tree.F α S` is `α × Forest.Open α S`, so `Tree.corec` takes a step `S → α × Forest.Open α S`,
and `Tree.bisim` relates the children by `Occ.Rel` through the open forests' instance. Composed,
these are the contracts of the nested fixpoint: `(Tree, dtor)` is a final coalgebra of
`X ↦ α × μ F. 1 + X × F`, and `Forest α` the initial algebra of `F ↦ 1 + Tree α × F`.

The recursors of a run are those of its kind, the outer types opaque in the inner runs
(`Forest.rec` has no hypothesis for the trees), and a nested argument of an outer run through an
inner one has its hypothesis by membership in the closed type: `Membership (Tree α) (Forest α)`
is `PolyIso.Mem (fun X => Forest.Open α X)`, and `simp` computes it on the constructors
(`Forest.mem_cons : x ∈ Forest.cons t f ↔ x = t ∨ x ∈ f`).

A field may mention an outer type together with the run's own type through products and sums
(`Tree α × Forest α`), or under a named type constructor or a function where the field has a
structure in both (`List (Tree α × Forest α)`, `List (Tree α ⊕ Forest α)`), and a run may pass an
outer type on to a run
further inside (its field `C.Open α X` mentions the block's parameters and the outer one). Not
supported: a run outside another whose types have indices or form a block (the open type's
parameter is then a family, and nesting through it needs `IPolyIso` instances), and an outer type
with the run's own type in a field without such a structure (in two arguments of a type
constructor, `Two (Tree α) (Forest α)`): the open types then have no instances in their
parameter, and the block stops with that error.


# Recursors

Beyond the contract, the command generates the dependent recursor `T.rec` into any `Sort`, with
one minor premise per constructor carrying an induction hypothesis for each recursive argument:
`motive x` for a plain one, `∀ ys, motive (k ys)` under a telescope, and for a nested argument
one by membership,

```
datatype Rose
  | node (n : Nat) (cs : List Rose)

Rose.rec : {motive : Rose → Sort u} →
  ((n : Nat) → (cs : List Rose) → ((t : Rose) → PolyIso.Mem (fun X => List X) t cs → motive t) →
    motive (Rose.node n cs)) →
  (t : Rose) → motive t
```

`PolyIso.Mem F x c` says that some position of `c`, in the presentation of `F`, holds `x`
(`PolyIso.lean`). The functor is the argument's type with the occurrences abstracted, written
out (`fun X => E (List X) X`), at the instance that is its occurrence structure: products, sums,
functions and dependent pairs of functors with instances have instances, so every nested
argument's functor has one, and `simp` turns membership into the container's own (`mem_list`,
`mem_option`, `mem_array`) or into components (`mem_prod`, `mem_sum`, `mem_comp`, …). In a
family, when the positions of a nested argument are all at one index, its members are of the type
at that index and the hypothesis is as above (`List (T n)`, `T n × T n`, `T n × Nat`,
`T n ⊕ T n`); otherwise it is by membership at an index,
`∀ j (t : T j), IPolyIso.Mem (fun X => G X) j t c → motive j t` (`T n × T (n + 1)`, and a sum
inside a named type constructor, `List (T n ⊕ T n)`). The instance is the one instance search
finds for the functor (`fun X => Vec (List X) n` is `Vec`'s instance at `List`,
`fun X => E (X × Nat) Nat` is `E`'s at the product), so a hypothesis written by hand is the
recursor's. The recursors per type of a block are the same at the motive of each type, with a
hypothesis by `IPolyIso.Mem` for each type of the block in the argument.

The computation rules `T.rec_ctorᵢ` give each hypothesis as the recursor itself:
`Rose.rec node (Rose.node n cs) = node n cs fun t _ => Rose.rec node t`. The recursor is
derivable from the contract (a fold into `Σ t, motive t`, with `induction` showing the first
component is the identity), but the command takes it from the encoding, by well-founded
recursion on the immediate-child relation, so its computation rules hold propositionally and not
by `rfl`.
