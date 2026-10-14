# Contract for `codata`

```
codata T
  | ctor₁ …
  | ctor₂ …
```

The constructor list defines a functor `F`, the sum of the constructors' argument types with `T`
replaced by a variable. `F.map` is its action on functions, with the functor laws
`F.map id = id` and `F.map (g ∘ f) = F.map g ∘ F.map f`. Its lifting to relations is *defined*
from `F.map`: `F.Rel R a b` holds when `a` and `b` are the two projections of one value over
`R`-related pairs,

```
F.Rel R a b := ∃ z : F {p : X × Y // R p.1 p.2}, F.map (·.1.1) z = a ∧ F.map (·.1.2) z = b
```

which for the generated `F` means: same constructor, equal non-recursive fields, related
recursive fields. The command produces:

1. The type `T`.
2. Destructor `dtor : T → F T`.
3. Corecursor `corec : (S → F S) → S → T`.
4. `dtor_corec : ∀ c x, dtor (corec c x) = F.map (corec c) (c x)`.
5. `bisim : (∀ x y, R x y → F.Rel R (dtor x) (dtor y)) → ∀ x y, R x y → x = y`.

This is the minimal interface, and it is tight: `F.Rel` is not a parameter of it, so `bisim` is
Park's coinduction principle for `F` and nothing looser, and `(T, dtor)` is a final coalgebra of
`F`. Constructors
`ctor : F T → T` with `dtor_ctor` and `corec_eq : corec c x = ctor (F.map (corec c) (c x))`
will be provided later, derived from `dtor` and `dtor_corec` (`ctor := corec (F.map dtor)`).


# Indexed families

```
codata T : I → Type u
  | ctor₁ … : T idx₁
  | ctor₂ … : T idx₂
```

Everything is read over families `I → Type u`, for an index type `I : Type w`. The constructor
list defines a functor `F` on families, `F X : I → Type u`: at index `i`, the sum of the
constructors whose result index is `i`, with `T idx` replaced by `X idx` in their argument
types. `F.map` is its action on functions of families, with the functor laws, and `F.Rel` is
defined from it as in the plain case, indexwise:

```
F.map : (∀ j, X j → Y j) → ∀ {i}, F X i → F Y i
F.Rel R a b := ∃ z : F (fun j => {p : X j × Y j // R j p.1 p.2}) i,
  F.map (fun _ p => p.1.1) z = a ∧ F.map (fun _ p => p.1.2) z = b
```

The command produces:

1. The family `T : I → Type u`.
2. Destructor `dtor : ∀ {i}, T i → F T i`.
3. Corecursor `corec : (∀ i, S i → F S i) → ∀ {i}, S i → T i`, for any family `S : I → Type v`,
   in any universe `v`.
4. `dtor_corec : ∀ c {i} (x : S i), dtor (corec c x) = F.map (fun _ x => corec c x) (c i x)`.
5. `bisim : (∀ i x y, R i x y → F.Rel R (dtor x) (dtor y)) → ∀ {i} x y, R i x y → x = y`,
   for any `R : ∀ i, T i → T i → Prop`.

This is the plain contract in the category of families over `I`: `(T, dtor)` is a final
coalgebra of `F` there. The index is implicit wherever an argument determines it, and explicit
in the families of functions and relations. A plain type is the case `I = Unit`. Derived as
before: `ctor : ∀ {i}, F T i → T i` with `dtor_ctor`, and `corec_eq`. With several indices
`(i₁ : I₁) → I₂ → Type u`, `I` is their `PSigma` and every statement above is curried.

Universes: `u` is arbitrary, but the encoding stores the index in the tree, so the family lives
in a universe at least that of `I` (and of the constructors' data), `u ≥ w`; `inductive` has no
such constraint. The command writes `Type _` for the family and lets Lean compute the level, so
a declaration with `u` too small comes out one level higher rather than failing.


# Inductive types

```
data T
  | ctor₁ …
  | ctor₂ …
```

The same functor `F`, with `F.map` and the functor laws. Its lifting to predicates is *defined*
from `F.map`: `F.All P a` holds when `a` is the projection of a value over elements satisfying
`P`,

```
F.All P a := ∃ z : F {x : X // P x}, F.map (·.1) z = a
```

which for the generated `F` means: every recursive field satisfies `P`. The command produces:

1. The type `T`.
2. Constructor `ctor : F T → T`.
3. Fold `fold : (F S → S) → T → S`, for any `S : Type v`, in any universe `v`.
4. `fold_ctor : ∀ a y, fold a (ctor y) = a (F.map (fold a) y)`.
5. `induction : (∀ y, F.All motive y → motive (ctor y)) → ∀ t, motive t`, for any
   `motive : T → Prop`.

This is the dual of the coinductive contract and tight in the same way: `F.All` is not a
parameter, so `induction` is the induction principle for `F` and nothing weaker, and `(T, ctor)`
is an initial algebra of `F`. Derived from the contract alone: `dtor : T → F T`
(`dtor := fold (F.map ctor)`) with `dtor_ctor` and `ctor_dtor`, `fold_eq : fold a t =
a (F.map (fold a) (dtor t))`, uniqueness of `fold`, and the isomorphism between any two
implementations. Indexed families are read over `I → Type u` exactly as in the previous section:
`fold : (∀ i, F S i → S i) → ∀ {i}, T i → S i` and `induction` for `motive : ∀ i, T i → Prop`,
with the same universe remarks.

Nested occurrences change nothing in the contracts. A constructor argument whose type mentions
`T` other than plainly or under arrows, `List (T idx)`, `T i × T j`, `A → List (T idx)`,
`Option (T idx × T idx)`, `(n : ℕ) × (Fin n → T idx)`, …, has an *occurrence structure*: an
equivalence `G X ≃ Σ sh, Pos sh → X` between the argument type as a function `G` of the
occurrence and a shape with contents at its positions (`Codata.Occ`, `Codata.IOcc` when the
positions carry an index of the family). It is built by recursion on the syntax of the type,
from a constant, the occurrence, products, sums, functions and dependent pairs over constant
types, and named type constructors, whose structures are leaves (`List`, `Option`, `Array`, the
declared types, any type constructor registered with `Codata.OccLeaf`). `F` keeps the argument
type as a field, `F.map` acts on it through the structure (`Occ.map`, which is `List.map` on
lists, componentwise on pairs, …, by the simp lemmas `Occ.map_list`, `Occ.map_prod`, …), and the
canonical `F.Rel` relates nested fields with the same shape and related contents (`Occ.Rel`).

Conversely a declared type has an occurrence structure in its type parameter, when the last
parameter `α` is used only at parameter positions (as the type of a field, under a function type,
or nested). Then `T.Shape α ≅ Σ s₀ : T.Shape₀, T.P s₀ → α` (`T.shapeEquiv`) with the erased
shapes `T.Shape₀` and the parameter positions `T.P`, and the command provides
`T.occ : Codata.Occ T.Sh T.Pos (fun α => T params α idx)`: the shapes `T.Sh` are the erased
trees (the type at the signature `T.psig.sig₀`), a position is a path to a node together with a
parameter position of its erased shape, and the structure is the generic `PSignature.occ`/`coocc`
(`Param.lean`), registered as a leaf. The same holds for a family parameter `X : J → Type u`
(positions `X j`), with the indexed structure `Codata.IOcc` (`G X ≅ Σ sh, (q : Pos sh) →
X (pidx sh q)`), of which `Occ` is the case `J = Unit`. This is what lets a later declaration
nest through `T` (`Forest (Tree α)` with a declared `Forest`). The structure is computed on the
constructors: `T.map_c : Occ.map T.occ T.occ f (T.c …) = T.c …` with `f` at the parameter
positions, `map f` at the recursive ones and `map (map f)` through nested arguments, and
`T.rel_c : R … → Rel R … → Occ.Rel T.occ T.occ R (T.c …) (T.c …)`, the introduction of the
relator from `R` at the parameter positions and `Rel R` at the recursive ones; the two copies of
the parameter are in independent universes.


# Mixed blocks

```
mixed_mutual
codata Tree (α : Type u)
  | node (a : α) (children : Forest α)
data Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end
```

A block with `data` and `codata` declarations is a nested fixpoint, and a cyclic system has
several nested solutions (the trees outside the forests are the finitely branching infinite
trees, the forests outside the trees the finite ones), so the block states the order: *the
textual order is the nesting order, the first declaration outermost*. A `mutual` block may not
mix the two kinds. A *run* is a maximal sequence of adjacent declarations of the same kind and
is one uniform block with the contract above; runs `R₁ ⊃ R₂ ⊃ … ⊃ Rₖ` nest as follows.

1. A run is declared with one extra parameter for the run outside it that it mentions, the
   family `X` (a type `X : Type u_<R>` for a run of one type without indices, a family
   `X : J → Type u_<R>` over the run's packed index `(m : Which) ×' idx` otherwise), every
   occurrence of a type of that run replaced by `X` (at its packed index) and every occurrence
   of its own types applied to `X`.
2. Every occurrence of a type `E` of the run inside it is `E params (Rᵢ params X)` (or
   `E params (fun p => Rᵢ params X p.1 …)`), a nested occurrence through the container that
   `E` is in its family parameter.
3. The outermost run has no extra parameter: its types are closed.

So the user sees the parameterised inner types (`Forest α X`, `Forest.nil : Forest α X`,
`Forest.fold`, `Forest.rec`) and the closed outer ones (`Tree.node : α → Forest α (Tree α) →
Tree α`, `Tree.corec`, `Tree.bisim` with `Occ.Rel`/`IOcc.Rel` on the forests). The
principles compose: coinduction on an outer run sees the inner runs through their relators, one
finite layer per step (`Forest.rel_cons`, `Occ.rel_map`); induction on an inner run sees
the outer runs as opaque parameters; an inner induction inside a coinductive step is parametric
in the outer relation; a coinduction inside an inductive step is a closed statement about the
outer type. All declarations of a block have the same parameters, the declarations of a run
the same indices; the universe of a family parameter is a `universe` variable declared in
scope. Any number of runs, in any order; a declaration may mention any run inside its own (an
occurrence of a type of a run further inside is applied to the chain of families down to the
declaration's own run, `Trace α (Menu α (Proc α))`, a nested occurrence through the composite of
the declared structures); for now, among the runs outside its own, only the adjacent one.

Beyond the contract, the command generates the dependent recursor `T.rec` into any `Sort`, with
one minor premise per constructor carrying an induction hypothesis for each recursive argument.
It is derivable from the contract (a fold into `Σ t, motive t`, with `induction` showing the
first component is the identity), but the command takes it from the encoding, by well-founded
recursion on the immediate-child relation, so its computation rules `T.rec_ctorᵢ` hold
propositionally and not by `rfl`.
