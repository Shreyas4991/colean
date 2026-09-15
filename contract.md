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

Nested occurrences `G (T idx)` through a container `G` (`List`, `Option`, `A × ·`, or any type
constructor with a `Codata.Container` instance, `G X ≅ Σ sh, Pos sh → X`) change nothing in the
contracts: `F` keeps `G X` as a field, `F.map` acts inside `G` through the container
(`Container.map`, which is `List.map` on lists), and the canonical `F.Rel` relates nested fields
with the same shape and related contents (`Container.Rel`).

Conversely a declared type is a container in its type parameter, when the last parameter `α` is
used only at parameter positions (as the type of a field, under a function type, or through a
container). Then `T.Shape α ≅ Σ s₀ : T.Shape₀, T.P s₀ → α` (`T.shapeEquiv`) with the erased
shapes `T.Shape₀` and the parameter positions `T.P`, and the command provides
`Codata.Container (fun α => T params α idx) T.Sh T.Pos`: the shapes `T.Sh` are the erased
trees (the type at the signature `T.psig.sig₀`), a position is a path to a node together with a
parameter position of its erased shape, and the instance is the generic
`PSignature.container`/`cocontainer` (`Param.lean`). The same holds for a family parameter
`X : J → Type u` (positions `X j`), with the indexed container class `Codata.IContainer`
(`G X ≅ Σ sh, (q : Pos sh) → X (pidx sh q)`), of which `Container` is the case `J = Unit`.
This is what lets a later declaration nest through `T` (`Forest (Tree α)` with a declared
`Forest`).

A mixed `mutual` block, with `data` and `codata` declarations, means the nested fixpoint with
the inductive types inside the coinductive ones, and its contract is the composition of the two
above: the inductive types are declared with the coinductive family as an extra parameter
(`Forest α X`, a type `X` for one coinductive type without indices, a family `X : J → Type u`
over the coinductive block's packed index otherwise), and the coinductive types are declared
with the inductive ones applied to the coinductive family (`Tree.node : α → Forest α (Tree α)
→ Tree α`, a nested occurrence). So `Forest.fold`, `Forest.rec` are those of the parameterised
inductive type, `Tree.F α X` has the field `children : Forest α X`, and `Tree.corec`,
`Tree.bisim` are those of a coinductive type nesting through a container, with
`Container.Rel`/`IContainer.Rel` on the forests. The other nesting order is another type; it is
written as two declarations in that order.

Beyond the contract, the command generates the dependent recursor `T.rec` into any `Sort`, with
one minor premise per constructor carrying an induction hypothesis for each recursive argument.
It is not derivable from the contract, whose `induction` is in `Prop`; it comes from the
encoding, by well-founded recursion on the immediate-child relation, so its computation rules
`T.rec_ctorᵢ` hold propositionally and not by `rfl`.
