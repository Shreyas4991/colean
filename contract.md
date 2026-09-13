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
