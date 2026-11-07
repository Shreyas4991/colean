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
positions carry an index of the family). It is built by recursion on the elaborated type, from
a constant, the occurrence, products, sums, functions and dependent pairs over constant types,
and named type constructors, whatever their spelling. `F` keeps the argument type as a field, `F.map` acts on it
through the structure, and the canonical `F.Rel` relates nested fields with the same shape and
related contents (`Occ.Rel`).

A named type constructor `G` is the user's part of the contract (`PolyIso.lean`):

1. `PolyIso G Sh Pos`: `G` is presented as a polynomial functor, `G X ≃ Σ sh : Sh, (Pos sh → X)`
   for every `X`.
2. `PolyMap G G'`: the intended action `G X → G' Y` on functions, between two instantiations of
   `G`, with the naturality of the presentation.

Together they are an isomorphism of functors. The action is a class on two instantiations
because the state of `corec` lives in any universe, so `F.map` crosses universes, which Lean's
`Functor` cannot state, and naturality in each universe separately does not determine the map
between them. The command requires both instances. It follows that the map on such a field is
the intended one (`Occ.map_ofIso`): `List.map` on lists (`Occ.map_list`), and componentwise on
pairs and the other built-in forms (`Occ.map_prod`, …). For a functor on families the classes
are `IPolyIso` and `IPolyMap`, with `G X ≃ Σ sh, (q : Pos sh) → X (pidx sh q)`.

A declared type gets these instances when it can, in a separate step after its declaration
(`Gen/Derive.lean`): for `fun X => T (H₁ X) … (Hₙ X)` over the parameters that may vary, with the
`Hᵢ` themselves instances, so that one instance covers every use, constants and the identity
being instances too. If that step fails, it logs a warning and leaves no trace: the type is
declared as usual and can still be given instances by hand. The step works from the contract:
a value is a tree of shapes with the contents of its slots (`Model/Poly.lean`), and the map on
the parameter is the structural one (`PolyFix.d_map`). For now it covers a single type without
indices.


# Mutual blocks

```
mutual
data Even : Nat → Type
  | zero : Even 0
  | succ {n : Nat} (o : Odd n) : Even (n + 1)
data Odd : Nat → Type
  | succ {n : Nat} (e : Even n) : Odd (n + 1)
end
```

A block of `data` declarations, or of `codata` declarations, is one family `Even_Odd` over the
inductive `Even_Odd.Ix`, with a constructor per type whose arguments are the indices of that type
(`Ix.Even n`, `Ix.Odd n`), so the contract is the one of indexed families, over `I = Ix`. The types
are `Even n := Even_Odd (.Even n)`. All types of a block have the same parameters, on which `Ix`
may depend. Their indices may differ, and a type may have none. As for any family, the family
lives in a universe at least that of `Ix`, so the largest index of the block counts for every type.


# Mixed blocks

A block with `data` and `codata` declarations is a nested fixpoint, and a cyclic system has
several nested solutions (the trees outside the forests are the finitely branching infinite
trees, the forests outside the trees the finite ones), so such a block would have to state the
order. A `mutual` block may not mix the two kinds. The `mixed_mutual` command, which nested the
declarations in the order written, is removed, pending a redesign.


# Recursors

Beyond the contract, the command generates the dependent recursor `T.rec` into any `Sort`, with
one minor premise per constructor carrying an induction hypothesis for each recursive argument.
It is derivable from the contract (a fold into `Σ t, motive t`, with `induction` showing the
first component is the identity), but the command takes it from the encoding, by well-founded
recursion on the immediate-child relation, so its computation rules `T.rec_ctorᵢ` hold
propositionally and not by `rfl`.
