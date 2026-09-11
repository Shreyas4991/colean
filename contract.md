# Contract for `codata`

```
codata T
  | ctor₁ …
  | ctor₂ …
```

The constructor list defines a functor `F`, the sum of the constructors' argument types with `T`
replaced by a variable. `F.map` is its action on functions, `F.Rel` its lifting to relations
(same constructor, equal non-recursive fields, related recursive fields). The command produces:

1. The type `T`.
2. Destructor `dtor : T → F T`.
3. Corecursor `corec : (S → F S) → S → T`.
4. `dtor_corec : ∀ c x, dtor (corec c x) = F.map (corec c) (c x)`.
5. `bisim : (∀ x y, R x y → F.Rel R (dtor x) (dtor y)) → ∀ x y, R x y → x = y`.

This is the minimal interface: `(T, dtor)` is a final coalgebra of `F`. Constructors
`ctor : F T → T` with `dtor_ctor` and `corec_eq : corec c x = ctor (F.map (corec c) (c x))`
will be provided later, derived from `dtor` and `dtor_corec` (`ctor := corec (F.map dtor)`).
