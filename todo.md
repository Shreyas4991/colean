# Deferred

## The family's universe should not depend on the index universe

Today `Signature.Cotype σ : I → Type (max w u v)` with `I : Type w`: the index enters the
universe of the family, so `codata Foo : Type 1 → Type` is refused (the family is in `Type 1`,
and the command says so at the sort), whereas `inductive Foo : Type 1 → Type` is fine. The data
universes `u`, `v` are necessary (as for `inductive`); `w` is not.

Cause: the tree alphabet is `Lbl := Σ i, Shape i`, and `Raw Idx Lbl` lives where its alphabet
lives. The index is only *needed* in `IsWf` (a `Prop`, so it may mention `Σ i, Shape i` at any
size) and in `dtorC`, which computes the shape from the root label (a function, whose universe
does not affect `T`).

Fix, without touching the six generated lemmas: parametrise the generic layer by a small
alphabet. A signature carries `L : Type u'`, `label : (Σ i, Shape i) → L`,
`unlabel : L → Option (Σ i, Shape i)` with `unlabel (label x) = some x`, and likewise a small
position alphabet `B₀ : L → Type v'` with its embedding. `encode` writes `label ⟨i, s⟩` at the
root, `IsWf i t` says the root label unlabels to a shape at `i` with well-formed children, and
`Cotype σ i : Type (max u' v')`. The present layer is the case `L := Σ i, Shape i`,
`label := id`.

For a `codata` declaration the small alphabet is the unindexed "constructor plus data" type and
its positions (this is how Lean represents inductive families: data stored, index computed);
the command generates `Shape₀`, `B₀`, `label`, `unlabel` by pattern matching and the law by
`cases` then `rfl`, and keeps the indexed `Shape`, `B`, `toC`, `ofC` and their lemmas as they
are, so index unification by `cases` is preserved. Do not use the unindexed shapes *as* the
container (`{s // out s = i}`): that trades index unification for index equations and casts in
the generated proofs, and for index expressions that do not reduce (`n - 1`, `i + 1` in `Fin`)
the uniform scripts stop working.

Worth doing only if a large index with small data shows up; for coinductive types the large
index is usually stored as data too, which forces the universe anyway.

## A single proposition as index

`Signature.I : Type w`, so `codata T : (h : 0 < 5) → Type` is rejected, while proofs among
several indices are fine through the `PSigma` packing. Switching to `I : Sort w` is not the
one-line change it looks like: `Σ' i, Shape i` then lives in `Sort (max 1 w (u + 1))`, which
Lean cannot unify with the `Type _` that the alphabet of `Raw` must be (no level subtraction).
The route is at the command level: detect a lone `Prop` index by elaborating the index type,
and pack it as `PLift p` (or as `PSigma` with `Unit`). Since a `Prop`-valued index is
proof-irrelevant, such a family is a plain type with a precondition, so this is a convenience
only.

## Generate `PolyIso` on demand

Today instances are generated only for `data` and `codata`, when they are declared. A plain
`structure` or `inductive` used as a leaf gets the missing-instance error, even when it is
obviously polynomial:

```
structure Box (X : Type u) where
  val : X

codata T
  | mk (x : Box T)
```

Generate the instances when a declaration needs them instead: when `checkLeaf` finds no instance
for a leaf whose head is a user-defined structure or inductive, derive them there and go on. The
definition has to be read from the environment, at the `Expr` level, since it may come from another
file with other `open`s. If generation fails, the error stays the missing-instance one. Two
independent files may then generate the same instance, so the names have to be unique per module.
