# Plan: `codata` and `data` as subtypes of `Raw`

## Where we are

`Subtypes/Codata.lean` proves the contract (`T`, `dtor`, `corec`, `dtor_corec`, `bisim`) once, for
the container `σ.Obj X = { shape : σ.Shape, child : σ.B shape → X }` of any polynomial signature,
plus the derived layer (`ctor`, `corec_eq`, `corec_unique`, `casesOn`, injectivity, disjointness).
`Subtypes/CodataCmd.lean` turns a `codata` declaration into a signature, an isomorphism with
`σ.Obj`, and instantiations of those theorems. Supported: parameters, explicit and implicit
binders, plain recursive arguments, recursive arguments under `I → T` with `I` depending on the
constructor's data. Not supported: indices, mutual and nested types, `data`.

Design rules, fixed by discussion:

* the theory is stated as theorems and instantiated; the command proves by tactic only the six
  lemmas about the generated inductive `F`;
* `corec` is universe-polymorphic in the state, no `ULift` for users;
* noncomputable is fine; do not complicate anything to keep computability.

## 1. Indices

Target syntax, as for `inductive`:

```
codata Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)
```

Generic layer. A signature becomes indexed: an index type `I`, shapes `Shape : I → Type u` (a
constructor's data determines the result index, so shapes are a family), and positions with their
own index, `B : (i : I) → Shape i → Type v` and `idx : ∀ i s, B i s → I`. The container is
`σ.Obj (X : I → Type) (i : I) = { shape : Shape i, child : (b : B i shape) → X (idx b) }`. The
encoding stays in one `Raw` with labels `Σ i, Shape i` and path indices `Σ i s, B i s`; `IsWf`
becomes `I → Raw → Prop`, a greatest fixpoint over indexed predicates (`coinductive_fixpoint`
supports this), and `Cotype σ i := {t // IsWf i t}`. `dtorC`, `corecC` (for `S : I → Type` and
`c : ∀ i, S i → Obj S i`), `dtorC_corecC`, `bisimC` (for `R : ∀ i, T i → T i → Prop`) go through
with the index threaded; the `∃ s c c'` form of `Obj.Rel` keeps working because both sides share
the shape and hence the index.

Command. Parse the result type `: I₁ → … → Type u` and each constructor's result type
`T params idx`, and the index of each recursive argument `T params j` or `J → T params j`.
The generated `F` is `F params (X : I → Type _) : I → Type _`, with `F.map`, `F.Rel` and the
laws indexed; `T.Shape params : I → Type _` and `T.B params : (i : I) → T.Shape params i → Type _`
with `idx`; `toC`, `ofC`, the three laws, and the contract, all indexed. The uniform proofs are
unchanged in shape (`cases` on shapes, on the relation, on positions, `solve_by_elim`).

Tests: `Vec`, a coinductive family (e.g. streams indexed by a state machine or `CoVec : ℕ∞ → Type`),
and the sketches in `Sketch/Vec.lean` as a reference.

Open point: non-uniform parameters (`Nest α` with `Nest (α × α)` inside) are indices in disguise;
decide whether to support them by promoting them to indices as Lean does.

## 2. `data`: the inductive dual

Contract for `data`, to be written in `contract.md` when we start: `T`, `ctor : F T → T`,
`rec : (F S → S) → T → S`, `rec_ctor : rec a (ctor y) = a (F.map (rec a) y)`, and induction
(`∀ t, (∀ y, F.All motive y → motive (ctor y)) → motive t`). Derived: `dtor`, `ctor_dtor`,
`dtor_ctor`, uniqueness of `rec`, `casesOn`, injectivity, disjointness.

Encoding: the same `Raw`, the same `encode`, and `IsWf` by `inductive_fixpoint` instead of
`coinductive_fixpoint`. The recursor is the place where the encoding costs something: the
predicate is a `Prop`, so `rec` into `Type` goes through well-founded recursion on the
"immediate child" relation, whose well-foundedness is proved by `IsWf.induct` (see
`Sketch/FinList.lean`). Consequences to accept: `rec_ctor` is propositional, and `rec` does not
reduce by `rfl`.

Shared code: `Signature`, `Obj`, `encode`, `dtorC` and the transport machinery are reused; only
the fixpoint, the recursor and its theorems are new. Keep both commands in one file structure
(`Data.lean` next to `Codata.lean`, `DataCmd.lean` reusing the generators of `CodataCmd.lean`).

Tests: `FinList`, `FinTree`, `Nat'`, an indexed one once 1. is done, and the isomorphisms with
the native inductives from the sketches.

## 3. Mutual types

Mutual `codata … with …` blocks: one signature per type, or one signature with a sum of shapes
and an index picking the type (which is 1. again, with the type name as the index). The second is
less work and makes mixed blocks possible; do that. The generated `F` becomes a family over the
block, and `mutual_induct`-style principles come out of the indexed `bisim`.

Mixed inductive/coinductive blocks are rejected by Lean's fixpoint machinery (the joint operator
is not monotone in the mixed order); support them as nested fixpoints, as in `Sketch/Mutual.lean`:
the inner predicate is parameterised by the outer one and needs a `@[partial_fixpoint_monotone]`
lemma, which the command can generate uniformly.

## 4. Nested types

Nested occurrences through other types (`List (T α)`, another `codata`): reduce to the position
family by giving the container of the nesting type, i.e. a `Signature` for `List` with its own
`toC`/`ofC`; this is the QPF-style "nesting through a container". Needs a registry of containers
for the types allowed in nested positions (`List`, `Option`, products, previously declared
`codata`/`data`) and their `map`/`Rel` laws. Defer until 1. and 2. exist.

## 5. Surface

* Full `inductive` syntax: `where`, doc comments on constructors, `universe`-free `Type*`,
  auto-bound implicit parameters, `deriving` where meaningful (`Inhabited`, `Nonempty`).
* Injectivity lemmas for constructors with implicit binders, in `injEq` form with `HEq`.
* `F.Rel` introduction lemmas as simp lemmas, and a `bisim` variant "up to equality" (children
  related or equal), derived once in `Codata.lean` from `bisim` and `rel_map`.
* Corecursive function definitions by pattern matching (`codef f : … := … f …` compiled to
  `corec` with a guardedness check), later; until then users write `corec` with an explicit state.
* Naming review of the generated declarations before anything depends on them.

## Order

1. Indices (generic layer first, then command, tests `Vec` and a coinductive family).
2. `data`, reusing the indexed layer.
3. Mutual blocks via the index trick; then mixed blocks as nested fixpoints.
4. Nested types through containers.
5. Surface items, as they become blocking.
