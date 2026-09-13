# Plan: `codata` and `data` as subtypes of `Raw`

## Where we are

`Subtypes/Codata.lean`: the generic theory, for indexed polynomial signatures (a plain type is
a family over `Unit`), the contract (`contract.md`, plain and indexed sections), and the derived
layer. `Subtypes/CodataCmd.lean`: the `codata` command. `Subtypes/Test/`: one test per type.
`Subtypes.lean` imports everything and is the only import of the root module, so `lake build`
checks it all. `todo.md` holds deferred items that are not features.

Design rules, fixed by discussion:

* the theory is stated as theorems and instantiated; the command proves by tactic only the six
  lemmas about the generated inductive `F`;
* `corec` is universe-polymorphic in the state, no `ULift` for users;
* noncomputable is fine; do not complicate anything to keep computability.

## 1. Indices — DONE

Syntax, as for `inductive`:

```
codata Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)
```

DONE:

* any number of indices, dependent telescopes, propositions as indices (`Test/Cyc.lean`,
  `Test/Bounded.lean`);
* arbitrary index expressions in results and recursive arguments, including bare and repeated
  binders (`Test/Diag.lean`);
* recursive arguments under any telescope of arrows, dependent or curried, with the index
  depending on the bound variables (`Test/Tele.lean`);
* `casesOn` as the `cases` eliminator, refining the indices; injectivity and disjointness lemmas
  where they are well-typed; `motive` and `S` usable as named arguments.

NOT DONE, all in the front end (syntax analysis only):

* instance and strict-implicit binders in constructors;
* `∀ x, T (f x)` as an alternative spelling of a telescope;
* doc comments on `codata` declarations.

NOT DONE, and not planned:

* a proof binder that occurs only inside index terms and in no field (cannot be recovered);
* non-uniform parameters (`Nest α` with `Nest (α × α)` inside): Lean's `inductive` rejects them
  too; the user writes the parameter as an index, at the same universe cost as in Lean;
* the family's universe not depending on the index universe: deferred, see `todo.md`.

## 2. `data`: the inductive dual — NOT DONE

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

Tests: `FinList`, `FinTree`, `Nat'`, an indexed one, and the isomorphisms with the native
inductives from the sketches.

## 3. Mutual types — NOT DONE

Mutual `codata … with …` blocks: one signature with a sum of shapes and an index picking the
type (which is 1. again, with the type name as the index). The generated `F` becomes a family
over the block, and `mutual_induct`-style principles come out of the indexed `bisim`.

Mixed inductive/coinductive blocks are rejected by Lean's fixpoint machinery (the joint operator
is not monotone in the mixed order); support them as nested fixpoints, as in `Sketch/Mutual.lean`:
the inner predicate is parameterised by the outer one and needs a `@[partial_fixpoint_monotone]`
lemma, which the command can generate uniformly.

## 4. Nested types — NOT DONE

Nested occurrences through other types (`List (T α)`, another `codata`): reduce to the position
family by giving the container of the nesting type, i.e. a `Signature` for `List` with its own
`toC`/`ofC`; this is the QPF-style "nesting through a container". Needs a registry of containers
for the types allowed in nested positions (`List`, `Option`, products, previously declared
`codata`/`data`) and their `map`/`Rel` laws. Defer until 2. exists.

## 5. Surface — NOT DONE

* Full `inductive` syntax: `where`, doc comments on the declaration and on constructors,
  `universe`-free `Type*`, auto-bound implicit parameters, `deriving` where meaningful
  (`Inhabited`, `Nonempty`).
* Injectivity lemmas for constructors with implicit binders, in `injEq` form with `HEq`.
* `F.Rel` introduction lemmas as simp lemmas, and a `bisim` variant "up to equality" (children
  related or equal), derived once in `Codata.lean` from `bisim` and `rel_map`.
* Corecursive function definitions by pattern matching (`codef f : … := … f …` compiled to
  `corec` with a guardedness check), later; until then users write `corec` with an explicit state.
* Naming review of the generated declarations before anything depends on them.

## Order

1. Indices: DONE (front-end leftovers listed above).
2. `data`, reusing the indexed layer.
3. Mutual blocks via the index trick; then mixed blocks as nested fixpoints.
4. Nested types through containers.
5. Surface items, as they become blocking.
