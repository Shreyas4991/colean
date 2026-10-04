# Plan: `codata` and `data` as subtypes of `Raw`

## Where we are

`Subtypes/Codata.lean`: the generic theory, for indexed polynomial signatures (a plain type is
a family over `Unit`), the contract (`contract.md`, plain and indexed sections), and the derived
layer. `Subtypes/CodataCmd.lean`: the `codata` command. `Subtypes/Data.lean` and
`Subtypes/DataCmd.lean`: the inductive dual. `Subtypes/Test/`: one test per type.
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

## 2. `data`: the inductive dual — DONE

Contract in `contract.md` (`ctor`, `fold`, `fold_ctor`, `induction` with `F.All` defined from
`F.map`). `Subtypes/Data.lean`: the least fixpoint, the recursor by well-founded recursion on
the immediate-child relation, the transport theorems, `Data.Contract` and its derived layer.
`Subtypes/DataCmd.lean`: the command, sharing the analysis and the generators of `F`, the
signature, the isomorphism, the constructors and `casesOn` with `codata`.

DONE:

* the same syntax and scope as `codata`: parameters, indices, telescopes (`Test/FinList.lean`,
  `Test/FinTree.lean`, `Test/Nat.lean`, `Test/FinVec.lean`, `Test/LeT.lean`, `Test/WType.lean`);
* `T.fold` for families in any universe, `T.fold_ctor`, `T.fold_ctorᵢ`, `T.fold_eq`,
  `T.fold_unique`; derived `T.dtor` with `dtor_ctor`, `ctor_dtor`; constructors, injectivity,
  disjointness, `casesOn` as for `codata`;
* the dependent recursor `T.rec`, one minor premise per constructor with induction hypotheses,
  registered as the `induction` eliminator, with computation rules `T.rec_ctorᵢ` (propositional,
  by design);
* isomorphisms with the native types: `List`, a native tree, `Nat`, Mathlib's `WType`.

NOT DONE:

* injectivity for constructors with dependent binders (`sup (a : α) (f : β a → W α β)`): the
  `HEq` form, together with the implicit-binder case in section 5.

## 3. Mutual types — NOT DONE

Mutual `codata … with …` blocks: one signature with a sum of shapes and an index picking the
type (which is 1. again, with the type name as the index). The generated `F` becomes a family
over the block, and `mutual_induct`-style principles come out of the indexed `bisim`.

Mixed inductive/coinductive blocks are rejected by Lean's fixpoint machinery (the joint operator
is not monotone in the mixed order); support them as nested fixpoints, as in the hand-written sketch `Sketch/Mutual.lean` on the
`progress` branch:
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
2. `data`: DONE (leftovers listed above).
3. Mutual blocks via the index trick; then mixed blocks as nested fixpoints.
4. Nested types through containers.
5. Surface items, as they become blocking.
