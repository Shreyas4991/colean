# Plan: `codata` and `data` as subtypes of `Raw`

## Where we are

The layout follows `architecture.md`: `Framework.lean` (the contracts and what follows from
them), `PolyIso.lean` (the user interface for nesting), `Model/` (`Cotype`, `Intype`, `Occ`,
`Poly`: the fixpoints on `Raw`, occurrence structures, fixpoints as polynomial functors),
`Syntax.lean` (the command syntax), `Gen/` (the generators by step, on `Expr`: `Decl`, `Occ`,
`Ctx`, `Front`, `Functor`, `Signature`, `Iso`, `Model`, `Rel`, `Framework`, `Extras`, `Surface`,
`Derive`, the pipeline `Command`, and `Mixed` for mixed blocks), `CodataCmd.lean`/`DataCmd.lean` (the commands),
`MutualCmd.lean` (blocks, mixed blocks), all directly under `Colean/`; the tests are the separate library
`ColeanTest/`, one test per type; `Sketch/` holds hand-written experiments, a library outside the
default build, which need not compile. The root modules `Colean.lean` and `ColeanTest.lean`
import everything and are both default targets, so `lake build` checks it all. The contract is
`contract.md`; `todo.md` holds deferred items that are not features.

The commands elaborate the user's declaration as `inductive` does and generate everything as
`Expr`s, in one `TermElabM` run (`architecture.md`, "The generators"). Until 2026-11 they
generated syntax; the old generators are in the git history (`bc6498d`).

Design rules, fixed by discussion:

* the theory is stated as theorems and instantiated; the command proves by tactic only the laws
  of the inductives it generates (`F`, and the layer of step 5);
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

* any number of indices, dependent telescopes, propositions as indices (`ColeanTest/Cyc.lean`,
  `ColeanTest/Bounded.lean`);
* arbitrary index expressions in results and recursive arguments, including bare and repeated
  binders (`ColeanTest/Diag.lean`), and result indices that are not patterns, `T (n * 2)`,
  `T (!b)` (`ColeanTest/ResultIndex.lean`);
* recursive arguments under any telescope of arrows, dependent or curried, with the index
  depending on the bound variables (`ColeanTest/Tele.lean`);
* `casesOn` as the `cases` eliminator, refining the indices; injectivity and disjointness lemmas
  where they are well-typed; `motive` and `S` usable as named arguments.

NOT DONE, in the front end:

* doc comments on `codata` declarations.

Instance and strict-implicit binders in constructors, and `∀ x, T (f x)` as a spelling of a
telescope, came with the elaboration of the declaration on `Expr` (2026-11).

NOT DONE, and not planned:

* a proof binder that occurs only inside index terms and in no field (cannot be recovered);
* non-uniform parameters (`Nest α` with `Nest (α × α)` inside): Lean's `inductive` rejects them
  too; the user writes the parameter as an index, at the same universe cost as in Lean;
* the family's universe not depending on the index universe: deferred, see `todo.md`.

## 2. `data`: the inductive dual — DONE

Contract in `contract.md` (`ctor`, `fold`, `fold_ctor`, `induction` with `F.All` defined from
`F.map`). `Model/Intype.lean`: the least fixpoint, the recursor by well-founded recursion on
the immediate-child relation, the transport theorems, `Data.Contract` and its derived layer.
`DataCmd.lean`: the command, sharing the analysis and the generators of `F`, the
signature, the isomorphism, the constructors and `casesOn` with `codata`.

DONE:

* the same syntax and scope as `codata`: parameters, indices, telescopes
  (`ColeanTest/FinList.lean`, `ColeanTest/FinTree.lean`, `ColeanTest/Nat.lean`,
  `ColeanTest/FinVec.lean`, `ColeanTest/LeT.lean`, `ColeanTest/WType.lean`);
* `T.fold` for families in any universe, `T.fold_ctor`, `T.fold_ctorᵢ`, `T.fold_eq`,
  `T.fold_unique`; derived `T.dtor` with `dtor_ctor`, `ctor_dtor`; constructors, injectivity,
  disjointness, `casesOn` as for `codata`;
* the dependent recursor `T.rec`, one minor premise per constructor with induction hypotheses,
  those of nested arguments by membership (`PolyIso.Mem`, `IPolyIso.Mem`), registered as the
  `induction` eliminator, with computation rules `T.rec_ctorᵢ` (propositional, by design);
* isomorphisms with the native types: `List`, a native tree, `Nat`, Mathlib's `WType`.

NOT DONE:

* injectivity for constructors with dependent binders (`sup (a : α) (f : β a → W α β)`): the
  `HEq` form, together with the implicit-binder case in section 5.

## 3. Mutual types — DONE

`MutualCmd.lean`: Lean's own `mutual … end` syntax around `codata` or `data`
declarations; the block is elaborated as Lean's mutual `inductive` (shared parameters, the types
as local variables), and is one family over the inductive `Blk.Ix`, with a constructor per type
whose arguments are the indices of that type, generated by the single-type pipeline as a family
with one index. Per type: the type, the
constructors and their lemmas, `casesOn` as the `cases` eliminator, aliases `corec`, `bisim`,
`fold`, and for `data` the recursor `rec` with a motive per type and its rules `rec_cᵢ`;
block-level `corec`, `bisim`, `rec` with states, relations and motives over `Ix`
(`ColeanTest/MTree.lean`, `ColeanTest/MRose.lean`, `ColeanTest/EvenOdd.lean`,
`ColeanTest/MutualIx.lean`).

DONE:

* uniform blocks, `codata` or `data`, with parameters and indices, and constructor names shared
  by several types (qualified in the block-level inductives and the recursors' minor premises
  only);
* types of one block with different indices, as Lean allows;
* induction over a block by `induction x` for `x : Blk m i`, with per-constructor alternatives;
  Lean's `induction` tactic refuses mutual inductives, so this is not less than `inductive`;
* induction per type, `induction t using Tₘ.rec (motive_2 := …)`, with recursors in the shape
  of Lean's mutual ones (a motive per type, the minor premises of the block) and their rules
  `Tₘ.rec_cᵢ`; the block-level rules are `Blk.rec_cᵢ`.

NOT DONE:

* nothing else planned. A `mutual` block mixing `data` and `codata` is rejected; mixed blocks are
  section 5, `mixed_mutual`.

## 4. Nested types — DONE; instances for declared types DONE

`PolyIso.lean` is the interface: `PolyIso F Sh Pos` (`F X ≃ Σ sh, Pos sh → X`) and `PolyMap F F'`
(the intended action between two instantiations, with naturality), together an isomorphism of
functors, and `IPolyIso`, `IPolyMap` for functors on families. The command requires both at
every named type constructor. `Model/Occ.lean` keeps the bundled structures `Occ`/`IOcc`,
internal to the command, with the combinators `const`, `hole`, `prod`, `sum`, `pi`, `piP`,
`sigma`, `comp` (and `IOcc.ofOcc`, `reidx`, `compC`, `compI`, `Occ.ofI`, `Occ.compI`), their
laws, and the leaves `Occ.ofIso F`. The command builds the structure of every nested argument
by recursion on its elaborated type (`Gen/Occ.lean`), with instance search only at named type
constructors; an instance at one universe only fixes the universe of the type. `Signature` has
no erased shapes.

Defining a type and constructing its instance are decoupled (2026-11-06): the generated
structures `T.occ`, `T.Sh`, `T.Pos`, the lemmas `T.map_c`, `T.rel_c`, the erased shapes, and
`Model/Param.lean` are gone. The old version is in the git history. Instances are generated
after the type, in a separate step that cannot fail the declaration (`Gen/Derive.lean`), from
the contract, by the generic theorems of `Model/Poly.lean`.

DONE:

* nested arguments of any shape built from occurrences by `×`, `⊕`, `(a : A) → …` (constant
  domain, a proposition allowed), `(a : A) × …`, and named constructors, at any depth: `T × T`,
  `A → List T`, `Option (T × T)`, `T ⊕ A`, `(n : ℕ) × (Fin n → T)`, `0 < n → List T`, occurrences
  at several indices in one argument (`Chain n × Chain (n + 1)`); for `codata` and `data`
  (`ColeanTest/OccNest.lean`, `ColeanTest/Rose.lean`, `ColeanTest/FinRose.lean`);
* any type constructor with user instances, plain or on families, in `codata`, `data` and
  mutual blocks, a declared type included (`ColeanTest/Nest.lean`, `ColeanTest/OccNest.lean`);
* generated instances for a single `data` or `codata` without indices, over all parameters that
  may vary, composed with constants and with the identity, so `E (List T) (Option T)`, `E Nat T`
  and `E T T` come from one instance, and a named constructor may take the hole in several
  arguments (`ColeanTest/Derive.lean`); `data` nests through `codata` and the other way round;
* generated instances for indexed families, at every index (an argument of the instance), and
  for the types of `mutual` blocks, at their index of the block, presented per block over the
  block's index without the parameters that vary (`Blk.Poly.Ix`): `Vec T 3`, `Vec (T n) n`,
  `Ping T`, `Ev T 2` (`ColeanTest/DeriveIdx.lean`, 2026-11-09). The theory is the plain one on the
  total spaces (`Model/Poly.lean`).

NOT DONE:

* generating instances on demand, for user-defined structures and inductives (`todo.md`);
* generated instances for a type of a block whose nested argument has positions at the block's
  index only after cases on them (`Ping × Pong`, `Ping × Nat`): the step fails with its warning.
  A fix would cast the children along a generated equation of the indices, or reindex the
  trees of shapes along `Blk.Poly.ixIn`;
* `IPolyIso` instances, where the varying parameter is itself a family;
* a field mentioning two parameters that may vary (`p : α × β`): both then count as constant;
* holes at different indices in several arguments of a named constructor (`Pair (T i) (T j)`);
* constructor-level lemmas for the generated map, and `simp` lemmas for membership through
  generated instances: `PolyFix.d_map` states the map on layers only;
* in a family or a block, a nested argument through a product or a sum gets the hypothesis by
  `IPolyIso.Mem` even when all its occurrences are at one index (`Own × Nat` in a block): its
  positions are at that index only after cases on them;
* `PolyMap`/`IPolyMap` instances for the composites across plain functors and functors on
  families (`fun X => G fun _ => X`, `fun X => G fun k => H k X`, reindexing): their
  `PolyIso`/`IPolyIso` instances exist;
* `rel_*` characterisations of `Occ.Rel` through `prod`, `pi`, `comp` as iffs (only the
  introductions exist), and user-facing `T.map`/`T.Rel` abbreviations.

## 5. Mixed blocks — DONE, on top of nesting (2026-11-11)

A block with `data` and `codata` declarations is a nested fixpoint, and a cyclic system has
several nested solutions, so the block says the order: `mixed_mutual … end`, the textual order,
the first outermost (`MutualCmd.lean`, `Gen/Mixed.lean`, `contract.md`). Runs of one kind are
declared from the innermost out, each by the pipeline: the runs inside the first open, under
`Tₘ.Open`, with a parameter per outer run they need, through which the runs outside nest by the
instances of step 5; then the closed types `Tₘ := Tₘ.Open params (outer types)`, abbreviations,
as soon as the first run's types exist, with which the first run is stated, and the interface of
each run inside restated at them. The design and the history before 2026-11 are in the git
history (`bc6498d`).

DONE:

* any number of runs, of one type or of a block, inner runs with indices, parameters and
  section variables (`ColeanTest/Mixed.lean`, `MixedOrder.lean`, `MixedRuns.lean`,
  `MixedBlock.lean`, `MixedIdx.lean`, `MixedParam.lean`);
* the closed types with the whole interface of a standalone declaration, the statements of the
  outer runs with them, and the hypotheses of the recursors through inner runs by membership in
  the closed types (`Membership` instances, with the `simp` lemmas `Tₘ.mem_c`);
* `simp` through the nesting: the closed constructors are abbreviations of the open ones, so the
  `simp` lemmas of step 5 (`Tₘ.Open.Poly.map_c`, `mem_c`) apply to them;
* a block of one kind is a `mutual` block, with a warning; `mutual` rejects a mixed block.

NOT DONE:

* outer runs with indices, or of several types: the open types' parameter is then a family, and
  nesting through it needs `IPolyIso` instances, not generated (section 4); the block stops at the
  error of step 5 (`ColeanTest/MixedRejected.lean`);
* a field mentioning an outer type together with the run's own type (`p : Tree α × Forest α`):
  step 5 does not generate instances in a parameter used so (gap 2 of section 4); the same error;
* with parameters, a run passing an outer type on to a run further inside (A ⊃ B ⊃ C, `C`
  mentioning `A`): the middle run's field `c : C.Open α X` has no recursion of `B`, but it
  mentions two parameters, `α` and `X`, and step 5 drops both although only `X` needs to vary
  (gap 3 of section 4); the same error. Several parameters in one field would fix it, and so
  would letting step 5 keep the block's parameters constant. Without parameters the block is
  accepted;
* the functor of an outer run at its state, and the rules mapping through inner runs
  (`Tree.F.node : α → Forest.Open α X → Tree.F α X`, `T.fold_c`), mention the open types: they are
  the inner types at a state, with no closed form;
* membership instances for members of an outer run with indices or of several types (which fail
  anyway); the hypotheses through a composite (`List (Forest α)`) stay by `PolyIso.Mem`, which
  `simp` turns into membership in the closed types;
* instances for the closed types in their declared parameters (the open types have them, the
  closed ones would need the outer types' instances, which a mixed outer run does not get).

## 6. Surface — NOT DONE

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
3. Mutual blocks: DONE (leftovers listed above).
4. Nested types: DONE, with generated instances for single types, families and blocks.
5. Mixed blocks: DONE (leftovers listed above).
6. Surface items, as they become blocking.
