# Plan: `codata` and `data` as subtypes of `Raw`

## Where we are

The layout follows `architecture.md`: `Framework.lean` (the contracts and what follows from
them), `Model/` (`Cotype`, `Intype`, `Occ`, `Param`: the fixpoints on `Raw`, occurrence
structures, the structure in a parameter), `Cmd/` (the generators by step: `Analysis`,
`Functor`, `Model`, `Framework`, `Extras`, `Surface`), `CodataCmd.lean`/`DataCmd.lean` (the
pipelines and commands), `MutualCmd.lean` (blocks), `Test/` (one test per type), `Sketch/`
(hand-written experiments, not built), all directly under `Colean/`. The root module
`Colean.lean` imports everything, so `lake build` checks it all. The contract is `contract.md`; `todo.md` holds
deferred items that are not features.

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
`F.map`). `Model/Intype.lean`: the least fixpoint, the recursor by well-founded recursion on
the immediate-child relation, the transport theorems, `Data.Contract` and its derived layer.
`DataCmd.lean`: the command, sharing the analysis and the generators of `F`, the
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

## 3. Mutual types — DONE

`MutualCmd.lean`: Lean's own `mutual … end` syntax around `codata` or `data`
declarations; the block is one family over the enumeration `Blk.Which` of its types, prepended
to the index telescope, and elaborated by the single-type pipeline. Per type: the type, the
constructors and their lemmas, `casesOn` as the `cases` eliminator, aliases `corec`, `bisim`,
`fold`; block-level `corec`, `bisim`, `rec` with states, relations and motives over `Which`
(`Test/MTree.lean`, `Test/MRose.lean`, `Test/EvenOdd.lean`).

DONE:

* uniform blocks, `codata` or `data`, with parameters and indices, and constructor names shared
  by several types (qualified in the block-level inductives only);
* induction over a block by `induction x` for `x : Blk m i`, with per-constructor alternatives;
  Lean's `induction` tactic refuses mutual inductives, so this is not less than `inductive`.

NOT DONE:

* types of one block with different index telescopes (Lean allows them): the block index would
  be a dependent pair `(m : Which) ×' Ix m`;
* nothing else planned. Mixed inductive/coinductive blocks are section 5: today a mixed
  `mutual` block is accepted with the fixed reading "codata outer" (`Test/Mixed.lean`); it will
  be rejected once `mixed_mutual` exists.

## 4. Nested types — DONE, switched to occurrence structures (2026-09-17)

`Model/Occ.lean`: the bundled structures `Occ Sh Pos G` (`G X ≃ Σ sh, Pos sh → X`) and
`IOcc Sh Pos pidx G` (positions carry an index of the family), their laws (`toC`/`ofC`, `map`
and `Rel` between two structures at different universes, `rel_map`, `rel_intro`, `rel_ofC`,
`exists_map_of_rel`), the combinators `const`, `hole`, `prod`, `sum`, `pi`, `piP`, `sigma`,
`comp` (and `IOcc.ofOcc`, `reidx`, `compC`, `compI`, `Occ.ofI`, `Occ.compI` across the two
kinds), the leaves `Occ.list`, `Occ.option`, `Occ.array` with the registry classes
`OccLeaf`/`IOccLeaf`, and the computation lemmas `map_prod`, `map_pi`, `map_comp`, `map_list`,
…, `forall_toC_*`, `rel_hole_intro`, `rel_prod_intro`. The command (`occTreeOf`, `occTermOf`,
`classify`) builds the structure of every nested argument by recursion on the syntax of its
type, with instance search only at named type constructors; `Kind.occ`/`PKind.occ` carry the
tree, the structure term, its shapes, positions and position index; everything else is as
before (the shape of the argument is data of the constructor, its positions are recursive
positions, `toC`/`ofC` go through the structure). The `Container`/`IContainer` classes, the
whole-expression instance search and the composition instances are gone.

DONE:

* nested arguments of any shape built from occurrences by `×`, `⊕`, `(a : A) → …` (constant
  domain, a proposition allowed), `(a : A) × …`, and named constructors (`List`, `Option`,
  `Array`, the declared types), at any depth: `T × T`, `A → List T`, `Option (T × T)`,
  `T ⊕ A`, `(n : ℕ) × (Fin n → T)`, `0 < n → List T`, occurrences at several indices in one
  argument (`Chain n × Chain (n + 1)`); for `codata` and `data` (`Test/OccNest.lean`,
  `Test/Rose.lean`, `Test/FinRose.lean`);
* any type constructor with an `OccLeaf`/`IOccLeaf` instance written by hand;
* the structure generated for every `data`/`codata` (and every type of a mutual block, and the
  block family) whose last parameter is a type `α` or a family `X : J → Type u` used only at
  parameter positions, now including nested ones of any shape (`(p : α × α)`, `(as : List α)`):
  `T.Shape₀`, `T.P`, `T.shapeEquiv`, `T.psig`, `T.Sh`, `T.Pos`, `T.occ`, `T.instOccLeaf` (and
  `T.pidx`, `T.posIdx` for a family), the constructor-level lemmas `T.map_c`, `T.rel_c`;
* nesting through declared types (`Forest (Tree α)`, `Forest α (fun p => Blk α p)`), for `data`
  and `codata` (`Test/Param.lean`, `Test/Mixed.lean`).

NOT DONE:

* a declared type with the recursive occurrence in several parameter positions at once
  (`Pair X X` for a declared `Pair α β`): the multi-hole structure (parameters as holes,
  erasure of all at once); this is also section 5, step 2;
* an argument mixing the parameter and the recursive type (`List (α × T)`): the type is
  declared, but it gets no structure in `α`;
* `rel_*` characterisations of `Occ.Rel` through `prod`, `pi`, `comp` as iffs (only the
  introductions exist), and user-facing `T.map`/`T.Rel` abbreviations.

## 5. Mixed blocks: `mixed_mutual` — steps 1, 3 and 4 DONE, 2 NOT DONE

A block with `data` and `codata` declarations is a nested fixpoint, and a cyclic system has
several nested solutions (data outer and codata outer differ; the two orders of `Tree`/`Forest`
are finitely branching infinite trees, and finite trees), so the block must say the order. No
system does this on a block with per-type kinds: Agda's `∞`/Idris's `Inf` mark references with
the fixed convention "codata outer", sized types and explicit `μ`/`ν` calculi write the order,
Rocq and Isabelle have no mixed blocks and nest by hand. Nested fixpoints of the same kind
commute (Bekič), different kinds do not; so an order is a sequence of *runs*.

Decisions (fixed):

* a new command `mixed_mutual … end` (`mixed_mutual` is a token; bare identifiers `mixed_mutual`
  in importing files break, as `data` does); Lean's `mutual` keeps its meaning and rejects
  mixed blocks with a message pointing here;
* the textual order is the nesting order, the first declaration outermost ("the main type
  first"): `codata Tree` then `data Forest` is the finitely branching infinite trees;
* a run is a maximal sequence of adjacent declarations of the same kind and is one uniform
  mutual block (`Which`, block-level `corec`/`rec`, per-type aliases, as in section 3);
* every order is allowed, any number of runs, no restriction on which runs a declaration may
  mention (steps 2 and 3 below make this possible);
* a `mixed_mutual` block with a single kind is accepted with a warning ("use `mutual`");
  nothing else is printed;
* no `∞` marks: a reference marked differently from the others of its type is a thunk type
  `codata T∞ | delay (t : T)` written in the block; marks may become sugar for that later.

Semantics and contract (to be written as a "mixed mutual" section of `contract.md`): runs
`R₁ ⊃ R₂ ⊃ … ⊃ Rₖ`, outermost first; `Rᵢ` is a uniform block with one family parameter per
outer run it mentions (a type for a run of one type without indices, a family over the run's
packed index `(m : Which) ×' idx` otherwise) and nesting through the inner runs at their
families; `Rᵢ` keeps the uniform `data`/`codata` contract with the outer runs as parameters.
The principles compose: coinduction on an outer run sees the inner runs through their relators
(`Container.Rel`/`IContainer.Rel`, one whole finite layer per step), induction on an inner run
sees the outer runs as opaque parameters; an inner induction inside a coinductive step is
parametric in the outer relation `R` (`rel_map`, `rel_intro`, `rel_c`), a coinduction inside an
inductive step is a closed statement about the outer type. Users see the parameterised inner
types (`Forest α X`) and the closed outer ones (`Tree.node : α → Forest α (Tree α) → Tree α`).
The universe of a family parameter is a `universe` variable declared in scope (holes drift).

Steps, in order (steps 1 and 3 were done on the `Container` classes; since the switch to
occurrence structures, section 4, the same lemmas and compositions are stated with `Occ`:
`Container.map f` ↦ `Occ.map T.occ T.occ f`, `Container.comp` ↦ `Occ.comp` built by the
command, `genContainerLemmas` ↦ `genOccLemmas`, no instances passed):

1. DONE (2026-09-16). Constructor-level container lemmas, for every declared container (`data`
   and `codata`, type or family parameter): `T.map_c : Container.map f (T.c args) = T.c args'`
   (`f` at the parameter positions, `map f` at recursive ones, `map (map f)` through nested
   containers) and `T.rel_c` (`R` at parameter positions, `Rel R` at recursive ones ⇒
   `Rel R (T.c …) (T.c …)`), the two copies of the parameter in independent universes
   (`universe u'` declared in scope). Generic part: `Param.lean` `mapS`/`mapV`/`mapObj`,
   `mapV_encode` (the map on the trees of one layer), `mapObj_eq` and `map_ctorI_of`,
   `map_ctorC_of`, `cmap_ctorI_of`, `cmap_ctorC_of` (the map of a constructor application, with
   the layer of the target shape and the children as hypotheses, the latter under any proof of
   the erased-shape equation); `Codata.lean` `ctorC`, `ctor_eq_ctorC_of` (the derived codata
   constructor is the one on the container, `T.ctor_eq_ctorC`); `Container.lean`
   `toC_map`, `exists_map_of_rel'`/`exists_map_of_rel` (elimination of `Rel`),
   `exists_fn_of_forall`. Per-constructor scripts (`genContainerLemmas`): `dsimp` of `toC`,
   `shapeEquiv`, `shapeTo` everywhere, `toC_map` for the nested arguments, `cases`; for a
   container in the parameter (`as : List α`) the erased shape changes with the argument and
   the transport is reduced by one substitution lemma per recursive position (`key`).
   `rel_c` is `rel_map` on the constructor over the related pairs, rewritten by `map_c`. The
   generated instances are named `T.instContainer`/`T.instIContainer` and passed explicitly in
   the lemmas (the instance search runs before the numerals of an index are elaborated inside
   `fun α => T α (n + 1)`). Tests: `Test/Param.lean` (`Node`, `Vec`), `Test/Mixed.lean`
   (`Tree.bin` unfolded).
2. Containers in a suffix of the parameters, and nested occurrences with mixed positions:
   * the container parameter is a suffix `X₁ … Xₙ` of the parameters, one family over
     `J₁ ⊕ … ⊕ Jₙ` (`PSignature.J` is arbitrary already), one instance per suffix, the
     occurrence picking the shortest suffix covering the arguments that mention the block or
     the enclosing type's own container parameter;
   * `Kind.nest` records a role per summand of the container's index: recursive (with index
     terms), parameter of the enclosing type (with index terms), or fixed; position
     constructors carry the summand as an equation, `B.c_x (q) (j) (h : pidx x_s q = inr j)`
     with recursive index `j`, `P.c_x (q) (a) (h : pidx x_s q = inl a)` with parameter index
     `a`;
   * the enclosing `Shape` stores the values at parameter positions of a nested container
     (`x_v : ∀ q a, pidx x_s q = inl a → X a`), erased in `Shape₀`, exposed by
     `shapeTo`/`shapeOf`;
   * `toC`/`ofC` transport along the equation (`match hq : pidx x_s q with …`); the seven
     `F`-lemma scripts, `shapeOf_shapeTo`/`shapeTo_shapeOf`, `rel_ofC`'s bullets and `genRec`'s
     hypotheses (`∀ q j h, motive j (h ▸ (toC x).2 q)`) generalise `pidx x_s q` and case on it;
   * `F.map`/`F.Rel` through a mixed nest map per summand
     (`IContainer.map (fun p => match p with | inl _ => id | inr j => f j)`).
   Gives chain-shaped references between non-adjacent runs (`Trace → Proc` in
   `Proc ⊃ Menu ⊃ Trace`): without it `Menu` is no container in the processes, since its
   shapes contain trace shapes that still hold processes. Not started. A cheap alternative,
   to be decided: `mixed_mutual` could add to the run before `Trace` a wrapper type
   `ProcW α X | wrap (p : X)` (a constant functor, so the nested fixpoint is unchanged) and
   rewrite `Trace`'s occurrences of `Proc` to it, one wrapper per run crossed; every reference
   becomes adjacent with the current machinery, at the price of visible wrappers
   (`Trace.tick m (ProcW.wrap p) next`).
3. DONE (2026-09-16). Composition, for a reference from a run to a run further inside
   (`Proc → Trace`, the occurrence `Trace α (Menu α (Proc α))`): the instances
   `Container.comp`, `IContainer.comp`, `Container.compI`, `IContainer.compC` in
   `Container.lean` (shapes `Σ sh, (q : Pos sh) → Sh'`, positions `Σ q, Pos' (z.2 q)`, the
   equivalence by `Equiv` combinators, at low priority), found by instance search for the
   composite `fun X => G (H X)`; `nestedOcc` abstracts the unique recursive occurrence
   anywhere under type constructors (applications, products, lambdas; not arrows) into
   `G := fun X => ty[occ := X]`, so `List (Option (T i))` of section 4 is closed too;
   `mixed_mutual` applies an occurrence of a run further inside to the chain of families down
   to the declaration's own run (`famOf`). Tests: `Test/Rose.lean`, `Test/FinRose.lean`
   (`Rose₂`), `Test/MixedRuns.lean` (`Proc → Trace`, `Outer → Inner`). Since the switch to
   occurrence structures (section 4) the composite is `Occ.comp` built by the command, no
   instance search.
4. DONE (2026-09-15), before steps 2 and 3. The command (`MutualCmd.lean`): syntax
   `mixed_mutual (codata|data)+ end`; runs; inside-out elaboration (`elabRuns`: a family
   parameter for the adjacent outer run if mentioned, occurrences rewritten by one pass of
   `substOccs` with three substitutions, nesting through the adjacent inner run at the run's
   own family, `Which` of every run generated first, `universe u_<Run>` declared in scope);
   warning for a uniform block; `mutual` rejects mixed blocks; a temporary error for a
   declaration mentioning a run other than its own and its two neighbours, to be removed by
   steps 2 and 3. Tests: `Test/Mixed.lean` and `Test/MixedOrder.lean` as `mixed_mutual` blocks
   (both orders), `Test/MixedRuns.lean` (`Proc ⊃ Menu ⊃ Trace`, the three rejected forms by
   `#guard_msgs`); `Sketch/MixedFail.lean` kept. Docs: `contract.md` ("Mixed blocks"), the
   `MutualCmd.lean` header, memory. References to runs further inside: step 3. NOT DONE: a
   reference to a run further outside (step 2).

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
4. Nested types: DONE (leftovers listed above).
5. Mixed blocks, `mixed_mutual`: steps 1, 3 and 4 DONE; step 2 NOT DONE (a reference to a run
   further outside).
6. Surface items, as they become blocking.
