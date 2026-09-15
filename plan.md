# Plan: `codata` and `data` as subtypes of `Raw`

## Where we are

`Subtypes/Codata.lean`: the generic theory, for indexed polynomial signatures (a plain type is
a family over `Unit`), the contract (`contract.md`, plain and indexed sections), and the derived
layer. `Subtypes/CodataCmd.lean`: the `codata` command. `Subtypes/Data.lean` and
`Subtypes/DataCmd.lean`: the inductive dual. `Subtypes/MutualCmd.lean`: mutual blocks of
either. `Subtypes/Container.lean`: containers for nested occurrences; `Subtypes/Param.lean`: a
declared type as a container in its parameter. `Subtypes/Test/`: one test per type.
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

## 3. Mutual types — DONE

`Subtypes/MutualCmd.lean`: Lean's own `mutual … end` syntax around `codata` or `data`
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

## 4. Nested types — DONE

`Subtypes/Container.lean`: the class `Container G Sh Pos` (`G X ≅ Σ sh, Pos sh → X`, shapes and
positions independent of `X`), `Container.map`/`Container.Rel` between two universes with their
laws, and the registry: instances for `List`, `Option`, `A × ·`. A nested argument
`x : G (T idx)` contributes the container's shape as data and its positions as recursive
positions; the generic theory is unchanged, the functor `F` keeps `G X`, and the isomorphism
goes through the container's (`Test/Rose.lean`, `Test/FinRose.lean`).

`Subtypes/Param.lean`: a declared type is itself a container in its type parameter. A signature
with parameter positions (`PSignature`: erased shapes `Shape₀`, positions `P` of the parameter,
recursive positions `B` over `Shape₀`) gives the ordinary signature at any parameter type `α`
through an equivalence `Shape ≃ Σ s₀, P s₀ → α`; the erased trees are the shapes of the
container, a path to a node with a parameter position of its erased shape is a position, and
`PSignature.container`/`cocontainer` are the instances for `Intype`/`Cotype` (Mathlib's
`MvPFunctor.wp`/`mp`, done pathwise on `Raw`: `erase`, `reattach`, `layer`).

DONE:

* `List`, `Option`, `A × ·` in recursive positions, for `codata` and `data`, with `F.map` acting
  through `Container.map` (simp lemmas back to `List.map`, `Option.map`), `F.Rel` through
  `Container.Rel` (`rel_intro`), induction hypotheses at the positions of the container
  (`mem_toC_list`, `toC_list_mem` for lists);
* any type constructor with a `Container` instance written by hand;
* the instance generated for every `data`/`codata` (and every type of a mutual block) whose
  last parameter is a type `α` used only at parameter positions (`(a : α)`, `(f : A → α)`,
  `(as : G α)` through a container `G`): `T.Shape₀`, `T.P`, `T.shapeEquiv`, `T.psig`,
  `T.sig := T.psig.sig T.Shape T.shapeEquiv`, `T.Sh`, `T.Pos` and
  `instance : Container (fun α => T params α idx) T.Sh T.Pos`; other uses of `α` (a negative
  occurrence, an index) just skip the instance;
* the same for a family parameter `X : J → Type u` (positions `X j`, `A → X j`, `G (X j)`),
  with the positions' indices `T.pidx` and the indexed container class `IContainer`
  (`Container.lean`), instance `IContainer (fun X => T params X idx) T.Sh T.Pos T.posIdx`;
* nesting through declared types (`Forest (Tree α)` with a declared `Forest`, and
  `Forest α (fun p => Blk α p.1 p.2)` through an indexed container), for `data` and `codata`:
  the mixed inductive/coinductive block of section 3 (`Test/Param.lean`, `Test/Mixed.lean`).

NOT DONE:

* nesting under a telescope (`k : A → List (T i)`);
* composed containers (`List (Option (T i))`), containers in several parameters and nested
  occurrences with mixed positions: section 5, steps 2 and 3;
* containers whose shapes depend on the argument's universe;
* constructor-level lemmas for `Container.map` and `Container.Rel` on a declared type:
  section 5, step 1.

## 5. Mixed blocks: `mixed_mutual` — NOT DONE

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

Steps, in order:

1. Constructor-level container lemmas, for every declared container (`data` and `codata`):
   `T.map_c : Container.map f (T.c args) = T.c args'` (`f` at the parameter positions, `map f`
   at recursive ones, `map (map f)` through nested containers) and `T.rel_c` (introduction:
   `R` at parameter positions, `Rel R` at recursive ones ⇒ `Rel R (T.c …) (T.c …)`), plus
   `map_nil`-style cases and the `IContainer` versions. Generic part in `Param.lean`: the
   layer of `encode` (`erase_encode`, `reattach_encode`, `valAt` at the root and at
   `Pos.cons`), `mapV_encode : mapV f (encode i z) = encode i (mapObj f z)`, and
   `rel_ctorI_intro`; per-constructor proofs reduce to `cases b; rfl` (casts along `sh₀_symm`
   K-reduce, as in `child_encode_castP`). Prerequisite for any bisimulation through a declared
   container with different forests (`Test/Mixed.lean`'s `sorry`: the unfolding of `Tree.bin`).
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
   shapes contain trace shapes that still hold processes.
3. Composition, for a reference from a run to a run two levels inside (`Proc → Trace`, whose
   family has the component `Menu α (Proc α)`): `IContainer.comp` in `Container.lean`
   (`MvPFunctor.comp`: shapes `Σ sh, (q : Pos sh) → Sh_{pidx q}`, positions
   `Σ q, Pos_{pidx q} …`, with the `map`/`Rel` laws), and `mixed_mutual` emitting a named
   composite with its instance so that the occurrence has a single block-valued family; also
   closes `List (Option (T i))` of section 4.
4. The command: syntax; `readDecl` over the block; runs; inside-out elaboration generalising
   `elabMixed` (parameters per referenced outer run, occurrence rewriting, `Which` of every run
   generated first, `universe u_<Run>`); warning for a uniform block; `mutual` rejecting mixed
   blocks. May land before steps 2 and 3 with a temporary error for references between
   non-adjacent runs (a declaration mentioning a run other than its own and its two
   neighbours), removed when they land. Tests: `Test/Mixed.lean` and `Test/MixedOrder.lean`
   rewritten as `mixed_mutual` blocks in both orders, `Proc ⊃ Menu ⊃ Trace` with three runs,
   the non-adjacent variants after steps 2 and 3, `Sketch/MixedFail.lean` kept as is. Docs:
   `contract.md`, the `MutualCmd.lean` header, memory.

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
5. Mixed blocks, `mixed_mutual`: NOT DONE, steps 1–4 in that order.
6. Surface items, as they become blocking.
