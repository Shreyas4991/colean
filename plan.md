# Plan: `codata` and `data` as subtypes of `Raw`

## Where we are

`Subtypes/Codata.lean` proves the contract (`T`, `dtor`, `corec`, `dtor_corec`, `bisim`) once, for
the container `σ.Obj X i = { shape : σ.Shape i, child : (b : σ.B i shape) → X (σ.idx b) }` of any
indexed polynomial signature, plus the derived layer (`ctor`, `corec_eq`, `corec_unique`,
`casesOn`, injectivity, disjointness). A plain type is a family over `Unit`; there is no separate
plain theory. `Subtypes/CodataCmd.lean` turns a `codata` declaration into a signature, an
isomorphism with `σ.Obj`, and instantiations of those theorems. `Subtypes.lean` imports everything
in the folder and is the only import of the root module, so `lake build` checks it all. Supported:
parameters, any number of indices (propositions included), explicit and implicit binders, plain
recursive arguments, recursive arguments under `A → T` with `A` depending on the constructor's
data. Not supported: mutual and nested types, `data`.

Design rules, fixed by discussion:

* the theory is stated as theorems and instantiated; the command proves by tactic only the six
  lemmas about the generated inductive `F`;
* `corec` is universe-polymorphic in the state, no `ULift` for users;
* noncomputable is fine; do not complicate anything to keep computability.

## 1. Indices (done for `codata`)

Syntax, as for `inductive`:

```
codata Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

codata Bounded : (n : Nat) → n ≤ 10 → Type
  | step {n : Nat} {h : n + 1 ≤ 10} (s : Bounded (n + 1) h) : Bounded n (Nat.le_of_succ_le h)
  | stay {n : Nat} {h : n ≤ 10} (s : Bounded n h) : Bounded n h
```

Generic layer (`Codata.lean`). An indexed signature is an index type `I`, shapes
`Shape : I → Type u`, positions `B : (i : I) → Shape i → Type v`, and the index
`idx : B i s → I` of the recursive argument at each position. The container is
`σ.Obj (X : I → Type) i = { shape : Shape i, child : (b : B i shape) → X (idx b) }`; the encoding is
one `Raw` with labels `Σ i, Shape i` and path indices `Σ l, B l.1 l.2`; `IsWf : I → Raw → Prop` is
a greatest fixpoint over indexed predicates, `Cotype σ i := {t // IsWf i t}`. `dtorC`, `corecC`,
`dtorC_corecC`, `bisimC`, the transport theorems, `Contract` and the `_of` theorems are the plain
ones with the index threaded through; the index is implicit wherever an argument determines it.
The index of a position is a *function* (computed once the position is a constructor) rather
than a further index of `B`: with propositions as indices, unification cannot recover a proof
argument from an index term, since any two proofs are definitionally equal.

Command. With a declared sort `: (i₁ : I₁) → I₂ → Type u`, every constructor gives its result
type `T params idx₁ idx₂`, and recursive arguments carry their indices. The generic theory has one
index type, so several indices are packed into `T.Ix := (i₁ : I₁) ×' I₂` (a `PSigma`, hence
propositions are allowed) and none into `Unit`; all user-facing declarations stay curried, with the index binders
named as the user named them. The internal isomorphism `T.toC`/`T.ofC` and its laws keep the
index binders curried and take the family on the packed index; the instantiations of the generic
theorems convert with lambdas (`fun j₁ j₂ => f ⟨j₁, j₂⟩`, `fun p => c p.1 p.2`), so every
generated statement is the generic one up to definitional unfolding. Generated constructor
applications are fully explicit (`@F.c params X …`), again so that no proof argument is ever
inferred. Injectivity and disjointness lemmas are generated only when well-typed (indices
independent of the constructor's arguments, and equal for disjointness). `casesOn` has motive
`∀ j₁ j₂, T j₁ j₂ → Sort _`; `cases` refines the indices (`cases v` on `v : Vec α 0` leaves only
`nil`, on `Bounded 10 h` only `stay`). `motive` and the state type `S` are plain binder names, so
`(motive := …)` and `(S := …)` work.

Tests: `Test/Vec.lean` (with `toList`/`ofList` inverse to each other, up to the equality of
lengths), `Test/Alt.lean` (streams alternating between two sorts), `Test/Walk.lean` (walks on
`Int` with the position as index, determined by their steps, by bisimulation), `Test/Cyc.lean`
(two indices, the second depending on the first), `Test/Bounded.lean` (a proposition as index), `Test/Diag.lean` (indices that are bare or
repeated binders);
`Sketch/IdxVec.lean` and `Sketch/IdxCyc.lean` are hand-written templates of the generated
declarations for one and two indices.

The generated `match`es (`F.map`, `idx`, `toC`, `ofC`, `casesOnAux`) take the index binders
as explicit discriminants, name a binder's index pattern at its first occurrence only, and use
`_` for the constructor's own arguments in those positions; Lean's pattern elaborator refuses to
name a forced variable, and which index variables `match a with` generalises is Lean's choice,
not the generator's (`Test/Diag.lean`: `step {n} … : Diag n n`, `stop {n m} : Diag n m`). The
one constructor shape left unsupported is a proof binder that occurs only inside index terms
and in no field: it can be recovered neither by name nor by unification.

Left for later: `data` families (section 2), and non-uniform parameters (`Nest α` with
`Nest (α × α)` inside), which are indices in disguise; decide whether to support them by
promoting them to indices as Lean does.

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

1. Indices: done for `codata`.
2. `data`, reusing the indexed layer.
3. Mutual blocks via the index trick; then mixed blocks as nested fixpoints.
4. Nested types through containers.
5. Surface items, as they become blocking.
