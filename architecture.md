# Architecture of `Colean/`

A declaration `codata T … | …` or `data T … | …`, or a `mutual` block of them, is processed in
steps with fixed boundaries. Each step sees only the outputs of the steps above it; each has one
file of theory and one generator file.

| Step | Sees | Produces | Proofs |
|---|---|---|---|
| 1. Functor | the declaration | `T.F`, `T.F.map`, `map_id`, `map_comp` | tactic, per declaration |
| 2. Model | `T.F` | `T.contract : Contract T F` (a signature, an isomorphism `F X ≃ σ.Obj X`, the fixpoint on `Raw`) | the isomorphism's laws by tactic; the rest instantiated |
| 2b. Model extras | the model | polymorphic `fold`/`corec`, `T.rec` | instantiated |
| 3. Framework | `T.contract` only | `ctor`, `dtor_ctor`, `ctor_dtor`, `ctor_injective`, `corec_eq`, `corec_unique` and the data duals | none: instantiation of generic theorems |
| 4. Surface | the constructor list and steps 2–3 | `T.cᵢ` with their lemmas, `casesOn`, `rec_cᵢ`, `fold_cᵢ`, the characterisation `T.F.Rel`, the types, aliases and per-type recursors of a block | term assembly |
| 5. Instances | a declared type | `PolyIso`/`PolyMap` instances for it (`T.Poly.*`) | the layer's laws by tactic; the fixpoint instantiated |

## Files

Theory, in dependency order:

- `Raw.lean`: the general type `Raw I L := List I → Option L` (the model's carrier).
- `PolyIso.lean`: the user interface for nesting: `PolyIso` and `PolyMap` (and `IPolyIso`, `IPolyMap` for functors on families) say that a functor is isomorphic to a polynomial functor. Instances for `List`, `Option`, `Array`. Depends on Mathlib only.
- `Framework.lean`: `Codata.Rel`, `Codata.Contract`, `Data.All`, `Data.Contract` and every theorem that follows from a contract alone. Depends on Mathlib only.
- `Model/Cotype.lean`: signatures, the container functor `Obj`, the encoding, the greatest fixpoint `IsWf`, `Cotype`, its contract pieces and the transport theorems to a functor `F ≃ Obj`.
- `Model/Intype.lean`: the least fixpoint `IsFin`, `Intype`, the dependent recursor by well-founded recursion, fold, and the transports.
- `Model/Poly.lean`: a least or greatest fixpoint of a layer polynomial in a parameter is polynomial in that parameter: trees of shapes, `Path`, `PolyFix`, `coFix`, `inFix`.
- `Model/Occ.lean`: occurrence structures `Occ`/`IOcc`, internal to the command: their combinators, laws and computation lemmas; the leaves are `Occ.ofIso F`, from the `PolyIso` instances.

Generators, on `Expr`, in dependency order. `Syntax.lean` holds the command syntax.

- `Gen/Decl.lean`: adding declarations from closed `Expr`s, each checked by the kernel before the next: inductive types with the auxiliary constructions of `inductive` (fixed indices promoted to parameters, as `inductive` does), noncomputable definitions, theorems by term or by a tactic on a goal metavariable, simp lemmas and other attributes; definitions by cases (`mkCasesOnApp`).
- `Gen/Occ.lean`: the occurrence structure of an elaborated argument type, by recursion on its head after `whnfR` (and `id`); instance search at leaves.
- `Gen/Ctx.lean`: the context `Ctx`: parameters (section variables first), indices and constructor arguments as free variables of one `TermElabM` run, the types being defined as local variables at a placeholder universe, argument kinds, names; for a block, its index `Blk.Ix`.
- `Gen/Front.lean`: syntax → `Ctx`, elaborating the declarations as `inductive` does, a single one or the types of a block.
- `Gen/Functor.lean`: step 1.
- `Gen/Signature.lean`, `Gen/Iso.lean`, `Gen/Model.lean`: step 2 (the signature; the isomorphism and its laws; the type and the contract).
- `Gen/Rel.lean`: `T.F.Rel`, `rel_map`, `rel_ofC` (step 4, generated before the model, see below).
- `Gen/Framework.lean`: step 3.
- `Gen/Extras.lean`: step 2b (`T.rec`).
- `Gen/Surface.lean`: step 4 (constructors and their lemmas, `casesOn`, `rec_cᵢ`, `fold_cᵢ`; in a block, the types `Tₘ`, the aliases and, for `data`, the recursors `Tₘ.rec` per type).
- `Gen/Derive.lean`: step 5, separate from the pipeline (see below).
- `Gen/Command.lean`: the pipeline. `CodataCmd.lean`, `DataCmd.lean`: the commands; `MutualCmd.lean`: `mutual` blocks of them.

## The generators

The commands read the user's syntax only to elaborate it. `Gen/Front.lean` elaborates a
declaration as Lean's `inductive` does: the parameters and the declared sort, then the types being
defined as local variables, against which each constructor is elaborated to one telescope. Every
later decision is taken on the elaborated types, after `whnfR`: an occurrence is an application of
one of these variables to the parameters (and indices), and products, sums, functions, dependent
pairs and leaves are recognised by their head. So spellings that mean the same type are one
(`A × B` and `Prod A B`, an abbreviation, `id A`, `Σ`, `<|`, an arrow-form constructor), and no
generated name can capture a user's.

The whole pipeline runs inside one `TermElabM` run, in the continuation of `Gen.withCtx`. Each
step has its own heartbeat budget, as a separate command would, and a failure restores the state
before the error is reported, so a failed command declares nothing, as with `inductive`. The
parameters, the indices and the constructor arguments are free variables of its local context.
A generator builds the types and values of its declarations as `Expr`s over these variables and
closes each declaration once, with `mkForallFVars`/`mkLambdaFVars` and the binder infos of that
declaration (`withBinderInfo`); the occurrences of the types being defined are replaced by what
a step needs (`replaceOcc`, `withArgsAt`). The declarations are added directly (`addDecl`,
`Gen/Decl.lean`): inductive types with the constructions of `inductive`, definitions by `casesOn`,
theorems. Generated constants are used through `constWith`, at the universes a use needs.

Proofs are terms where a theorem of the theory applies. Where building a term by hand would be
painful, the statement is a goal metavariable and a tactic closes it: `MVarId.cases`, `refl`,
`simp only`, `rewrite` from `MetaM`, or a short tactic script run on the goal (`rel_map`,
`rel_ofC`, the `rw` steps of step 5). A value by dependent cases is built the same way, as the
instantiated goal. The only syntax left is the command syntax, these tactic scripts, and the
attributes of the eliminators.

A position `b : T.B idx (Shape.c d)` is eliminated in general position (`casesPos`,
`Gen/Iso.lean`): at variables, solving the equation of the shapes, by the heterogeneous
`noConfusion`, before those of the indices, which then hold by definition. So a constructor's
result index need not be a pattern (`T (n * 2)`, `T (!b)`), as with `inductive`; `MVarId.cases`
would have to invert it. Other eliminations are at index variables: the layers by cases on `F` or
on the shape, `rel_ofC` by cases on `F.Rel` after writing the layers as `toC a`.

## Rules

- Tactic proofs are the laws of the generated inductives: the functor laws (step 1), the isomorphism laws and the lifting laws (steps 2 and 4), and in step 5 the laws of the layer and the rewriting steps of the fixpoint. Everything else instantiates a theorem of `Framework.lean` or `Model/`.
- The framework never mentions a model, a signature or `Raw`; the model never mentions a declaration; the surface never proves anything.
- A nested argument enters the model as a shape with positions; the user-facing `F` keeps its type.
- Some generated proofs need the definitional unfolding of Lean before 4.34 (`withUnfolding`, around those proofs only): a term of the signature is the expected one only after unfolding.

## Known boundary violations

- `T.corec`, `T.fold` (universe-polymorphic in the state) and `T.rec` come from the model, because `Contract` fixes one universe for `F`. Fix: a universe-polymorphic framework interface, after which `T.rec` derives from `fold` and `induction`.
- `T.F.Rel` (surface) is generated before the model, because `rel_ofC` and the contract's `bisim` are stated with it. Fix: state `bisim` with the canonical `Rel`, derive the inductive characterisation in step 4 by term-level introduction and elimination lemmas.

## Blocks

A `mutual` block of `codata`, or of `data`, declarations is one family over the inductive
`Blk.Ix`, which has a constructor per type whose arguments are that type's indices. The front end
declares `Blk.Ix` and gives the family the one index `m : Blk.Ix params`; an occurrence
`Tₘ params idx` is then at `Blk.Ix.Tₘ idx`, and steps 1 to 3 run on the family as on a single
type with one index. Step 4 adds the types `Tₘ params idx := Blk params (.Tₘ idx)`, and works per
type: the constructors and their lemmas are stated with the types `Tₘ`, `Tₘ.casesOn` has only the
constructors of `Tₘ`, and `Tₘ.corec`, `Tₘ.bisim`, `Tₘ.fold` restrict the block-level declarations.
For `data`, `Tₘ.rec` has a motive per type, as Lean's mutual recursors: it is `Blk.rec` at the
motive `fun i x => Blk.Ix.casesOn i motive_1 … x`, whose minor premises are the per-type ones by
unfolding, and its rules `Tₘ.rec_cᵢ` are the block-level rules `Blk.rec_cᵢ` by unfolding.

A block mixing `data` and `codata` is a nested fixpoint, whose order is a choice. The
`mixed_mutual` command that stated the order is removed, pending a redesign; `mutual` rejects
such a block.

## Nesting and declared types

Defining a type and presenting it as a polynomial functor are separate steps. Step 5,
`deriveInstances` (`Gen/Derive.lean`), runs after the pipeline has finished, in the same run: it
reads the declaration's context and the type's public declarations, and nothing in the pipeline
depends on it. On failure it restores the state and logs a warning, so it can't affect the type.

It generates one instance per type, `PolyIso (fun X => T (H₁ X) … (Hₙ X))` with premises on the
`Hᵢ`, over the parameters that may vary, and the eta-reduced form `T A₁ … Aₙ₋₁`. Only the layer
`T.Poly.toL`/`ofL` and its laws are per declaration; the fixpoint is `Model/Poly.lean`, one proof
for `data` and `codata`, from the contract. The structure of a field in a parameter is that of
`Gen/Occ.lean`, with the premise's structure at the parameter.

Scope: a single type without indices. Mutual blocks and indexed families are skipped.
