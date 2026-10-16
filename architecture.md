# Architecture of `Colean/`

A declaration `codata T … | …` or `data T … | …` is processed in steps with fixed boundaries.
Each step sees only the outputs of the steps above it; each has one file of theory and one
generator file.

| Step | Sees | Produces | Proofs |
|---|---|---|---|
| 1. Functor | the declaration | `T.F`, `T.F.map`, `map_id`, `map_comp` | tactic, per declaration |
| 2. Model | `T.F` | `T.contract : Contract T F` (a signature, an isomorphism `F X ≃ σ.Obj X`, the fixpoint on `Raw`) | the isomorphism's laws by tactic; the rest instantiated |
| 2b. Model extras | the model | polymorphic `fold`/`corec`, `T.rec`, `T.occ`, `T.map_c`, `T.rel_c` | instantiated, some tactic |
| 3. Framework | `T.contract` only | `ctor`, `dtor_ctor`, `ctor_dtor`, `ctor_injective`, `corec_eq`, `corec_unique` and the data duals | none: instantiation of generic theorems |
| 4. Surface | the constructor list and steps 2–3 | `T.cᵢ` with their lemmas, `casesOn`, `rec_cᵢ`, `fold_cᵢ`, the characterisation `T.F.Rel`, per-type names of a block | term assembly |

## Files

Theory, in dependency order:

- `Raw.lean`: the general type `Raw I L := List I → Option L` (the model's carrier).
- `Framework.lean`: `Codata.Rel`, `Codata.Contract`, `Data.All`, `Data.Contract` and every theorem that follows from a contract alone. Depends on Mathlib only.
- `Model/Cotype.lean`: signatures, the container functor `Obj`, the encoding, the greatest fixpoint `IsWf`, `Cotype`, its contract pieces and the transport theorems to a functor `F ≃ Obj`.
- `Model/Intype.lean`: the least fixpoint `IsFin`, `Intype`, the dependent recursor by well-founded recursion, fold, and the transports.
- `Model/Occ.lean`: occurrence structures `Occ`/`IOcc`, their combinators, laws and computation lemmas.
- `Model/Param.lean`: a fixpoint's occurrence structure in its parameter (erasure on `Raw`), and the computation of its map on a layer.

Generators, in dependency order:

- `Cmd/Analysis.lean`: syntax → `Ctx`. The occurrence structure of a nested argument is built here by recursion on the syntax of its type; instance search only at named type constructors.
- `Cmd/Functor.lean`: step 1.
- `Cmd/Model.lean`: step 2, ending with `genContractDef`/`genDataContractDef`.
- `Cmd/Framework.lean`: step 3.
- `Cmd/Extras.lean`: step 2b (`genOcc`, `genCtorEqCtorC`, `genOccLemmas`, `genRec`).
- `Cmd/Surface.lean`: step 4 (`genRel`, `genCtors`, `genCases`, `genTypes`, `genAliases`, `genRecLemmas`, `genDataAliases`).
- `CodataCmd.lean`, `DataCmd.lean`: the pipelines and the commands. `MutualCmd.lean`: `mutual` and `mixed_mutual` blocks, which only rewrite syntax and call the pipelines.

## Rules

- The only tactic proofs are the functor laws (step 1) and the isomorphism laws (step 2). Everything else instantiates a theorem of `Framework.lean` or `Model/`.
- The framework never mentions a model, a signature or `Raw`; the model never mentions a declaration; the surface never proves anything.
- A nested argument enters the model as a shape with positions; the user-facing `F` keeps its type.

## Known boundary violations

- `T.corec`, `T.fold` (universe-polymorphic in the state) and `T.rec` come from the model, because `Contract` fixes one universe for `F`. Fix: a universe-polymorphic framework interface, after which `T.rec` derives from `fold` and `induction`.
- `T.F.Rel` (surface) is generated before the model, because `rel_ofC` and the contract's `bisim` are stated with it. Fix: state `bisim` with the canonical `Rel`, derive the inductive characterisation in step 4 by term-level introduction and elimination lemmas.
- `T.map_c`, `T.rel_c` are per-constructor lemmas proved by tactic on the encoding (step 2b). Fix: one generic theorem about erasure, or generation on first use by a nesting declaration.
- `genCtorEqCtorC` (step 2b) relates the framework's `ctor` to the model's `ctorC`; it exists only for the previous item.
