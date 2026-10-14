import Colean.Subtypes.Cmd.Functor
import Colean.Subtypes.Cmd.Surface

/-!
# The `codata` command

Current scope: parameters, a single type or a mutual block, any number of indices. Constructor
binders may be explicit or implicit; recursive arguments may be plain (`t : T params idx`),
under a telescope of arrows (`f : (y₁ : B₁) → … → Bₙ → T params idx`), dependent or not, where
the domains may depend on the constructor's own data and the index on the bound variables, or
*nested*: any other type mentioning `T`, built from occurrences by products, sums, functions
and dependent pairs over constant types, and named type constructors with an occurrence
structure (`List`, `Option`, `Array`, the declared types; see `Occ.lean`):
`children : List (T params idx)`, `p : T params i × T params j`, `k : A → List (T params idx)`,
`c : Option (T params idx × T params idx)`, `List (Option (T params idx))`, …. The structure of
the argument type is built by recursion on its syntax (`occTreeOf`, `occTermOf`), with instance
search only at the named constructors. A data binder may not mention `T`. When the last
parameter is a type `α`, or a family `X : J → Type u`, used only at parameter positions
(`(a : α)`, `(f : A → α)`, or nested, `(as : List α)`, `(p : α × α)`; `(t : X j)`, …), the type
itself has an occurrence structure in it (see `Param.lean`), registered as a leaf, so that later
declarations may nest through it: `children : Forest (T params idx)` through a declared
`Forest`, or `children : Forest (fun p => T params (idx p))` through a declared `Forest` with a
family parameter (an indexed structure, `IOcc`), which is what mixed `mutual` blocks elaborate
to (`MutualCmd.lean`).

```
codata ITree (E : Type → Type) (R : Type)
  | Ret (r : R)
  | Tau (t : ITree E R)
  | Vis {X : Type} (e : E X) (k : X → ITree E R)

codata Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)
```

The command generates, with the parameters as arguments of every declaration (explicit for the
types `T`, `T.F`, `T.Shape`, `T.B`, `T.sig`, implicit elsewhere):

* `T.F (params) (X : Type _)`: the constructor list with `T params` replaced by `X`, as an
  inductive type; `T.F.map` and `T.F.Rel`, its action on functions and its lifting to relations,
  with the laws `T.F.map_id`, `T.F.map_comp`, `T.F.rel_map`, and the simp lemmas `T.F.map_ctorᵢ`;
* the signature: `T.Shape` (the constructors with their non-recursive data only, plus the shape
  `x_s` of each nested argument `x`) and `T.B : T.Shape → Type`, the positions for recursive
  arguments, one nullary constructor `ctorᵢ_t` per plain argument `t`, one unary constructor
  `ctorᵢ_f (p : A)` per function argument `f : A → T` and one `ctorᵢ_x (q : Pos x_s)` per nested
  argument (positions of its structure); bundled as `T.sig`;
* with a container parameter `α`: the erased shapes `T.Shape₀` (the shapes without the
  arguments at parameter positions, plus the shape of each argument nested in `α`), the
  parameter positions `T.P : T.Shape₀ → Type`, one constructor `ctorᵢ_a` per argument `(a : α)`,
  `ctorᵢ_f (y : A)` per `(f : A → α)` and `ctorᵢ_as (q : Pos as_s)` per nested `as`, the
  equivalence `T.shapeEquiv : T.Shape α ≃ Σ s₀, T.P s₀ → α` (by `T.shapeTo`/`T.shapeOf`), the
  parameterised signature `T.psig` (`T.B` is then over `T.Shape₀`, `T.sig := T.psig.sig …`),
  and after the type the structure `T.Sh`, `T.Pos` and
  `T.occ : Occ T.Sh T.Pos (fun α => T params α idx)` with its registration `T.instOccLeaf`; for
  a family parameter `X : J → Type u`, also the positions' indices `T.pidx : T.P s₀ → J`,
  `T.posIdx` and `T.occ : IOcc T.Sh T.Pos T.posIdx (fun X => T params X idx)`; and the
  constructor-level lemmas `T.map_ctorᵢ` (`Occ.map T.occ T.occ f` on a constructor application)
  and `T.rel_ctorᵢ` (`Occ.Rel T.occ T.occ R` on two constructor applications from `R` and
  `Rel R` on their arguments), see `genOccLemmas`;
* `T.toC`, `T.ofC` with the four laws `T.ofC_toC`, `T.toC_ofC`, `T.ofC_map`, `T.rel_ofC`;
* the contract: `T`, `T.dtor`, `T.corec`, `T.dtor_corec`, `T.bisim`, transported from the
  generic `Signature` theorems; `T.corec` accepts a state in any universe;
* derived from the contract (`Codata.Contract`): `T.ctor`, `T.dtor_ctor`, `T.ctor_dtor`,
  `T.ctor_injective`, `T.corec_eq`, `T.corec_unique`; the individual constructors `T.ctorᵢ` with
  the simp lemmas `T.dtor_ctorᵢ` and `T.ctor_ctorᵢ` (`T.ctor (T.F.ctorᵢ …) = T.ctorᵢ …`),
  injectivity `T.ctorᵢ_inj` (for constructors without implicit binders) and disjointness
  `T.ctorᵢ_ne_ctorⱼ`, all simp lemmas;
* a case analysis principle `T.casesOn`, registered as the `cases` eliminator for `T`, with
  its computation rules `T.casesOn_ctorᵢ` as simp lemmas.

With indices (`codata T (params) : (i₁ : I₁) → I₂ → Type u`, constructors
`ctorᵢ … : T params idx₁ idx₂`), the same declarations are generated in their indexed form:
`T.F (params) (X : ∀ i₁ i₂, Type _) : ∀ i₁ i₂, Type _`, `T.F.map (f : ∀ j₁ j₂, X j₁ j₂ → Y j₁ j₂)`,
`T.Shape : ∀ i₁ i₂, Type _`, `T.B : ∀ i₁ i₂, T.Shape i₁ i₂ → ∀ j₁ j₂, Type _` (a position records
the indices of its recursive argument), `T : ∀ i₁ i₂, Type _`, `T.dtor {i₁ i₂}`,
`T.corec (c : ∀ j₁ j₂, S j₁ j₂ → T.F S j₁ j₂) {i₁ i₂}`, `T.bisim (R : ∀ j₁ j₂, …)`, a motive
`∀ j₁ j₂, T j₁ j₂ → Sort _` for `T.casesOn`, and so on. The index binders carry the names the
user gave them. Injectivity and disjointness lemmas are generated only when they are well-typed,
that is when the indices involved do not depend on the constructors' arguments and (for
disjointness) coincide.

The generic theory (`Codata.lean`) has one index type. Several indices are packed into one,
`T.Ix (params) := (i₁ : I₁) ×' I₂` (a `PSigma`, so indices may be propositions), and no index is
`Unit`; the user-facing declarations are curried: the internal isomorphism `T.toC`/`T.ofC` with
its three laws takes the family on the packed index, and the instantiations of the generic
theorems convert between the two forms with lambdas (`fun j₁ j₂ => f ⟨j₁, j₂⟩`,
`fun p => c p.1 p.2`), so that every statement above is definitionally the generic one. With one
index nothing is packed.

Only the seven lemmas about the generated inductive `T.F` (`map_id`, `map_comp`, `rel_map`,
`ofC_toC`, `toC_ofC`, `ofC_map`, `rel_ofC`) are proved by tactic scripts, and those are `cases`
followed by `rfl` or `solve_by_elim`, with the laws of `Occ.lean` for nested arguments;
everything else instantiates a theorem of `Codata.lean`.
The declarations from `T` on are generated in a `noncomputable section`, since the encoding
decides equality of shapes classically.

The analysis of the declaration (`mkCtx`) and the generators of `T.F`, the signature, the
isomorphism, the constructors and `casesOn` are shared with the `data` command
(`DataCmd.lean`), which differs only in the contract and what is derived from it; `T.F.Rel`,
`rel_map` and `rel_ofC` are generated for `codata` only. A mutual block (`MutualCmd.lean`) is
one family whose first index enumerates its types: `mkCtx` receives the types with their
constructors and the enumeration, every generator works on the block, and the user-facing
types, constructors, `casesOn` and aliases are per type (`genTypes`, `genCases`, `genAliases`).

The generators are split by the steps of `architecture.md`: `Cmd/Analysis.lean` (the context),
`Cmd/Functor.lean` (step 1), `Cmd/Model.lean` (step 2), `Cmd/Extras.lean` (step 2b),
`Cmd/Framework.lean` (step 3), `Cmd/Surface.lean` (step 4); this file is the pipeline.
-/

open Lean Elab Command Lean.Parser.Term

namespace Codata

/-- The generators of `codata`, in order. The encoding decides equality of shapes classically:
the type's corecursor and constructors are noncomputable. -/
def codataPipeline (ctx : Ctx) : CommandElabM Unit := do
  -- Since Lean 4.34 implicit arguments and the types of assigned metavariables are compared
  -- without unfolding definitions; the generated proofs rely on unfolding the type to its model,
  -- so restore the old comparison for the generated declarations only.
  elabCommand (← `(section))
  elabCommand (← `(set_option backward.isDefEq.respectTransparency false))
  elabCommand (← `(set_option backward.isDefEq.respectTransparency.types false))
  genFunctor ctx
  if ctx.co then genRel ctx
  genSignature ctx
  genIso ctx
  elabCommand (← `(noncomputable section))
  genContract ctx
  genContractDef ctx
  genTypes ctx
  genDerived ctx
  genCtors ctx
  genCases ctx
  genAliases ctx
  genOcc ctx
  genCtorEqCtorC ctx
  genOccLemmas ctx
  elabCommand (← `(end))
  elabCommand (← `(end))

@[command_elab codataCmd] def elabCodata : CommandElab := fun stx => do
  let `(codata $T:ident $paramsStx:bracketedBinder* $[: $sortStx]? $ctorsStx:codataCtor*) := stx
    | throwUnsupportedSyntax
  codataPipeline (← mkCtx true T paramsStx sortStx #[(T, ctorsStx)] none)

end Codata
