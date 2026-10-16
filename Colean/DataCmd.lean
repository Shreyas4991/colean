import Colean.CodataCmd

/-!
# The `data` command

The inductive twin of `codata`, with the same syntax and the same scope (parameters, indices,
recursive arguments under telescopes):

```
data FinList (α : Type u)
  | nil
  | cons (a : α) (l : FinList α)

data Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)
```

The analysis of the declaration and the generators of `T.F`, the signature `T.sig` and the
isomorphism `T.toC`/`T.ofC` are those of `CodataCmd.lean`; `T.F.Rel` is not generated. The
command then produces, from the generic theory of `Data.lean`:

* the contract: `T := Intype sig`, `T.ctor : F T i → T i`, `T.fold : (∀ i, F S i → S i) →
  T i → S i` for a family `S` in any universe, `T.fold_ctor`, and `T.contract : Data.Contract`,
  whose `induction` field (for the canonical lifting `Data.All`) is instantiated at the packed
  index directly from `Signature.induction_of`;
* derived from the contract: `T.dtor` (Lambek), `T.dtor_ctor`, `T.ctor_dtor`,
  `T.ctor_injective`, `T.fold_eq`, `T.fold_unique`; the constructors `T.ctorᵢ` with `T.dtor_ctorᵢ`,
  `T.ctor_ctorᵢ`, `T.fold_ctorᵢ`, injectivity and disjointness, and `T.casesOn`, as for `codata`;
* the dependent recursor `T.rec : {motive : ∀ i, T i → Sort v} → minors → ∀ {i} (t : T i),
  motive i t`, with one minor premise per constructor carrying an induction hypothesis for each
  recursive argument (`∀ ys, motive _ (k ys)` under a telescope), registered as the
  `induction` eliminator, and its computation rules `T.rec_ctorᵢ` as simp lemmas. It is
  `Signature.rec_of` at the packed index, with the minor premises assembled by a `match` on
  `F T i` (`T.recAux`); its computation rules are propositional, since the generic recursor is
  built from `WellFounded.fix`.

The `Prop` instance of `T.rec` is induction with per-constructor hypotheses; the contract's
`induction` with the `Data.All` hypothesis is not curried for the user.
-/

open Lean Elab Command Lean.Parser.Term

namespace Codata

/-- The generators of `data`, in order. The encoding decides equality of shapes classically, and
the recursor is by well-founded recursion: the type's constructors and recursors are
noncomputable. -/
def dataPipeline (ctx : Ctx) : CommandElabM Unit := do
  -- Since Lean 4.34 implicit arguments and the types of assigned metavariables are compared
  -- without unfolding definitions; the generated proofs rely on unfolding the type to its model,
  -- so restore the old comparison for the generated declarations only.
  elabCommand (← `(section))
  elabCommand (← `(set_option backward.isDefEq.respectTransparency false))
  elabCommand (← `(set_option backward.isDefEq.respectTransparency.types false))
  genFunctor ctx
  genSignature ctx
  genIso ctx
  elabCommand (← `(noncomputable section))
  genDataContract ctx
  genDataContractDef ctx
  genTypes ctx
  genDataDerived ctx
  genCtors ctx
  genCases ctx
  genRec ctx
  genRecLemmas ctx
  genDataAliases ctx
  genOcc ctx
  genOccLemmas ctx
  elabCommand (← `(end))
  elabCommand (← `(end))

@[command_elab dataCmd] def elabData : CommandElab := fun stx => do
  let `(data $T:ident $paramsStx:bracketedBinder* $[: $sortStx]? $ctorsStx:codataCtor*) := stx
    | throwUnsupportedSyntax
  dataPipeline (← mkCtx false T paramsStx sortStx #[(T, ctorsStx)] none)

end Codata
