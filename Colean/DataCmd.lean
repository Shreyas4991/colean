import Colean.CodataCmd

/-!
# The `datatype` command

The inductive twin of `codatatype`, with the same syntax and the same scope (parameters, indices,
recursive arguments under telescopes):

```
datatype FinList (α : Type u)
  | nil
  | cons (a : α) (l : FinList α)

datatype Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)
```

The analysis of the declaration and the generators of `T.F`, the signature `T.Colean.sig` and the
isomorphism `T.Colean.toC`/`T.Colean.ofC` are those of `codatatype` (`Gen/`, `CodataCmd.lean`);
`T.F.Rel` is not generated. The command then produces, from the generic theory (`Framework.lean`,
`Model/Intype.lean`):

* the contract: `T := Intype sig`, `T.ctor : F T i → T i`, `T.fold : (∀ i, F S i → S i) →
  T i → S i` for a family `S` in any universe, `T.fold_ctor`, and `T.contract : Data.Contract`,
  whose `induction` field (for the canonical lifting `Data.All`) is instantiated at the packed
  index directly from `Signature.induction_of`;
* derived from the contract: `T.dtor` (Lambek), `T.dtor_ctor`, `T.ctor_dtor`,
  `T.ctor_injective`, `T.fold_eq`, `T.fold_unique`; the constructors `T.ctorᵢ` with `T.dtor_ctorᵢ`,
  `T.ctor_ctorᵢ`, `T.fold_ctorᵢ`, injectivity and disjointness, and `T.casesOn`, as for
  `codatatype`;
* the dependent recursor
  `T.rec : {motive : ∀ i, T i → Sort v} → minors → ∀ {i} (t : T i), motive i t`, with one minor
  premise per constructor carrying an induction hypothesis for each recursive argument
  (`∀ ys, motive _ (k ys)` under a telescope; for a nested argument `c`, by membership,
  `∀ t, PolyIso.Mem (fun X => G X) t c → motive _ t` (through `List`, `Option` and `Array` by
  theirs, `∀ t, t ∈ c → motive _ t`), also when its positions are at one index only after cases on
  them, or `IPolyIso.Mem` at an index when they are at several indices), registered as the
  `induction` eliminator, and its computation rules `T.rec_ctorᵢ` as simp lemmas, with the
  hypothesis of a nested argument `fun t _ => T.rec … t`. It is `T.Colean.recPos`, the recursor with
  the hypotheses of nested arguments at the positions of their structures, with these turned into
  membership (`PolyIso.memRec`); `T.Colean.recPos` is `Signature.rec_of` at the packed index, with
  the minor premises assembled by `casesOn` on `F T i` (`T.Colean.recAux`). The computation rules
  are propositional, since the generic recursor is built from `WellFounded.fix`.

The `Prop` instance of `T.rec` is induction with per-constructor hypotheses; the contract's
`induction` with the `Data.All` hypothesis is not curried for the user.
-/

open Lean Elab Command

namespace Codata

@[command_elab dataCmd] def elabData : CommandElab := Gen.elabDecl

end Codata
