import Colean.Gen.Command

/-!
# The `codata` command

Current scope: parameters, a single type, a mutual block or a mixed block of `codata` and `data`
declarations (`MutualCmd.lean`), any number of indices. Constructor
binders may be explicit or implicit; recursive arguments may be plain (`t : T params idx`),
under a telescope of arrows (`f : (y₁ : B₁) → … → Bₙ → T params idx`), dependent or not, where
the domains may depend on the constructor's own data and the index on the bound variables, or
*nested*: any other type mentioning `T`, built from occurrences by products, sums, functions
and dependent pairs over constant types, and named type constructors with `PolyIso` and
`PolyMap` instances (`List`, `Option`, `Array`, and the user's; see `PolyIso.lean`):
`children : List (T params idx)`, `p : T params i × T params j`, `k : A → List (T params idx)`,
`c : Option (T params idx × T params idx)`, `List (Option (T params idx))`, …. The structure of
the argument type is built by recursion on its elaborated type (`Gen/Occ.lean`), with instance
search only at the named constructors. A declared type, a family or the types of a block, is
given such instances when its parameters allow it, at every index (step 5, `Gen/Derive.lean`), so
that a later declaration can nest through it; for other types the user provides them.

```
codata ITree (E : Type → Type) (R : Type)
  | Ret (r : R)
  | Tau (t : ITree E R)
  | Vis {X : Type} (e : E X) (k : X → ITree E R)

codata Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)
```

The command generates, with the parameters as arguments of every declaration (with the binder
annotations the user wrote for the types `T`, `T.F`, `T.Shape`, `T.B`, `T.sig`, as `inductive`
does, implicit elsewhere):

* `T.F (params) (X : Type _)`: the constructor list with `T params` replaced by `X`, as an
  inductive type; `T.F.map` and `T.F.Rel`, its action on functions and its lifting to relations,
  with the laws `T.F.map_id`, `T.F.map_comp`, `T.F.rel_map`, and the simp lemmas `T.F.map_ctorᵢ`;
* the signature: `T.Shape` (the constructors with their non-recursive data only, plus the shape
  `x_s` of each nested argument `x`) and `T.B : T.Shape → Type`, the positions for recursive
  arguments, one nullary constructor `ctorᵢ_t` per plain argument `t`, one unary constructor
  `ctorᵢ_f (p : A)` per function argument `f : A → T` and one `ctorᵢ_x (q : Pos x_s)` per nested
  argument (positions of its structure); bundled as `T.sig`;
* `T.toC`, `T.ofC` with the four laws `T.ofC_toC`, `T.toC_ofC`, `T.ofC_map`, `T.rel_ofC`;
* the contract: `T`, `T.dtor`, `T.corec`, `T.dtor_corec`, `T.bisim`, transported from the
  generic `Signature` theorems; `T.corec` accepts a state in any universe;
* derived from the contract (`Codata.Contract`): `T.ctor`, `T.dtor_ctor`, `T.ctor_dtor`,
  `T.ctor_injective`, `T.corec_eq`, `T.corec_unique`; the individual constructors `T.ctorᵢ` with
  the simp lemmas `T.dtor_ctorᵢ` and `T.ctor_ctorᵢ` (`T.ctor (T.F.ctorᵢ …) = T.ctorᵢ …`),
  injectivity `T.ctorᵢ_inj` (as `injEq`: proofs left out, `HEq` where the two sides' types differ,
  none when nothing is left) and disjointness `T.ctorᵢ_ne_ctorⱼ` where it is found (below), all
  simp lemmas;
* a case analysis principle `T.casesOn`, registered as the `cases` eliminator for `T`, with
  its computation rules `T.casesOn_ctorᵢ` as simp lemmas.

With indices (`codata T (params) : (i₁ : I₁) → I₂ → Type u`, constructors
`ctorᵢ … : T params idx₁ idx₂`), the same declarations are generated in their indexed form:
`T.F (params) (X : ∀ i₁ i₂, Type _) : ∀ i₁ i₂, Type _`, `T.F.map (f : ∀ j₁ j₂, X j₁ j₂ → Y j₁ j₂)`,
`T.Shape : ∀ i₁ i₂, Type _`, `T.B : ∀ i₁ i₂, T.Shape i₁ i₂ → ∀ j₁ j₂, Type _` (a position records
the indices of its recursive argument), `T : ∀ i₁ i₂, Type _`, `T.dtor {i₁ i₂}`,
`T.corec (c : ∀ j₁ j₂, S j₁ j₂ → T.F S j₁ j₂) {i₁ i₂}`, `T.bisim (R : ∀ j₁ j₂, …)`, a motive
`∀ j₁ j₂, T j₁ j₂ → Sort _` for `T.casesOn`, and so on. The index binders carry the names the
user gave them. Where a result index mentions the constructor's arguments, injectivity shares
them between its two sides, as `injEq` does for `inductive`
(`Vec.cons_inj : Vec.cons a v = Vec.cons a' v' ↔ a = a' ∧ v = v'` at one `n`), and the
arguments it shares may be implicit. Disjointness is stated where reducible unification finds
where the result indices of the two constructors meet, at the arguments where they meet; there is
none when they cannot meet (`Vec.nil` and `Vec.cons`), nor when unification does not find where
they do (`T 0` and `T (n * 2)`).

The generic theory (`Framework.lean`, `Model/Cotype.lean`) has one index type. Several indices are packed into one,
`T.Ix (params) := (i₁ : I₁) ×' I₂` (a `PSigma`, so indices may be propositions), and no index is
`Unit`; the user-facing declarations are curried: the internal isomorphism `T.toC`/`T.ofC` with
its three laws takes the family on the packed index, and the instantiations of the generic
theorems convert between the two forms with lambdas (`fun j₁ j₂ => f ⟨j₁, j₂⟩`,
`fun p => c p.1 p.2`), so that every statement above is definitionally the generic one. With one
index nothing is packed.

Only the laws of the generated inductive `T.F` (`map_id`, `map_comp`, `rel_map`, `ofC_toC`,
`toC_ofC`, `ofC_map`, `rel_ofC`) are proved by tactics on goal metavariables, `cases` followed
by `rfl`, `simp only` or `solve_by_elim`, with the laws of `Model/Occ.lean` for nested arguments;
everything else instantiates a theorem of the theory. Every declaration is noncomputable: the
encoding decides equality of shapes classically, and a `PolyIso` instance may be noncomputable
too.

The declaration is analysed (`Gen/Front.lean`) and the generated declarations are built as
`Expr`s and added directly, by the generators of `Gen/`, split by the steps of
`architecture.md`: `Gen/Functor.lean` (step 1), `Gen/Signature.lean`, `Gen/Iso.lean`,
`Gen/Model.lean` (step 2), `Gen/Extras.lean` (step 2b), `Gen/Framework.lean` (step 3),
`Gen/Rel.lean` and `Gen/Surface.lean` (step 4), `Gen/Derive.lean` (step 5); `Gen/Command.lean`
is the pipeline, shared with the `data` command (`DataCmd.lean`), which differs only in the
contract and what is derived from it, and with mutual blocks (`MutualCmd.lean`); `T.F.Rel`,
`rel_map` and `rel_ofC` are generated for `codata` only.
-/

open Lean Elab Command

namespace Codata

@[command_elab codataCmd] def elabCodata : CommandElab := Gen.elabDecl

end Codata
