import Colean.Gen.Command
import Colean.Gen.CCPO

/-!
# The `codatatype` command

Current scope: parameters, a single type, a mutual block or a mixed block of `codatatype` and
`datatype` declarations (`MutualCmd.lean`), any number of indices. Constructor
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
codatatype ITree (E : Type → Type) (R : Type)
  | Ret (r : R)
  | Tau (t : ITree E R)
  | Vis {X : Type} (e : E X) (k : X → ITree E R)

codatatype Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)
```

The command generates, with the parameters as arguments of every declaration (with the binder
annotations the user wrote for the types `T`, `T.F`, `T.Colean.Shape`, `T.Colean.B`, `T.Colean.sig`,
as `inductive` does, implicit elsewhere):

* `T.F (params) (X : Type _)`: the constructor list with `T params` replaced by `X`, as an inductive
  type; `T.F.fmap` and `T.F.Rel`, its action on functions and its lifting to relations, with the
  laws `T.F.fmap_id`, `T.F.fmap_comp`, `T.F.rel_fmap`, and the simp lemmas `T.F.fmap_ctorᵢ`;
* the signature: `T.Colean.Shape` (the constructors with their non-recursive data only, plus the
  shape `x_s` of each nested argument `x`) and `T.Colean.B : T.Colean.Shape → Type`, the positions
  for recursive arguments, one nullary constructor `ctorᵢ_t` per plain argument `t`, one unary
  constructor `ctorᵢ_f (p : A)` per function argument `f : A → T` and one `ctorᵢ_x (q : Pos x_s)`
  per nested argument (positions of its structure); bundled as `T.Colean.sig`;
* `T.Colean.toC`, `T.Colean.ofC` with the four laws `T.Colean.ofC_toC`, `T.Colean.toC_ofC`,
  `T.Colean.ofC_map`, `T.Colean.rel_ofC`;
* the contract: `T`, `T.dtor`, `T.corec`, `T.dtor_corec` (simp), `T.bisim`, transported from the
  generic `Signature` theorems; `T.corec` accepts a state in any universe;
* derived from the contract (`Codata.Contract`): `T.ctor`, `T.dtor_ctor` (simp), `T.ctor_dtor`,
  `T.ctor_injective`, `T.corec_eq`, `T.corec_unique`; the individual constructors `T.ctorᵢ` with
  the simp lemmas `T.dtor_ctorᵢ` and `T.ctor_ctorᵢ` (`T.ctor (T.F.ctorᵢ …) = T.ctorᵢ …`),
  injectivity `T.ctorᵢ_inj` (as `injEq`: proofs left out, `HEq` where the two sides' types differ,
  none when nothing is left) and disjointness `T.ctorᵢ_ne_ctorⱼ` where it is found (below), all
  simp lemmas;
* a case analysis principle `T.casesOn`, registered as the `cases` eliminator for `T`, with
  its computation rules `T.casesOn_ctorᵢ` as simp lemmas. It is the `induction` eliminator too:
  `codatatype` has no induction, and `induction s` is `cases s` rather than a look at the encoding.

The internals, which no user-facing statement mentions (the signature, the isomorphism and its
laws, the model's recursor, the instances of step 5), are under `T.Colean`. They are `protected`,
and so are `T.ctor`, `T.bisim`, `T.F`, `T.contract`, as `inductive` protects its auxiliary
constructions: after `open T` these are not `bisim`, …, only `T.bisim` and dot notation;
`protectedGen` (`Gen/Decl.lean`) has the list. The type, the constructors, the eliminators
`T.rec`, `T.casesOn` (as Lean leaves them), `T.fold`, `T.corec`, `T.dtor`, and the lemmas are not
protected. A constructor named as a generated declaration (`dtor`, `fold_eq`, `fmap`, the functor
having a constructor of each name) is refused before anything is declared (`checkCtorNames`,
`Gen/Front.lean`).

With indices (`codatatype T (params) : (i₁ : I₁) → I₂ → Type u`, constructors
`ctorᵢ … : T params idx₁ idx₂`), the same declarations are generated in their indexed form:
`T.F (params) (X : ∀ i₁ i₂, Type _) : ∀ i₁ i₂, Type _`, `T.F.fmap (f : ∀ j₁ j₂, X j₁ j₂ → Y j₁ j₂)`,
`T.Colean.Shape : ∀ i₁ i₂, Type _`, `T.Colean.B : ∀ i₁ i₂, T.Colean.Shape i₁ i₂ → ∀ j₁ j₂, Type _`
(a position records the indices of its recursive argument), `T : ∀ i₁ i₂, Type _`, `T.dtor {i₁ i₂}`,
`T.corec (c : ∀ j₁ j₂, S j₁ j₂ → T.F S j₁ j₂) {i₁ i₂}`, `T.bisim (R : ∀ j₁ j₂, …)`, a motive
`∀ j₁ j₂, T j₁ j₂ → Sort _` for `T.casesOn`, and so on. The index binders carry the names the user
gave them. Where a result index mentions the constructor's arguments, injectivity shares them
between its two sides, as `injEq` does for `inductive`
(`Vec.cons_inj : Vec.cons a v = Vec.cons a' v' ↔ a = a' ∧ v = v'` at one `n`), and the arguments it
shares may be implicit. Disjointness is stated where reducible unification finds where the result
indices of the two constructors meet, at the arguments where they meet; there is none when they
cannot meet (`Vec.nil` and `Vec.cons`), nor when unification does not find where they do (`T 0` and
`T (n * 2)`).

The generic theory (`Framework.lean`, `Model/Cotype.lean`) has one index type. Several indices are
packed into one, `T.Colean.Ix (params) := (i₁ : I₁) ×' I₂` (a `PSigma`, so indices may be
propositions), and no index is `Unit`; the user-facing declarations are curried: the internal
isomorphism `T.Colean.toC`/`T.Colean.ofC` with its three laws takes the family on the packed index,
and the instantiations of the generic theorems convert between the two forms with lambdas
(`fun j₁ j₂ => f ⟨j₁, j₂⟩`, `fun p => c p.1 p.2`), so that every statement above is definitionally
the generic one. With one index nothing is packed.

Only the laws of the generated inductive `T.F` (`fmap_id`, `fmap_comp`, `rel_fmap`, `ofC_toC`,
`toC_ofC`, `ofC_map`, `rel_ofC`) are proved by tactics on goal metavariables, `cases` followed
by `rfl`, `simp only` or `solve_by_elim`, with the laws of `Model/Occ.lean` for nested arguments;
everything else instantiates a theorem of the theory. Every declaration is noncomputable: the
encoding decides equality of shapes classically, and a `PolyIso` instance may be noncomputable
too.

The declaration is analysed (`Gen/Front.lean`) and the generated declarations are built as
`Expr`s and added directly, by the generators of `Gen/`, split by steps:
`Gen/Functor.lean` (step 1), `Gen/Signature.lean`, `Gen/Iso.lean`,
`Gen/Model.lean` (step 2), `Gen/Extras.lean` (step 2b), `Gen/Framework.lean` (step 3),
`Gen/Rel.lean` and `Gen/Surface.lean` (step 4), `Gen/Derive.lean` (step 5); `Gen/Command.lean`
is the pipeline, shared with the `datatype` command (`DataCmd.lean`), which differs only in the
contract and what is derived from it, and with mutual blocks (`MutualCmd.lean`); `T.F.Rel`,
`rel_fmap` and `rel_ofC` are generated for `codatatype` only.

The attribute `with_ccpo` (`Syntax.lean`), off by default, gives a declared type the order of
approximation, Lean's `Lean.Order.CCPO`, with which `partial_fixpoint` defines corecursive
functions into it, and the monotonicity lemmas of its constructors (`Gen/CCPO.lean`): applied
after the declaration, `attribute [with_ccpo] T`, or among the declaration's modifiers,
`@[with_ccpo] codatatype T …`, applied once everything is declared, as `inductive` applies its
attributes. The bottom is the first constructor without arguments, or the one named by
`with_ccpo (bot := c)`.

The declaration is parsed as Lean's `inductive` (`Syntax.lean`): doc comments, attributes,
`private`, `protected` and `noncomputable` on the type and on the constructors, universe names
`T.{u}` and `where`, handled as `inductive` handles them (`DeclStx.elabMods`, `Gen/Front.lean`).
-/

open Lean Elab Command

namespace Codata

@[command_elab codataCmd] def elabCodata : CommandElab := Gen.elabDecl

/-- The attribute `with_ccpo` (`Syntax.lean`), on a `codatatype`: `Gen/CCPO.lean`. A failure is
an error of the attribute, which then declares nothing. -/
initialize registerBuiltinAttribute {
  name := `with_ccpo
  descr := "the order of approximation on a `codatatype`, for `partial_fixpoint`"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == .global do throwError "with_ccpo: the attribute is global only"
    let bot? := match stx with
      | `(attr| with_ccpo (bot := $c:ident)) => some c.getId
      | _ => none
    let env ← getEnv
    try
      withRef stx <| Term.TermElabM.run' (Gen.CCPO.genCCPO decl bot?) |>.run'
    catch e =>
      setEnv env
      throw e
  erase := fun _ => throwError "with_ccpo: the attribute cannot be erased"
}

end Codata
