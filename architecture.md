# Architecture of `Colean/`

A declaration `codata T … | …` or `data T … | …`, or a `mutual` block of them, is processed in
steps with fixed boundaries; a `mixed_mutual` block runs them on each of its runs (see "Mixed
blocks"). Each step sees only the outputs of the steps above it; each has one
file of theory and one generator file.

| Step | Sees | Produces | Proofs |
|---|---|---|---|
| 1. Functor | the declaration | `T.F`, `T.F.map`, `map_id`, `map_comp` | tactic, per declaration |
| 2. Model | `T.F` | `T.contract : Contract T F` (a signature, an isomorphism `F X ≃ σ.Obj X`, the fixpoint on `Raw`) | the isomorphism's laws by tactic; the rest instantiated |
| 2b. Model extras | the model | polymorphic `fold`/`corec`, `T.recPos`, `T.rec` | instantiated |
| 3. Framework | `T.contract` only | `ctor`, `dtor_ctor`, `ctor_dtor`, `ctor_injective`, `corec_eq`, `corec_unique` and the data duals | none: instantiation of generic theorems |
| 4. Surface | the constructor list and steps 2–3 | `T.cᵢ` with their lemmas, `casesOn`, `rec_cᵢ`, `fold_cᵢ`, the characterisation `T.F.Rel`, the types, aliases and per-type recursors of a block | term assembly |
| 5. Instances | a declared type, family or block | `PolyIso`/`PolyMap` instances for it (`T.Poly.*`), and the `simp` lemmas `T.Poly.map_cᵢ`, `T.Poly.mem_cᵢ` | the layer's laws by tactic; the fixpoint instantiated; the lemmas by a theorem of `Model/Poly.lean` and definitional unfolding (map), cases on the positions of a layer (membership) |

## Files

Theory, in dependency order:

- `Raw.lean`: the general type `Raw I L := List I → Option L` (the model's carrier).
- `PolyIso.lean`: the user interface for nesting: `PolyIso` and `PolyMap` (and `IPolyIso`, `IPolyMap` for functors on families) say that a functor is isomorphic to a polynomial functor, and `PolyIso.Mem` (`IPolyIso.Mem`, at an index) says what the members of a value are. Instances for constants, the identity, `List`, `Option`, `Array`, and for products, sums, functions, dependent pairs and composites of functors with instances, with `simp` lemmas for membership through all of them. Depends on Mathlib only.
- `Framework.lean`: `Codata.Rel`, `Codata.Contract`, `Data.All`, `Data.Contract` and every theorem that follows from a contract alone. Depends on Mathlib only.
- `Model/Cotype.lean`: signatures, the container functor `Obj`, the encoding, the greatest fixpoint `IsWf`, `Cotype`, its contract pieces and the transport theorems to a functor `F ≃ Obj`.
- `Model/Intype.lean`: the least fixpoint `IsFin`, `Intype`, the dependent recursor by well-founded recursion, fold, and the transports.
- `Model/Poly.lean`: a least or greatest fixpoint of a layer polynomial in a parameter is polynomial in that parameter: trees of shapes, `Path`, `PolyFix`, `coFix`, `inFix`; for a family, at every index (`ILay`, `IPath`, `IPolyFix`, `icoFix`, `iinFix`), on the total space of the plain case. The map through a right inverse of the destructor (`map_eq_of_d`) and membership in one step (`exists_val_iff`), for the `simp` lemmas of step 5.
- `Model/Occ.lean`: occurrence structures `Occ`/`IOcc`, internal to the command: their combinators, laws and computation lemmas (`simp`, for `IOcc` as for `Occ`); the leaves are `Occ.ofIso F`, from the `PolyIso` instances, and the instances of the built-in forms are the combinators by definition (`Occ.ofIso_prod`, …, `simp` lemmas but for the identity's).
- `Model/Occ2.lean`: occurrence structures in two variables `Occ₂`, `G X Y ≃ Lay PX PY X Y` with the layer of `Model/Poly.lean`, for a field with a parameter and the recursion in one argument: combinators, laws, the computation of the map, `AgreeY`, the agreement of its map in `Y` with that of the structure in `Y` alone, and membership in each variable (`MemX`, `MemY`, `simp` through the combinators).
- `Model/IOcc2.lean`: the same over a family, `IOcc₂`, the recursive variable a family over an index, each position in it at its index (the layer of `ILay`), for families and blocks: combinators, among them a plain structure at one index (`ofOcc₂`), laws, the map, `AgreeY` with the indexed structure in `Y` alone read along a map of the indices, and membership, a member in `Y` with its index.

Generators, on `Expr`, in dependency order. `Syntax.lean` holds the command syntax.

- `Gen/Decl.lean`: adding declarations from closed `Expr`s, each checked by the kernel before the next: inductive types with the auxiliary constructions of `inductive` (fixed indices promoted to parameters, as `inductive` does), noncomputable definitions, theorems by term or by a tactic on a goal metavariable, simp lemmas and other attributes; definitions by cases (`mkCasesOnApp`).
- `Gen/Occ.lean`: the occurrence structure of an elaborated argument type, by recursion on its head after `whnfR` (and `id`); instance search at leaves.
- `Gen/Ctx.lean`: the context `Ctx`: parameters (section variables first), indices and constructor arguments as free variables of one `TermElabM` run, the types being defined as local variables at a placeholder universe, argument kinds, names; for a block, its index `Blk.Ix`.
- `Gen/Front.lean`: syntax → `Ctx`, elaborating the declarations as `inductive` does, a single one or the types of a block, or a run of a mixed block with the other runs' types replaced (`Mix`).
- `Gen/Functor.lean`: step 1.
- `Gen/Signature.lean`, `Gen/Iso.lean`, `Gen/Model.lean`: step 2 (the signature; the isomorphism and its laws; the type and the contract).
- `Gen/Rel.lean`: `T.F.Rel`, `rel_map`, `rel_ofC` (step 4, generated before the model, see below).
- `Gen/Framework.lean`: step 3.
- `Gen/Extras.lean`: step 2b (`T.recPos`, `T.rec`), and the instance of an occurrence structure (`isoOf`).
- `Gen/Surface.lean`: step 4 (constructors and their lemmas, `casesOn`, `rec_cᵢ`, `fold_cᵢ`; in a block, the types `Tₘ`, the aliases and, for `data`, the recursors `Tₘ.rec` per type).
- `Gen/Derive.lean`: step 5, separate from the pipeline (see below).
- `Gen/Command.lean`: the pipeline. `CodataCmd.lean`, `DataCmd.lean`: the commands; `MutualCmd.lean`: `mutual` blocks of them, and `mixed_mutual` blocks.
- `Gen/Mixed.lean`: a `mixed_mutual` block: its runs, the pipeline on each, the closed types of the runs inside, their membership instances, and their interface restated at the closed types.

## The generators

The commands read the user's syntax only to elaborate it. `Gen/Front.lean` elaborates a
declaration as Lean's `inductive` does: the parameters and the declared sort, then the types being
defined as local variables, against which each constructor is elaborated to one telescope. Every
later decision is taken on the elaborated types, after `whnfR`: an occurrence is an application of
one of these variables to the parameters (and indices), and products, sums, functions, dependent
pairs and leaves are recognised by their head. So spellings that mean the same type are one
(`A × B` and `Prod A B`, an abbreviation, `id A`, `Σ`, `<|`, an arrow-form constructor), and no
generated name can capture a user's. Before the types are declared, the names are checked (no
type twice in a block; no type, block or index of a block declared already: `checkNames`), and so
is a universe written in a declared sort, against the model's, which is the types' (`checkSorts`,
first in the pipeline; in a mixed block, of the closed types, before the outermost run).

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

- Tactic proofs are the laws of the generated inductives: the functor laws (step 1), the isomorphism laws and the lifting laws (steps 2 and 4), and in step 5 the laws of the layer, the rewriting steps of the fixpoint and the cases on the positions of a layer (membership). Everything else instantiates a theorem of `Framework.lean` or `Model/`.
- The framework never mentions a model, a signature or `Raw`; the model never mentions a declaration; the surface never proves anything.
- A nested argument enters the model as a shape with positions; the user-facing `F` keeps its type.
- Some generated proofs need the definitional unfolding of Lean before 4.34 (`withUnfolding`, around those proofs only): a term of the signature is the expected one only after unfolding.

## Recursors

The recursor `T.rec` is user-facing, so its type mentions only the user's types and the
user-facing classes. Its induction hypothesis for a nested argument `c` is by membership,
`∀ t, PolyIso.Mem (fun X => G X) t c → motive t`, with the argument's type `G` as a function of
the occurrences and, as its instance, the occurrence structure of the argument read as an
instance (`isoOf`): a leaf is `Occ.ofIso` of its instance, and the instances of the built-in
forms are the combinators by definition. In a family the hypothesis is by `IPolyIso.Mem` at an
index unless every position is at one index (the index of a position at variables mentions
neither the shape nor the position, or does after cases on it through products, `T n × T n`);
then the instance is a `PolyIso` at that index (`flat`), and in the second case the hypothesis at
the positions is brought to that index by these cases (`bridgeIH`, a `Sum.casesOn` term), and the
rule `T.rec_cᵢ` by the same cases (`bridgeEq`).

The structure of a nested argument, and so the instance of its hypothesis, is the one instance
search finds for the argument's functor: a leaf is a partial application when the occurrences are
in its last argument, and the whole type as a function of them otherwise (`wholeLeaf`): with
occurrences in several arguments, and in an argument other than the last when instance search
finds an instance for the whole (`Vec (List T) n` is `Vec`'s instance at `List`, not the
composite; `E (T × Nat) Nat` is `E`'s at the product). `simp` computes the map at the premise of
such an instance, a leaf or a built-in form (`Occ.ofIso_prod`, …).

`T.recPos` is the recursor of the model, with the hypotheses at the positions of the structures.
`T.rec` is `T.recPos` at minor premises that turn these hypotheses into membership
(`PolyIso.memRec`, by `Classical.choose`, with no proof in between since the instance is the
structure), and its rules `T.rec_cᵢ` are `T.recPos_ctor` followed by `PolyIso.memRec_pos` at
each nested argument.

## Known boundary violations

- `T.corec`, `T.fold` (universe-polymorphic in the state) and `T.recPos` come from the model, because `Contract` fixes one universe for `F`. Fix: a universe-polymorphic framework interface, after which the recursor derives from `fold` and `induction`.
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
unfolding, and its rules `Tₘ.rec_cᵢ` are the block-level rules `Blk.rec_cᵢ` by unfolding. A
hypothesis by membership at an index of the block (`IPolyIso.Mem`) is one per type of the
argument in `Tₘ.rec`, each at its type's motive, and `Blk.rec`'s is given to each at its
constructor of `Blk.Ix`.

A block mixing `data` and `codata` is a nested fixpoint, whose order is a choice; `mutual`
rejects such a block, and `mixed_mutual` states the order (next section).

## Mixed blocks

A `mixed_mutual` block is a sequence of runs, maximal sequences of adjacent declarations of the
same kind, the first outermost (`Gen/Mixed.lean`). The whole block is elaborated once, as
`mutual` would (`mixedVars`, discarded), for its section variables and for which declaration
mentions which; from these, the outer runs each run needs (`mixReach`: those it mentions, and
those the runs inside it that it mentions need), and the runs that nest through each. The
indices `Blk.Ix` of the runs that are blocks come next, on the declared parameters.

The runs inside the first are declared from the innermost out, each by the pipeline as a single
type or a block whose parameters end with one `X` per outer run it needs: the front end
(`withCtx` with a `Mix`) elaborates the run's constructors with every declaration of the block as
a local variable, then replaces the occurrences of an outer run's types by its `X` and those of a
run inside by that run's open type at the families of the runs it needs (`mixFam`), so the
analysis sees a declaration with parameters and nested occurrences, nothing new. Its names are
internal, `Tₘ.Open` (and `Blk.Open`). Step 5 gives the open types their instances in the `X`s,
through which the runs outside nest; when one of them does, a failure of step 5 is an error.

The first run is declared by the pipeline with a hook after its types (`closeTypes`): the closed
types `Tₘ params := Tₘ.Open params (fams)` of the runs inside, abbreviations, from the outermost
of them in, at the closed families of the runs each needs, and for each run that nests through a
closed type of one type without indices, the instance `Membership` of its members. The rest of
the pipeline states its declarations with these (`Ctx.foldTy`, through the arguments of the
constructors, `withTArgs`, and the hypotheses by membership, `memProp`): a term `Tₘ.Open params
(fams)` at the closed families is written `Tₘ params`, and `PolyIso.Mem` through it `x ∈ c`
(`foldClosed`).

Then the interface of each run inside is restated at the closed types (`restateRun`): every
public declaration `Tₘ.Open.d` (not those of the model or of step 5, nor the auxiliary
constructions of inductive types) as `Tₘ.d`, its statement that of `Tₘ.Open.d` at the closed
families written with the closed declarations, its value `Tₘ.Open.d` itself, with its
attributes (`simp`, the eliminators, `elab_as_elim`); an inductive type (`T.F`) becomes a
reducible definition and its constructors reducible definitions usable in patterns, the
constructors `Tₘ.c` reducible too, so that the lemmas of the open types, those of step 5 among
them, apply to the closed ones. Last, the `simp` lemmas `Tₘ.mem_c` of the membership instances,
the `simp` normal form of the membership through the open types (`memLemmas`). The names the user
wrote are the closed declarations in the info tree.

The functor of a run at its state keeps the open types of the runs inside at that state
(`Tree.F α X ∋ node (a : α) (children : Forest.Open α X)`): there is no closed form for it.

## Nesting and declared types

Defining a type and presenting it as a polynomial functor are separate steps. Step 5,
`deriveInstances` (`Gen/Derive.lean`), runs after the pipeline has finished, in the same run: it
reads the declaration's context and the type's public declarations, and nothing in the pipeline
depends on it. On failure it restores the state and logs a warning, so it can't affect the type.

It generates one instance per type, `PolyIso (fun X => T (H₁ X) … (Hₙ X))` with premises on the
`Hᵢ`, over the parameters that may vary, and the eta-reduced form `T A₁ … Aₙ₋₁`. Only the layer
`T.Poly.toL`/`ofL` and its laws are per declaration; the fixpoint is `Model/Poly.lean`, one proof
for `data` and `codata`, from the contract. The structure of a field in the parameters is that of
`Gen/Occ.lean`, with each premise's structure at its parameter; a field may mention several, and
when it has no structure in all of them the first ones are kept constant until the others have
one (`refineHoles`).

The layer is presented constructor by constructor of the presentation (`VCtor`): those of `T`,
with a nested argument split through its products and sums when it mentions a parameter that
varies outside the occurrences (`p : α × T α`, `f : T α ⊕ α`), or with indices has its positions at
an index only after cases on them (`T n × T (n + 1)`, `A × B` in a block). Its parts are fields at
parameter positions, recursive arguments or data, as arguments of their own; through a sum the
constructor is one constructor of the presentation per side. `toL` takes the parts by projections
and `Sum.casesOn` (`polyDispatch`), `ofL` puts them together (`applyVCtor`), and the laws do cases
on the split arguments (`polyDestructure`). The `simp` lemmas below are per constructor of the
presentation, stated with the parts (`p.1`, `p.2`, `T.c (Sum.inl a)`).

Under a named type constructor or a function the split stops: a part with a parameter and the
type (`p : List (α × T α)`, `k : Nat → α × T α`, `p : List (α ⊕ T α)`) has positions of both
kinds, and an occurrence structure in two variables (`Occ₂`, `Model/Occ2.lean`; `mixOcc`), built
from its structure in the occurrences alone (the parameter constant, as in `T.F`) by going through
its combinators down to parts in the parameters (`Occ₂.ofX`, at their structure in the premises)
and parts in the occurrences (`Occ₂.ofY`). Such an argument is presented with a shape, a position
in `P` and one in `B`, its layer is `Occ₂.toC`, and in `ofL_map` the map of `T.F` on it, by its
structure in the occurrences, is its map in them by `Occ₂.AgreeY`, proved combinator by
combinator.

With indices the structure is over the index of the presentation (`IOcc₂`, `Model/IOcc2.lean`;
`imixOcc`), its occurrences at the presentation's indices, so that the positions of the layer
carry them by construction; in a block, a nested argument whose positions are at a type of the
block only after cases on them inside a named type constructor (`p : List (RA α × Nat)`) is
presented so too, with no part in the parameters. When the positions are at one index after cases
(`oneIdx₂`), the structure is the plain one at that index (`IOcc₂.ofOcc₂`), whose map and members
are those of the plain one by definition, and the rules are stated as without indices, at the
type of the members. In `ofL_map` the map of `T.F`, by the family's indexed structure over its
own index, is its map by `IOcc₂.AgreeY`, along `ι`, the identity or `Blk.Poly.ixIn`; for a plain
structure at one index, from the plain agreement and the indexed structure at that index, by
unfolding (`IOcc₂.AgreeY.ofOcc₂`).

A family gets the instances at every index, `PolyIso (fun X => T (H X) idx)` with `idx` arguments
of the instance; its presentation is a family over the packed index, with the index of each
position (`T.Poly.idx`, `T.Poly.sig`), and the layer at an index `i` is `ILay`. The types of a
block get theirs at their index of the block: the presentation is per block (`Blk.Poly.*`), over
`Blk.Poly.Ix`, which is `Blk.Ix` without the parameters that vary (`Blk.Ix` takes them all, so it
cannot index trees of shapes that do not depend on them), read in the block's index along
`Blk.Poly.ixIn`; the instances are per type (`Tₘ.Poly.instPolyIso`), with the eta forms for a
type without indices. The theory takes the contract along this map (`ico_bisim`, `iin_ind`), and
`corec` and `fold` on states over the presentation's index through `Along` and `Over`.

Scope: in a block, a nested argument with positions at several types of the block inside a named
type constructor (`List (A × B)`) gets its instances but not its `simp` lemmas, which state the
members by the type of each; the step warns. A parameter in the same field as the type is
constant there when the field has no structure in two variables: in another argument of a leaf
than the type (`List (E α (T α))`), or under a functor on families. A parameter that is a family
(`IPolyIso`) is not supported: `Model/Poly.lean` has the fixpoint for a parameter that is a
type.

With the instances come, per constructor `c` of each type, two `simp` lemmas at the premises
(`genPolySimp`), so that `simp` computes through the instances in the rules of other types:

- `T.Poly.map_c`: `(Occ.ofIso fun X => T (H X) idx).map (Occ.ofIso fun X => T (H' X) idx) f
  (T.c args) = T.c args'`, data unchanged, a field at a parameter position mapped by its
  structure in the premises (`(Occ.ofIso H).map (Occ.ofIso H') f a`, `f a` by `simp` at the
  identity), a recursive argument by this map, a nested one by the map of its structure. It is
  stated on the leaf `Occ.ofIso`, as the other types' rules (`fold_c`, `F.map_c`, `dtor_corec`)
  mention the map: a rule on `PolyMap.map`, whose functor is implicit, would make `simp` solve
  `?H ?X =?= T` first and not apply at the identity premise. `Occ.map_ofIso` relates the two.
  An argument with a structure in two variables is mapped by `Occ₂.map`, by `f` in the parameter
  and by this map in the occurrences; at several indices of a family by `IOcc₂.map`, at each
  index by the map of the leaf there. The proof is `PolyFix.map_eq_of_d` at `ctor ∘ ofL` after
  `dtor_c`; the right-hand side is then the result by definition.
- `T.Poly.mem_c`: `PolyIso.Mem (fun X => T (H X) idx) x (T.c args) ↔ …`, a disjunct per field
  at a parameter position and per recursive argument (through a nested one, `∃ t, Mem G t c ∧
  Mem … x t`), `False` without any; an argument with a structure in two variables has two, by its
  structure in the parameter alone (the occurrences constant) and in the occurrences alone, whose
  positions are those of the structure in two variables by definition, or across a sum, where they
  are not, by `Occ₂.MemX` and `∃ t, Occ₂.MemY o t c ∧ …`, which `simp` computes through the
  combinators (a member with a property first, `simp ↓`, then the membership); at several indices
  of a family by `IOcc₂.MemX` and `IOcc₂.MemY`, a member with its index. It holds for `codata` as
  well: a slot is a finite path. The proof is `PolyFix.exists_val_iff` after `dtor_c`, then cases
  on the positions of the layer.

Both are stated on the constructors for `codata` too (a value is the constructor of its `dtor`,
and `corec_eq` writes a corecursive one so). The functors of the left-hand sides are not indexed,
since the leaves of other rules are often eta-reduced (`Occ.ofIso Forest`). A failure of the
lemmas is a warning that rolls back only them.
