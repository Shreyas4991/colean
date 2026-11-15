# Architecture of `Colean/`

A declaration `codatatype T … | …` or `datatype T … | …`, or a `mutual` block of them, is processed
in steps with fixed boundaries; a `mixed_mutual` block runs them on each of its runs (see "Mixed
blocks"). Each step sees only the outputs of the steps above it; each has one
file of theory and one generator file.

| Step | Sees | Produces | Proofs |
|---|---|---|---|
| 1. Functor | the declaration | `T.F`, `T.F.fmap`, `fmap_id`, `fmap_comp` | tactic, per declaration |
| 2. Model | `T.F` | `T.contract : Contract T F` (a signature, an isomorphism `F X ≃ σ.Obj X`, the fixpoint on `Raw`) | the isomorphism's laws by tactic; the rest instantiated |
| 2b. Model extras | the model | polymorphic `fold`/`corec`, `T.Colean.recPos`, `T.rec` | instantiated |
| 3. Framework | `T.contract` only | `ctor`, `dtor_ctor`, `ctor_dtor`, `ctor_injective`, `dtor_injective`, `dtor_inj` (`simp`), `corec_eq`, `corec_unique` and the data duals | none: instantiation of generic theorems |
| 4. Surface | the constructor list and steps 2–3 | `T.cᵢ` with their lemmas, `T.dtor_eq_cᵢ_iff`, `casesOn`, `rec_cᵢ`, `fold_cᵢ`, the characterisation `T.F.Rel` with one step of it at two constructors `T.F.rel_cᵢ_cⱼ` (`simp`), `T.F.Rel.mono`, `T.F.rel_refl`, and coinduction up to equality `T.coinduct`; in a block the types, and per type the interface of a single type with a family per type of the block: the layer `Tₘ.F` with its constructors `Tₘ.F.cᵢ`, map, lifting and laws, `dtor`, `ctor`, Lambek's lemma and `dtor_inj`, and `corec`, `dtor_corec`, `corec_eq`, `corec_unique`, `bisim`, `coinduct`, the lemmas of the lifting (`codatatype`) or `fold`, `fold_ctor`, `fold_eq`, `fold_unique`, `fold_cᵢ`, `rec` (`datatype`) | term assembly; by cases on the block's index, and two lemmas, between the block's family and the types packed by cases; the one-step lemmas and `Rel.mono` by cases on the lifting (in general position) and its constructor |
| 5. Instances | a declared type, family or block | `PolyIso`/`PolyMap` instances for it (`T.Colean.Poly.*`), and the `simp` lemmas `T.Colean.Poly.map_cᵢ`, `T.Colean.Poly.mem_cᵢ` | the layer's laws by tactic; the fixpoint instantiated; the lemmas by a theorem of `Model/Poly.lean` and definitional unfolding (map), cases on the positions of a layer (membership) |
| 6. Order (`with_ccpo`, off by default) | a declared `codatatype`, single, with at most one index | `T.instCCPO : Lean.Order.CCPO`, `T.approx_iff`, `T.approx_coind`, `T.bot_eq`, the monotonicity lemmas `T.monotone_cᵢ` | none for the order: `Model/CCPO.lean` instantiated; the bottom's positions empty by `cases`; the lemmas by the constructor of `T.F.Rel` |

## Files

Theory, in dependency order:

- `Raw.lean`: the general type `Codata.Raw I L := List I → Option L` (the model's carrier).
- `PolyIso.lean`: the user interface for nesting: `PolyIso` and `PolyMap` (and `IPolyIso`, `IPolyMap` for functors on families) say that a functor is isomorphic to a polynomial functor, and `PolyIso.Mem` (`IPolyIso.Mem`, at an index) says what the members of a value are. Instances for constants, the identity, `List`, `Option`, `Array`, and for products, sums, functions, dependent pairs and composites of functors with instances, functors on families among them, with `simp` lemmas for membership through all of them (through a sum at any value, `mem_sum`), and for a property of every member, or of some member, at any index, rewritten before the membership inside (`simp ↓`, `IPolyIso.forall_mem_prod`, `exists_mem_compC`, …) so that the index and the member are taken away at the holes (`forall_eq_heq_imp`, `exists_eq_heq_and`, …). Depends on Mathlib only.
- `Framework.lean`: `Codata.Rel`, `Codata.Contract`, `Data.All`, `Data.Contract` and every theorem that follows from a contract alone; and `rel_of_map_heq`, a lifting of relations read along a map between equal families, for the bisimulation per type of a block. Depends on Mathlib only.
- `Model/Cotype.lean`: signatures, the container functor `Obj`, the encoding, the greatest fixpoint `IsWf`, `Cotype`, its contract pieces and the transport theorems to a functor `F ≃ Obj`.
- `Model/Intype.lean`: the least fixpoint `IsFin`, `Intype`, the dependent recursor by well-founded recursion, fold, and the transports.
- `Model/Poly.lean`: a least or greatest fixpoint of a layer polynomial in a parameter is polynomial in that parameter: trees of shapes, `Path`, `PolyFix`, `coFix`, `inFix`; for a family, at every index (`ILay`, `IPath`, `IPolyFix`, `icoFix`, `iinFix`), on the total space of the plain case. The map through a right inverse of the destructor (`map_eq_of_d`) and membership in one step (`exists_val_iff`), for the `simp` lemmas of step 5.
- `Model/Occ.lean`: occurrence structures `Occ`/`IOcc`, internal to the command: their combinators, laws and computation lemmas (`simp`, for `IOcc` as for `Occ`; the map through a sum at any value as `Sum.map`, `map_sum`), the relation of two values through the combinators down to the leaves (`rel_prod`, …, `rel_list` as `List.Forall₂`, `rel_option` as `Option.Rel`, `rel_array` as `List.Forall₂` of the arrays' lists), a map on either side moved into it and a value related to itself (`rel_map_left`, `rel_self`, `simp`), the members of a value (`Occ.Mem`, `simp` through the combinators), and the map of an indexed structure at one index as the plain one's (`IOcc.map_flat_sum`, …); the leaves are `Occ.ofIso F`, from the `PolyIso` instances, and the instances of the built-in forms are the combinators by definition (`Occ.ofIso_prod`, …, `simp` lemmas but for the identity's).
- `Model/Occ2.lean`: occurrence structures in two variables `Occ₂`, `G X Y ≃ Lay PX PY X Y` with the layer of `Model/Poly.lean`, for a field with a parameter and the recursion in one argument: combinators, laws, the computation of the map, `AgreeY`, the agreement of its map in `Y` with that of the structure in `Y` alone, and membership in each variable (`MemX`, `MemY`, `simp` through the combinators down to the parts in one variable, whose members are `Occ.Mem`).
- `Model/CCPO.lean`: the order of approximation on a coinductive type with a bottom layer, from a contract and a presentation of its functor as a container (`Contract.Container`): `Approx`, its unfolding and coinduction, the supremum of a chain by `corec` (`csup`), Lean's `Lean.Order.CCPO` (`Contract.ccpo`), the monotonicity of the constructor; the order on a nested argument through its occurrence structure (`Occ.order`) and the monotonicity for it of the maps and constructors of the library's leaves and of the pairs of a product, for `partial_fixpoint` (step 6).
- `Model/IOcc2.lean`: the same over a family, `IOcc₂`, the recursive variable a family over an index, each position in it at its index (the layer of `ILay`), for families and blocks: combinators, among them a plain structure at one index (`ofOcc₂`), laws, the map, `AgreeY` with the indexed structure in `Y` alone read along a map of the indices, and membership, a member in `Y` with its index.

Generators, on `Expr`, in dependency order. `Syntax.lean` holds the command syntax: a declaration is Lean's `inductive` with its keyword swapped (`declModifiers`, `declId`, `optDeclSig`, `where`, Lean's `ctor`, `deriving`), and a `mixed_mutual` block holds commands up to `end`, as `mutual` does.

- `Gen/Decl.lean`: adding declarations from closed `Expr`s, each checked by the kernel before the next: inductive types with the auxiliary constructions of `inductive` (fixed indices promoted to parameters, as `inductive` does), noncomputable definitions, theorems by term or by a tactic on a goal metavariable, simp lemmas and other attributes, and the tag `colean_mutual_rec` of the recursors per type of a `datatype` block; definitions by cases (`mkCasesOnApp`); the generated names relative to a type (`genName`, `coleanNs`) and their protection (`protectedGen`).
- `Gen/Occ.lean`: the occurrence structure of an elaborated argument type, by recursion on its head after `whnfR` (and `id`); instance search at leaves.
- `Gen/Ctx.lean`: the context `Ctx`: parameters (section variables first), indices and constructor arguments as free variables of one `TermElabM` run, the types being defined as local variables at a placeholder universe, argument kinds, names; for a block, its index `Blk.Ix`.
- `Gen/Front.lean`: syntax → `Ctx`, elaborating the declarations as `inductive` does, a single one or the types of a block, or a run of a mixed block with the other runs' types replaced (`Mix`); before that, the modifiers (`DeclStx.elabMods`): the full name of each type, private or not, its universe names, and the modifiers of the type and the constructors; and the names (`checkNames`, `checkCtorNames`).
- `Gen/Functor.lean`: step 1.
- `Gen/Signature.lean`, `Gen/Iso.lean`, `Gen/Model.lean`: step 2 (the signature; the isomorphism and its laws; the type and the contract).
- `Gen/Rel.lean`: `T.F.Rel`, `rel_fmap`, `rel_ofC`, and the lemmas of the lifting: one step at two constructors `T.F.rel_cᵢ_cⱼ` (`simp`, `genRelSteps`, also per type of a block), by cases in general position (`casesRel`), `T.F.Rel.mono`, `T.F.rel_refl` (step 4, generated before the model, see below).
- `Gen/Framework.lean`: step 3.
- `Gen/Extras.lean`: step 2b (`T.Colean.recPos`, `T.rec`), and the instance of an occurrence structure (`isoOf`).
- `Gen/Surface.lean`: step 4 (constructors and their lemmas, `casesOn`, `rec_cᵢ`, `fold_cᵢ`, `T.dtor_eq_cᵢ_iff`, `T.coinduct`; in a block, the types `Tₘ`, and per type the layer `Tₘ.F` with its constructors `Tₘ.F.cᵢ` and the lemmas of its lifting, `Tₘ.dtor`, `Tₘ.ctor`, Lambek's lemma and `Tₘ.dtor_inj`, for `datatype` `Tₘ.fold` and its lemmas and the recursors `Tₘ.rec`, for `codatatype` `Tₘ.corec` and its lemmas, `Tₘ.bisim` and `Tₘ.coinduct`).
- `Gen/Pack.lean`: the display of the packing `Blk.Colean.St` of a block's families at a constructor of `Blk.Ix`, as the family it packs there (a delaborator, for the attribute `colean_pack`), and of the block functor's constructors at a packing as the constructors `Tₘ.F.c` of the layers per type (`layerCtorExt`, `delabLayerCtor`).
- `Gen/Derive.lean`: step 5, separate from the pipeline (see below), in parts under `Gen/Derive/`, each on the ones before: the holes and the structures of the fields (`Holes.lean`), the presentation (`Pres.lean`), the layer `toL`, `ofL` and its laws (`Layer.lean`), the fixpoint and the instances (`Fix.lean`), the `simp` lemmas (`Simp.lean`); `Derive.lean` runs them.
- `Gen/CCPO.lean`: step 6, run by the attribute `with_ccpo` (`CodataCmd.lean`), separate from the pipeline (below).
- `Gen/Command.lean`: the pipeline, before it a dotted name's namespace (`elabInNamespace`), and what comes after it as after `inductive`: the doc comments, `protected` constructors and the info trees (`finishDecls`), then the attributes (`applyDeclAttrs`). `CodataCmd.lean`, `DataCmd.lean`: the commands; `MutualCmd.lean`: `mutual` blocks of them, and `mixed_mutual` blocks, and the refusal of plain `induction` on a type of a `datatype` block (`evalInductionBlockType`).
- `Gen/Mixed.lean`: a `mixed_mutual` block: its runs, the pipeline on each, the closed types of the runs inside, their membership instances, and their interface restated at the closed types.

## The generators

The commands read the user's syntax only to elaborate it. A declaration with a dotted name
`Foo.T`, and a block whose types share a namespace, are elaborated inside that namespace, named
relative to it, as Lean's `expandNamespacedDeclaration` and `expandMutualNamespace` do for
`inductive` (`elabDecl`, `blockNamespace?`, `Gen/Command.lean`): the constructors refer to the
type as `T` or `Foo.T`. `Gen/Front.lean` elaborates a
declaration as Lean's `inductive` does: first its modifiers, as `inductiveSyntaxToView` does
(`Term.expandDeclId` names the type, private for a `private` one, and binds the universe names of
`T.{u}`; `unsafe`, `partial`, `meta` and `deriving` are rejected); then the parameters and the declared sort, then the types being
defined as local variables, against which each constructor is elaborated to one telescope. Every
later decision is taken on the elaborated types, after `whnfR`: an occurrence is an application of
one of these variables to the parameters (and indices), and products, sums, functions, dependent
pairs and leaves are recognised by their head. So spellings that mean the same type are one
(`A × B` and `Prod A B`, an abbreviation, `id A`, `Σ`, `<|`, an arrow-form constructor), and no
generated name can capture a user's. The generated names extend the types' full names, so a
private type makes them private; the names built from components (a block `A_B`, its index, the
open types of a mixed block) are made private with the types (`privateLike`), and the types of a
block are all private or all public. Before the types are declared, the names are checked (no
type twice in a block; no type, block or index of a block declared already; no two types with one
constructor of the block's index; no constructor twice in a type, nor named as a type, with the
messages of `inductive`: `checkNames`; no constructor named as a generated declaration, below:
`checkCtorNames`), and so
is a universe written in a declared sort, against the model's, which is the types' (`checkSorts`,
first in the pipeline; in a mixed block, of the closed types, before the outermost run).

The whole pipeline runs inside one `TermElabM` run, in the continuation of `Gen.withCtx`. Each
step has its own heartbeat budget, as a separate command would, and a failure restores the state
before the error is reported, so a failed command declares nothing, as with `inductive`. The doc
comments of the types and constructors, and the info trees of their names, come after the pipeline,
in the same all-or-nothing run; the attributes written on them come last, outside it: a failing
attribute leaves the declarations, as with `inductive`. The
parameters, the indices and the constructor arguments are free variables of its local context.
A generator builds the types and values of its declarations as `Expr`s over these variables and
closes each declaration once, with `mkForallFVars`/`mkLambdaFVars` and the binder infos of that
declaration (`withBinderInfo`); the occurrences of the types being defined are replaced by what
a step needs (`replaceOcc`, `withArgsAt`). The declarations are added directly (`addDecl`,
`Gen/Decl.lean`): inductive types with the constructions of `inductive`, definitions by `casesOn`,
theorems. Generated constants are used through `constWith`, at the universes a use needs.

Proofs are terms where a theorem of the theory applies. Where building a term by hand would be
painful, the statement is a goal metavariable and a tactic closes it: `MVarId.cases`, `refl`,
`simp only`, `rewrite` from `MetaM`, or a short tactic script run on the goal (`rel_fmap`,
`rel_ofC`, the `rw` steps of step 5). A value by dependent cases is built the same way, as the
instantiated goal. The only syntax left is the command syntax, these tactic scripts, and the
attributes of the eliminators.

A position `b : T.Colean.B idx (Shape.c d)` is eliminated in general position (`casesPos`,
`Gen/Iso.lean`): at variables, solving the equation of the shapes, by the heterogeneous
`noConfusion`, before those of the indices, which then hold by definition. So a constructor's
result index need not be a pattern (`T (n * 2)`, `T (!b)`), as with `inductive`; `MVarId.cases`
would have to invert it. Other eliminations are at index variables: the layers by cases on `F` or
on the shape, `rel_ofC` by cases on `F.Rel` after writing the layers as `toC a`.

## Rules

- Tactic proofs are the laws of the generated inductives: the functor laws (step 1), the isomorphism laws and the lifting laws (steps 2 and 4, with one step of the lifting at two constructors and its monotonicity), and in step 5 the laws of the layer, the rewriting steps of the fixpoint and the cases on the positions of a layer (membership). Everything else instantiates a theorem of `Framework.lean` or `Model/`.
- The framework never mentions a model, a signature or `Raw`; the model never mentions a declaration; the surface never proves anything.
- A nested argument enters the model as a shape with positions; the user-facing `F` keeps its type.
- Some generated proofs need the definitional unfolding of Lean before 4.34 (`withUnfolding`, around those proofs only): a term of the signature is the expected one only after unfolding.

## Names

The generated declarations are named after their type, a block or an open type `T` (`genName`,
`Gen/Decl.lean`; a name equal to the type's own is primed, `B.B'` for a type `B`, as `T.T` would
shadow the type inside its namespace). Those a user calls, or that a user-facing statement
mentions, are `T.s`: the functor `T.F` with its map `T.F.fmap`, the lifting `T.F.Rel` and their
laws and rules, `T.contract`, `T.ctor`, `T.dtor`, the eliminators and their rules, the lemmas of
step 3 and 4, the order of step 6, and the index `Blk.Ix` of a block (the block's family is over
it) and the open type `Tₘ.Open` of a run inside a mixed block (the functor of an outer type
mentions it). The internals are under `T.Colean` (`coleanNs`): the signature `T.Colean.Shape`,
`T.Colean.B`, `T.Colean.Ix` (the packed index of several), `T.Colean.ShapeP`, `T.Colean.idx`,
`T.Colean.sig`; the isomorphism `T.Colean.toC`, `T.Colean.ofC` and its laws `T.Colean.ofC_toC`,
`T.Colean.toC_ofC`, `T.Colean.ofC_map`, `T.Colean.rel_ofC`; the model's recursor
`T.Colean.recPos`, `T.Colean.recAux`, `T.Colean.recPos_ctor`; the cases before the cast
`Tₘ.Colean.casesOnAux`, `Tₘ.Colean.casesOn_ctor`; the packing `Blk.Colean.St` of a block's
families; and everything of step 5 (`T.Colean.Poly.*`, the instances and their `simp` lemmas
`T.Colean.Poly.map_cᵢ`, `T.Colean.Poly.mem_cᵢ` among them). So a constructor may be named as one
of the internals (`B`, `Shape`, `sig`, `toC`, `Poly`), or `map`.

A constructor `T.c` named as a generated declaration of its type, or whose constructor `F.c` of
the functor (`Blk.F.Tₘ_c` in a block when two types have a constructor `c`) is named as a
declaration of the functor (`fmap`, `Rel`, the auxiliary constructions of `inductive`, …), or
`F.Rel.c` as `F.Rel.mono`, would make the kernel refuse a generated declaration; the front end
refuses it first, at the constructor's name, before anything is declared (`checkCtorNames`, also
per run of a mixed block, in `checkMixNames`): "constructor `dtor` clashes with the generated
declaration `Cmd.dtor`; rename the constructor". The names checked are the fixed ones of the type
(`typeGenNames`) and of the functor (`functorGenNames`), the namespace `T.Colean`, and the rules
every constructor has (`T.dtor_cᵢ`, `T.ctor_cᵢ`, `T.casesOn_cᵢ`, `T.dtor_eq_cᵢ_iff`, `T.rec_cᵢ`,
`T.fold_cᵢ`, `T.F.fmap_cᵢ`), in a block the declarations of the layer per type `Tₘ.F` that its
constructor `Tₘ.F.c` may clash with (`layerGenNames`: `fmap`, its laws and rules, `Rel` and its laws,
and the one-step lemmas `Tₘ.F.rel_cᵢ_cⱼ`; the layer is a definition, without the auxiliary
constructions of an inductive type), and those of some constructors, conservatively (`ctorGenNames`):
`T.cᵢ_inj` of every constructor written with arguments or a type, `T.cᵢ_ne_cⱼ` of every two
constructors, `T.F.rel_cᵢ_cⱼ` of every two of a single `codatatype` (on the functor's
constructor), and in a type of a run inside a mixed block its membership lemmas `Tₘ.mem_cᵢ` and
instances `Tₘ.instMembershipO`: "constructor `a_inj` clashes with the generated declaration
`C7.a_inj` (injectivity of `C7.a`); rename the constructor". A rule of a constructor named as a
fixed declaration is refused at that constructor (`T.dtor_inj` for `inj`, `T.F.fmap_id` for
`id`), and so are two declarations generated from constructors with one name (`T.b_ne_ne_b`
from `b` and `ne_b` and from `b_ne` and `b`), unless the generator then gives one another name
or none (the membership lemmas, the one-step lemmas of the lifting, `T.dtor_eq_cᵢ_iff`). Step 5's
names are under `T.Colean`, and cannot clash with a constructor. `with_ccpo` refuses a
constructor named as a declaration of the order the same way (`Gen/CCPO.lean`), before it
declares anything: `T.monotone_cᵢ` for every constructor with a recursive argument.

The binders of the generated declarations that a user may name (`T.corec (S := …)`, `motive`, the
families `S₁ … Sₖ` of a block, the index `m` of a block's family, the `X` of a run inside a mixed
block) are plain, or primed when the declaration has that name already (a parameter `S` makes the
state `S'`, and `S` and `S'` make it `S''`; `plainOr`, `Ctx.userName`), so that they can still be
named.

As `inductive` protects its auxiliary constructions (`recOn`, `noConfusion`, `below`, `brecOn`,
`ctorIdx`, …, which the inductive types generated here, `T.F`, `T.Colean.Shape`, `T.Colean.B`,
`T.F.Rel`, get from it), the commands protect, relative to a type, a block or an open type `T`:
the declarations with generic names `T.ctor`, `T.bisim`, `T.F`, `T.contract`, the
index `Blk.Ix` and the open types `Tₘ.Open` of a mixed block; and everything under `T.Colean`.
After `open T` these are not `ctor`, `bisim`, …, only `T.ctor`, `T.bisim`, and after
`open T.Colean` not `toC`, only `T.Colean.toC`. The types, the constructors, the eliminators
`T.rec`, `T.casesOn` (which Lean leaves unprotected too) and `T.fold`, `T.corec`, `T.dtor`, and
the user-facing lemmas (`T.cᵢ_inj`, `T.cᵢ_ne_cⱼ`, `T.rec_cᵢ`, `T.fold_cᵢ`, `T.casesOn_cᵢ`,
`T.dtor_cᵢ`, `T.ctor_cᵢ`, `T.dtor_corec`, `T.corec_eq`, `T.corec_unique`, `T.fold_eq`,
`T.fold_unique`, `T.ctor_dtor`, `T.dtor_ctor`, `T.ctor_injective`, `T.dtor_injective`,
`T.dtor_inj`, `T.dtor_eq_cᵢ_iff`, `T.coinduct`, the declarations under `T.F`) are not, as Lean
protects neither constructors nor `inj`/`injEq`. The list is `protectedGen` (`Gen/Decl.lean`),
applied once the pipeline has declared everything, step 5 included (`protectGenerated`, at the end
of `pipeline`, and for the closed types of a mixed block at the end of `elabMixed`), so protection
changes no generated statement, and the generators refer to everything by its full name anyway.

## Recursors

The recursor `T.rec` is user-facing, so its type mentions only the user's types and the
user-facing classes. Its induction hypothesis for a nested argument `c` is by membership,
`∀ t, PolyIso.Mem (fun X => G X) t c → motive t`, with the argument's type `G` as a function of
the occurrences and, as its instance, the occurrence structure of the argument read as an
instance (`isoOf`): a leaf is `Occ.ofIso` of its instance, and the instances of the built-in
forms are the combinators by definition. When `G` is `List`, `Option` or `Array` with its
instance (at one index, in a family or a block too), the hypothesis is by their own membership,
`∀ t, t ∈ c → motive t`: the lemmas `PolyIso.mem_list`, `mem_option`, `mem_array` say which
(`stdMemLemmas`), and convert it (`memIffIH`). A composite (`List (Option T)`), a product, a sum,
a function or a user's type keeps `PolyIso.Mem`, which `simp` computes. In a family the hypothesis is by `IPolyIso.Mem` at an
index unless every position is at one index (the index of a position at variables mentions
neither the shape nor the position, or does after cases on it through products, functions and
dependent pairs, `T n × T n`, or on the value through sums reached through products and dependent
pairs, `T n ⊕ T n`: `oneIdx`, which step 5 shares); then the instance is a `PolyIso` at that index
(`flat`), and in the second case the hypothesis at the positions is brought to that index by these
cases (`bridgeIH`, a `Sum.casesOn` term, with the cases on the value in a context of their own so
that the term is the same wherever it is built), and the rule `T.rec_cᵢ` by the same cases
(`bridgeEq`). A sum under a named type constructor or a function (`List (T n ⊕ T n)`) is not
reached by cases on the value: the hypothesis is by `IPolyIso.Mem`, which `simp` computes through
the sum at any value (`IPolyIso.mem_sum`).

The structure of a nested argument, and so the instance of its hypothesis, is the one instance
search finds for the argument's functor: a leaf is a partial application when the occurrences are
in its last argument, and the whole type as a function of them otherwise (`wholeLeaf`): with
occurrences in several arguments, and in an argument other than the last when instance search
finds an instance for the whole (`Vec (List T) n` is `Vec`'s instance at `List`, not the
composite; `E (T × Nat) Nat` is `E`'s at the product). `simp` computes the map at the premise of
such an instance, a leaf or a built-in form (`Occ.ofIso_prod`, …).

`T.Colean.recPos` is the recursor of the model, with the hypotheses at the positions of the
structures. `T.rec` is `T.Colean.recPos` at minor premises that turn these hypotheses into
membership (`PolyIso.memRec`, by `Classical.choose`, with no proof in between since the instance is
the structure; through `List`, `Option` and `Array` then by `PolyIso.mem_list`, …), and its rules
`T.rec_cᵢ` are `T.Colean.recPos_ctor` followed by `PolyIso.memRec_pos` at each nested argument.

## Known boundary violations

- `T.corec`, `T.fold` (universe-polymorphic in the state) and `T.Colean.recPos` come from the model, because `Contract` fixes one universe for `F`. Fix: a universe-polymorphic framework interface, after which the recursor derives from `fold` and `induction`.
- `T.F.Rel` (surface) is generated before the model, because `rel_ofC` and the contract's `bisim` are stated with it. Fix: state `bisim` with the canonical `Rel`, derive the inductive characterisation in step 4 by term-level introduction and elimination lemmas.

## Blocks

A `mutual` block of `codatatype`, or of `datatype`, declarations is one family over the inductive
`Blk.Ix`, which has a constructor per type whose arguments are that type's indices. The front end
declares `Blk.Ix` and gives the family the one index `m : Blk.Ix params`; an occurrence
`Tₘ params idx` is then at `Blk.Ix.Tₘ idx`, and steps 1 to 3 run on the family as on a single
type with one index. Step 4 adds the types `Tₘ params idx := Blk params (.Tₘ idx)`, and works per
type: the constructors and their lemmas are stated with the types `Tₘ`, `Tₘ.casesOn` has only the
constructors of `Tₘ`, and each type gets the rest of the interface of a single type, with a family
per type of the block where the block-level declarations have one over `Blk.Ix`, as Lean's mutual
recursors have a motive per type, and nothing about `Blk.Ix`. The block-level declarations stay,
and so does the block's contract, the only one: the per-type ones are derived from them, by term
assembly.
For `datatype`, `Tₘ.rec` has a motive per type, as Lean's mutual recursors: it is `Blk.rec` at the
motive `fun i x => Blk.Ix.casesOn i motive_1 … x`, whose minor premises are the per-type ones by
unfolding, and its rules `Tₘ.rec_cᵢ` are the block-level rules `Blk.rec_cᵢ` by unfolding. A
hypothesis by membership at an index of the block (`IPolyIso.Mem`) is one per type of the
argument in `Tₘ.rec`, each at its type's motive, and `Blk.rec`'s is given to each at its
constructor of `Blk.Ix`.

The eliminators of the types: `T.casesOn` is the `cases` eliminator, and for `codatatype` the
`induction` one too, since `codatatype` has no induction and otherwise `induction` would unfold the
type to its encoding (a subtype of `Raw`). For a single `datatype`, `T.rec` is the `induction`
eliminator (`Gen/Extras.lean`), and in a `datatype` block `Blk.rec` is. The recursors per type
`Tₘ.rec` have a motive per type, which Lean's `induction` cannot take as its eliminator (the
other motives would be left as metavariables), so they carry the tag `colean_mutual_rec`, and
plain `induction t` on `t : Tₘ` is refused with a hint to `induction t using Tₘ.rec
(motive_2 := …)`, as Lean refuses a mutual inductive (`MutualCmd.lean`). The block family of a
`codatatype` block has no case analysis.

`Blk.Colean.St S₁ … Sₖ` packs a family per type into one on `Blk.Ix` by cases (`Blk.Ix.casesOn`);
the layer of a type, `Tₘ.F params S₁ … Sₖ idx`, is `Blk.F` at it and at `.Tₘ idx`, and its map
`Tₘ.F.fmap f₁ … fₖ` and, for `codatatype`, its lifting `Tₘ.F.Rel R₁ … Rₖ` are the block's at the
functions and relations packed by cases, all reducible, so that patterns and dot notation find the
block functor's constructors. The block functor names a constructor that two types share by its type
(`Blk.F.Tₘ_c`), so each type's layer has its constructors under their own names: `Tₘ.F.c`, the
block functor's constructor at the packed family, with the arguments as written and the
occurrences at `S₁ … Sₖ`, reducible and `@[match_pattern]`, so that `.c` finds it from the
expected type `Tₘ.F …` (before the unfolding to `Blk.F`), and a pattern `.c x` on `t.dtor` unfolds
to the block functor's constructor; their laws `Tₘ.F.fmap_id`, `Tₘ.F.fmap_comp`, `Tₘ.F.rel_fmap` are the
block's at the packed functions, equal to the packed identities and composites by cases.
`Tₘ.corec c₁ … cₖ` is `Blk.corec` at `Blk.Colean.St S₁ … Sₖ` and the step made of the `cⱼ` by cases,
and `Tₘ.fold a₁ … aₖ` is `Blk.fold` there at the algebra made of the `aⱼ`. The layer at the types,
`Tₘ.F params (T₁ params) …`, is `Blk.F` at `Blk.Colean.St (T₁ params) …`, which is `Blk params` at
every constructor of `Blk.Ix` by definition but not at a variable index, so the two are not one
type: `Tₘ.dtor` is `Blk.dtor` followed by `Blk.F.fmap ι`, and `Tₘ.ctor` is `Blk.ctor` after
`Blk.F.fmap ρ`, `ι` and `ρ` the identities between them by cases. The rules pass between them by
cases on the index: `ρ ∘ ι` and `ι ∘ ρ` are the identity by `funext` of `rfl` by cases, so the maps
by them cancel (`F.fmap_comp`, `F.fmap_id`), which gives Lambek's lemma per type from the block's;
`Tₘ.dtor_cᵢ` is `Blk.dtor_ctor` under the map, with `IOcc.map_heq_self` at a nested argument
(`Model/Occ.lean`, from `subst` on the equation of the two families), and `Tₘ.ctor_cᵢ` follows from
it and `Tₘ.ctor_dtor`; `Tₘ.dtor_corec` is `Blk.dtor_corec` under the map, `F.fmap_comp`, and the
composite equal to the packed corecursors by cases, and dually `Tₘ.fold_ctor` is `Blk.fold_ctor` at
`Blk.F.fmap ρ y`; `Tₘ.corec_eq`, `Tₘ.fold_eq` and `Tₘ.fold_cᵢ` follow from these as for a single
type; `Tₘ.corec_unique` and `Tₘ.fold_unique` are `Blk.corec_unique` and `Blk.fold_unique` at the
morphisms packed by cases, the hypothesis at each type from the per-type one under the map by `ρ`
(`codatatype`) or at `Blk.F.fmap ι y` (`datatype`); `Tₘ.bisim R₁ … Rₖ` is `Blk.bisim` at the packed
relation, its hypothesis at each type from the per-type one by `Codata.rel_of_map_heq`
(`Framework.lean`). The lemmas of the lifting per type are those of a single type: one step at two
constructors `Tₘ.F.rel_cᵢ_cⱼ` (`simp`), stated with the relations per type (`R₂ f g` at a forest; at
a nested argument the block's structure at the packed relations, which `simp` takes back to a
type's, `IOcc.rel_ofOcc`), proved as for a single type, `Tₘ.F.Rel.mono`, the block's at the packed
relations and hypotheses, and `Tₘ.F.rel_refl`, `Tₘ.F.rel_fmap` at the identities; `Tₘ.coinduct` is
`Tₘ.bisim` at the relations up to equality, and `Tₘ.dtor_injective` is `Tₘ.ctor_dtor` as a left
inverse. The block-level declarations, and the rules of the block's `dtor`, `ctor` and `fold`,
`Blk.dtor_cᵢ`, `Blk.ctor_cᵢ`, `Blk.fold_cᵢ`, stay; step 5 uses these. A run inside a `mixed_mutual`
block that is a block gets the same as `Tₘ.Open.F`, `Tₘ.Open.corec`, `Tₘ.Open.fold`, …, restated at
the closed types as `Tₘ.F`, `Tₘ.corec`, `Tₘ.fold`, … (next section). In the infoview,
`Blk.Colean.St S₁ … Sₖ` at a constructor `.Tⱼ idx` is shown as `Sⱼ idx` (`Gen/Pack.lean`), so that
the fields of a match on `t.dtor` show as trees and forests, and the block functor's constructor at
a packing as the layer's, `Forest.F.cons t f` for `Tree_Forest.F.cons t f`; the statements keep the
block functor's. The `cases` tactic on a layer names its cases by the block functor's constructors
(`| Even_succ o`).

A block mixing `datatype` and `codatatype` is a nested fixpoint, whose order is a choice; `mutual`
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
attributes (`simp`, the eliminators, `elab_as_elim`, `colean_mutual_rec`); an inductive type
(`T.F`) becomes a reducible definition and its constructors reducible definitions usable in
patterns, as do the constructors `Tₘ.Open.F.c` of the layers per type of a block (`Tₘ.F.c`), the
constructors `Tₘ.c` reducible too, so that the lemmas of the open types, those of
step 5 among them, apply to the closed ones. Last, the `simp` lemmas `Tₘ.mem_c` of the membership
instances, the `simp` normal form of the membership through the open types (`memLemmas`). The
names the user wrote are the closed declarations in the info tree.

The functor of a run at its state keeps the open types of the runs inside at that state
(`Tree.F α X ∋ node (a : α) (children : Forest.Open α X)`): there is no closed form for it.

## Nesting and declared types

Defining a type and presenting it as a polynomial functor are separate steps. Step 5,
`deriveInstances` (`Gen/Derive.lean`), runs after the pipeline has finished, in the same run: it
reads the declaration's context and the type's public declarations, and nothing in the pipeline
depends on it. On failure it restores the state and logs a warning, so it can't affect the type;
the warning gives a short reason, a limit of the step as it is and an error of the generator by
what it failed to generate (`stepPhase`), the error itself under
`set_option codata.deriveDetails true`. When no parameter may vary because of a field, an info
says so and why.

It generates one instance per type, `PolyIso (fun X => T (H₁ X) … (Hₙ X))` with premises on the
`Hᵢ`, over the parameters that may vary, and the eta-reduced form `T A₁ … Aₙ₋₁`, with the `PolyMap`
instance from `PolyMap Hᵢ H'ᵢ` premises, as the instances of the built-in forms (the eta form across
universes when the universe of the last parameter is its own). When a field fixes the universe of
the occurrences (`NDet (T α)` with `NDet : Type → Type`), the layer's `Y` is at it, and so are the
states of the fixpoint: the premises' shapes are in `Type`, and for `codatatype` their positions too
and `X` at that universe (`stepLevels`); for `datatype` above `Type`, the trees of shapes must reach
it (`checkStateLevel`, a limit otherwise). Only the layer `T.Colean.Poly.toL`/`ofL` and its laws are
per declaration; the fixpoint is `Model/Poly.lean`, one proof for `datatype` and `codatatype`, from
the contract. The structure of a field in the parameters is that of `Gen/Occ.lean`, with each
premise's structure at its parameter; a field may mention several, and when it has no structure in
all of them the fewest are kept constant, the first ones first, so that the others have one
(`refineHoles`).

The layer is presented constructor by constructor of the presentation (`VCtor`): those of `T`,
with a nested argument split through its products and sums when it mentions a parameter that
varies outside the occurrences (`p : α × T α`, `f : T α ⊕ α`), or with indices has its positions at
an index only after cases on them (`T n × T (n + 1)`, `A × B` in a block). Its parts are fields at
parameter positions, recursive arguments or data, as arguments of their own; through a sum the
constructor is one constructor of the presentation per side, at most `maxSplit` per constructor of
`T` (beyond, the arguments through sums are not split and have a structure in two variables, or
their indexed structure); the internal names of these constructors and parts take a suffix when
taken. `toL` takes the parts by projections
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
`imixOcc`), its occurrences at the presentation's indices, so that the positions of the layer carry
them by construction; in a block, a nested argument whose positions are at a type of the block only
after cases on them inside a named type constructor (`p : List (RA α × Nat)`) is presented so too,
with no part in the parameters. When the positions are at one index after cases (`oneIdx`, the
analysis of the recursor's hypotheses too), the structure is the plain one at that index
(`IOcc₂.ofOcc₂`), whose map and members are those of the plain one by definition, and the rules are
stated as without indices, at the type of the members. In `ofL_map` the map of `T.F`, by the
family's indexed structure over its own index, is its map by `IOcc₂.AgreeY`, along `ι`, the identity
or `Blk.Colean.Poly.ixIn`; for a plain structure at one index, from the plain agreement and the map
of the indexed structure at that index, the plain one's by definition and across a sum by cases on
the value (`IOcc₂.AgreeY.ofOcc₂`, `IOcc.map_flat_sum`, …).

A family gets the instances at every index, `PolyIso (fun X => T (H X) idx)` with `idx` arguments of
the instance; its presentation is a family over the packed index, with the index of each position
(`T.Colean.Poly.idx`, `T.Colean.Poly.sig`), and the layer at an index `i` is `ILay`. The types of a
block get theirs at their index of the block: the presentation is per block (`Blk.Colean.Poly.*`),
over `Blk.Colean.Poly.Ix`, which is `Blk.Ix` without the parameters that vary (`Blk.Ix` takes them
all, so it cannot index trees of shapes that do not depend on them), read in the block's index along
`Blk.Colean.Poly.ixIn`; the instances are per type (`Tₘ.Colean.Poly.instPolyIso`), with the eta
forms for a type without indices. The theory takes the contract along this map (`ico_bisim`,
`iin_ind`), and `corec` and `fold` on states over the presentation's index through `Along` and
`Over`.

Scope: in a block, a nested argument with positions at several types of the block inside a named
type constructor (`List (A × B)`) gets its instances but not its `simp` lemmas, which state the
members by the type of each; the step warns. A parameter in the same field as the type is
constant there when the field has no structure in two variables: in another argument of a leaf
than the type (`List (E α (T α))`), or under a functor on families. A parameter that is a family
(`IPolyIso`) is not supported: `Model/Poly.lean` has the fixpoint for a parameter that is a
type.

With the instances come, per constructor `c` of each type, two `simp` lemmas at the premises
(`genPolySimp`), so that `simp` computes through the instances in the rules of other types:

- `T.Colean.Poly.map_c`: `(Occ.ofIso fun X => T (H X) idx).map (Occ.ofIso fun X => T (H' X) idx) f
  (T.c args) = T.c args'`, data unchanged, a field at a parameter position mapped by its
  structure in the premises (`(Occ.ofIso H).map (Occ.ofIso H') f a`, `f a` by `simp` at the
  identity), a recursive argument by this map, a nested one by the map of its structure. It is
  stated on the leaf `Occ.ofIso`, as the other types' rules (`fold_c`, `F.fmap_c`, `dtor_corec`)
  mention the map: a rule on `PolyMap.map`, whose functor is implicit, would make `simp` solve
  `?H ?X =?= T` first and not apply at the identity premise. `Occ.map_ofIso` relates the two.
  An argument with a structure in two variables is mapped by `Occ₂.map`, by `f` in the parameter
  and by this map in the occurrences; at several indices of a family by `IOcc₂.map`, at each
  index by the map of the leaf there. The proof is `PolyFix.map_eq_of_d` at `ctor ∘ ofL` after
  `dtor_c`; the right-hand side is then the result by definition.
- `T.Colean.Poly.mem_c`: `PolyIso.Mem (fun X => T (H X) idx) x (T.c args) ↔ …`, a disjunct per field
  at a parameter position and per recursive argument (through a nested one, `∃ t, Mem G t c ∧
  Mem … x t`), `False` without any; an argument with a structure in two variables has two, by its
  structure in the parameter alone (the occurrences constant) and in the occurrences alone, whose
  positions are those of the structure in two variables by definition, or across a sum, where they
  are not, by `Occ₂.MemX` and `∃ t, Occ₂.MemY o t c ∧ …`, which `simp` computes through the
  combinators (a member with a property first, `simp ↓`, then the membership); at several indices
  of a family by `IOcc₂.MemX` and `IOcc₂.MemY`, a member with its index. It holds for `codatatype`
  as well: a slot is a finite path. The proof is `PolyFix.exists_val_iff` after `dtor_c`, then cases
  on the positions of the layer.

Both are stated on the constructors for `codatatype` too (a value is the constructor of its `dtor`,
and `corec_eq` writes a corecursive one so). The functors of the left-hand sides are not indexed,
since the leaves of other rules are often eta-reduced (`Occ.ofIso Forest`). A failure of the
lemmas is a warning that rolls back only them.

## Orders for `partial_fixpoint`

`attribute [with_ccpo] T` (or `@[with_ccpo] codatatype T …`, applied once the declaration is
complete, as `inductive` applies its attributes) gives a `codatatype` the order with which Lean's
`partial_fixpoint` defines corecursive functions into it (`Gen/CCPO.lean`). Like step 5 it runs on
a declared type, reads only the environment, and declares nothing in the pipeline: off by default,
nothing a declaration generates changes. A failure is an error of the attribute, which restores the
state.

The order is *approximation*, with a constructor without arguments as the bottom
(`with_ccpo (bot := c)`, or the first such constructor): `x ⊑ y` when `x` is the bottom, or `dtor x`
and `dtor y` are related by the lifting of the order, the greatest such relation
(`Contract.Approx`). It is defined from the contract and the bottom layer alone. That it is a
partial order and that chains have suprema needs the positions of a layer (the lifting by `map`
alone need not preserve intersections and composites of relations): the theory takes the
presentation of `F` as `σ.Obj` that every generated type has (`T.Colean.toC`, `T.Colean.ofC`,
`Contract.Container`), and the emptiness of the bottom's positions, by `cases` on `T.Colean.B`.
Antisymmetry is `bisim`; the supremum of a chain is `corec` on sets of elements, the bottom layer if
there is no other element, otherwise the shape of the others with the sets of their children at its
positions (`Contract.csup`). The instance is `Contract.ccpo T.contract e C hbot idx`, at every index
for a family, whose bottom is then a constructor at every index (`| stop {n} : T n`). The pieces are
elaborated from short terms on the generated constants, so that one generator covers the contract
over `Unit` of a plain type and a family's.

`partial_fixpoint` proves a definition monotone with the lemmas tagged
`@[partial_fixpoint_monotone]`, by the head of the body, and splits `match`es (on `t.dtor`). A
constructor gets `T.monotone_c`: its recursive arguments, plain, under a function (Lean's order on
functions) or nested with a plain structure, `List T`, `T × T` (the order through the structure,
`Occ.order`, which is `T.F.Rel`'s), are monotone functions, the others fixed; the proof is the
constructor of `T.F.Rel`, its premises the hypotheses, or reflexivity (`Occ.rel_refl`,
`IOcc.rel_refl`) for a fixed nested argument. Through a leaf the maps and the constructors are
monotone (`Occ.monotone_list_map`, `monotone_option_map`, `monotone_array_map`,
`monotone_list_cons`, `monotone_option_some`), and through a product the pairs, with the type's
own order at a component that is the type, where `partial_fixpoint` proves a recursive call
monotone (`monotone_prod_mk_hole`, `_hole_left`, `_hole_right`, then `monotone_prod_mk`, in this
order since the first lemma that applies is taken). The user's own functions (`bind` of
interaction trees) are proved monotone by `T.approx_coind`, coinduction up to the order.

Not supported: the types of `mutual` and `mixed_mutual` blocks (the outer `codatatype` of a mixed
block is a single type and is supported), several indices, and recursion through a composite
(`some [f n]` in `Option (List T)`) or a function into a list, whose orders through the structure
are not the leaves' (`Sketch/CCPOTour.lean`, Part II).

