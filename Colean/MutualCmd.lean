import Colean.DataCmd
import Colean.Gen.Mixed

/-!
# Mutual blocks

```
mutual
codatatype Tree (α : Type u)
  | node (a : α) (children : Forest α)
codatatype Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end
```

A `mutual … end` block whose declarations are all `codatatype`, or all `datatype`, with the same
parameters (binder annotations included, as in `inductive`), is one family: the block
`Tree_Forest` (the names joined by `_`, in their common namespace: `Foo.A_B` for `Foo.A` and
`Foo.B`, `Qa_X_Qb_X` for `Qa.X` and `Qb.X`) is declared as a
single family over the inductive `Tree_Forest.Ix`, which has a constructor per type, `Tree` and
`Forest` (`Qa_X` and `Qb_X`: the type's name in the block, its components joined by `_`), whose
arguments are the indices of that type, and every declaration of the single
type case is generated for the block (`Tree_Forest.F`, `Tree_Forest.corec`, `Tree_Forest.bisim`,
`Tree_Forest.rec`, …). This is how Lean itself elaborates mutual fixpoints, and the generic
theory needs nothing new. The types need not agree on their indices, since each has its own
constructor of `Ix`; where their universe is written, it must be the same, the block's
(`checkSorts`, `Gen/Command.lean`). The names the block declares, its types', its own and its
`Ix`, must be free, no type may occur twice, and no two types may give `Ix` one constructor
(`checkNames`, `Gen/Front.lean`): all are checked before the types are declared. Then, per type:
`Tree α := Tree_Forest α .Tree`, and `Even n := Even_Odd (.Even n)` with an index, its
constructors `Tree.node` with their lemmas under `Tree`, `Tree.casesOn` with only the
constructors of `Tree`, registered as the `cases` eliminator (for `codatatype` the `induction` one
too), and the rest of the interface of a single type, in the shape of Lean's mutual recursors (a
motive per type): a family, a step or an algebra, a morphism and a relation per type where a
single type has one, and nothing about `Ix`. The block-level declarations stay
(`Tree_Forest.ctor`, `Tree_Forest.corec`, `Tree_Forest.fold`, `Tree_Forest.bisim`, …), with one
family over `Ix` (`S : Tree_Forest.Ix α → Type _`, `c : ∀ i, S i → Tree_Forest.F α S i`); so
does the contract, `Tree_Forest.contract`, the block's only, from which everything follows.

```
Tree.dtor : Tree α → Tree.F α (Tree α) (Forest α)
Tree.ctor : Tree.F α (Tree α) (Forest α) → Tree α
Tree.dtor_ctor, Tree.ctor_dtor, Tree.ctor_injective, Tree.dtor_node, Tree.ctor_node
-- `codatatype`
Tree.corec : (S₁ → Tree.F α S₁ S₂) → (S₂ → Forest.F α S₁ S₂) → S₁ → Tree α
Tree.dtor_corec :
  (Tree.corec c₁ c₂ s).dtor = Tree.F.map (Tree.corec c₁ c₂) (Forest.corec c₁ c₂) (c₁ s)
Tree.corec_eq :
  Tree.corec c₁ c₂ s = Tree.ctor (Tree.F.map (Tree.corec c₁ c₂) (Forest.corec c₁ c₂) (c₁ s))
Tree.corec_unique (h₁ : S₁ → Tree α) (h₂ : S₂ → Forest α)
  (hh₁ : ∀ s, (h₁ s).dtor = Tree.F.map h₁ h₂ (c₁ s))
  (hh₂ : ∀ s, (h₂ s).dtor = Forest.F.map h₁ h₂ (c₂ s)) : h₁ s = Tree.corec c₁ c₂ s
Tree.bisim (R₁ : Tree α → Tree α → Prop) (R₂ : Forest α → Forest α → Prop)
  (H₁ : ∀ x y, R₁ x y → Tree.F.Rel R₁ R₂ x.dtor y.dtor)
  (H₂ : ∀ x y, R₂ x y → Forest.F.Rel R₁ R₂ x.dtor y.dtor) : R₁ x y → x = y
-- `datatype`
Tree.fold : (Tree.F α S₁ S₂ → S₁) → (Forest.F α S₁ S₂ → S₂) → Tree α → S₁
Tree.fold_node : Tree.fold a₁ a₂ (Tree.node a cs) = a₁ (.node a (Forest.fold a₁ a₂ cs))
Tree.fold_ctor, Tree.fold_eq, Tree.fold_unique
```

A family per type, all in one universe, is a family over the type's indices as declared
(`S₁ : Nat → Type _` for `Even : Nat → Type`), and so are a step `c₁ : ∀ n, S₁ n → Even.F S₁ S₂ n`
or an algebra `a₁ : ∀ n, Even.F S₁ S₂ n → S₁ n`, a morphism `h₁ : ∀ n, S₁ n → Even n` and a
relation `R₁ : ∀ n, Even n → Even n → Prop`. The layer of a type at a family per type,
`Tree.F α S₁ S₂`, is the block's functor at the families packed into one on `Ix` by cases
(`Tree_Forest.St S₁ S₂`), a reducible definition, so patterns and dot notation find the block
functor's constructors through it (`.node a s`, and `exact .cons _ _ _ _ h₁ h₂` for
`Forest.F.Rel`); so are its map `Tree.F.map f₁ f₂`, with the `simp` rules `Tree.F.map_node`, …
and the laws `Tree.F.map_id`, `Tree.F.map_comp`, and, for `codatatype`, its lifting
`Tree.F.Rel R₁ R₂`, with `Tree.F.rel_map`. The destructor per type, which dot notation `t.dtor`
finds, is the block's `dtor` followed by the map by the identity from `Tree_Forest α` to
`Tree_Forest.St (Tree α) (Forest α)`, and the constructor per type the block's `ctor` after the
map back: the two families are one at every constructor of `Ix` by definition, not at a variable
index. The rules of the block's `dtor`, `ctor` and `fold` are `Tree_Forest.dtor_node`,
`Tree_Forest.ctor_node`, `Tree_Forest.fold_node`, …, with the block-level names of shared
constructors (`Even_Odd.dtor_Even_succ`). In `match t.dtor with | .node a cs => …` the field
`cs` is `Tree_Forest.St (Tree α) (Forest α) .Forest`, a forest by definition and shown as
`Forest α` (`Gen/Pack.lean`), and `cs.dtor` is `Forest.dtor cs`. A nested argument is mapped by
the functions per type packed on `Ix` (`Rose.fold_node`, `Rose.F.map_node` for
`cs : List (Rose α)`), which `simp` takes to the function of the type at the positions
(`IOcc.map_ofOcc`).

Induction, for a `datatype` block (say `Rose` and `Forest`, the same declarations as `datatype`), is
either over the block, by `induction x` for `x : Rose_Forest α m` with one motive over `Ix` (the
block-level rules are `Rose_Forest.rec_cons`, …), or per type, with the recursors `Rose.rec`,
`Forest.rec` in the shape of Lean's mutual inductives: a motive per type (`motive_1`,
`motive_2` in block order), the minor premises of every constructor of the block, and the
type's own indices. They are `Rose_Forest.rec` at the motive made of these by cases on `Ix`. As
with Lean's mutual inductives, the other motives are given by name,
`induction t using Rose.rec (motive_2 := …)`, and plain `induction t` is refused with this
hint, as Lean refuses a mutual inductive, instead of unfolding the type to its encoding
(`evalInductionBlockType`). Their rules are `Rose.rec_node`, `Forest.rec_cons`, …, stated with
the recursors per type. A nested argument whose positions are at one type only after cases on
them (`p : Own × Nat`) has its hypothesis by `PolyIso.Mem` at that type's motive; one with
positions at several types of the block (`p : Rose α × Forest α`), one hypothesis by
`IPolyIso.Mem` per type.

The types get `PolyIso` and `PolyMap` instances at their index of the block, when the parameters
allow it (step 5, `Gen/Derive.lean`): the presentation is per block, `Tree_Forest.Poly.*`, over
`Tree_Forest.Poly.Ix`, the block's index without the parameters that vary, and the instances are
per type, `Tree.Poly.instPolyIso`. A nested argument with positions at one type only after cases
on them is split through its products and sums (`p : Own α × Nat`), or inside a named type
constructor has a structure in two variables (`p : List (Own α × Nat)`); at several types inside
a named type constructor (`List (Rose α × Forest α)`) it gets its instances but not its `simp`
lemmas, with a warning.

Constructor names shared by several types of the block are qualified in the block-level
inductives (`Even_succ`, `Odd_succ` in `Even_Odd.F`), and so are the minor premises of the
recursors and the alternatives of `induction`; the per-type declarations keep the plain names.

The block is analysed and generated by `Gen/` like a single declaration (`Gen/Front.lean`,
`Gen/Command.lean`); the per-type declarations are `Gen/Surface.lean`'s. A mixed block is
`Gen/Mixed.lean`'s, which runs the same pipeline on each run.

A `mutual` block mixing `datatype` and `codatatype` is rejected: such a block is a nested fixpoint,
and the nesting order is a choice, which `mixed_mutual` states.

As with `inductive`, a block whose types share a namespace (`Foo.A`, `Foo.B`) is elaborated
inside it, so its constructors refer to the types as `A` and `B` too; the types of a block
without a common namespace (`Qa.X`, `Qb.X`) are referred to by their full names.

Each declaration of a block has its own modifiers, as in `inductive` (`Syntax.lean`): doc comments,
attributes and `protected` per type and constructor. The types of a block, `mutual` or
`mixed_mutual`, have the same universe names, and are all `private` or all public, the block's own
declarations (its name, its index, its open types) being private with them; Lean allows mixing,
these commands do not.

## Mixed blocks: `mixed_mutual`

```
mixed_mutual
codatatype Tree (α : Type u)
  | node (a : α) (children : Forest α)
datatype Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end
```

A block with both kinds is a nested fixpoint, and a cyclic system has several nested solutions
(`Tree` outside `Forest` is the finitely branching infinite trees, `Forest` outside `Tree` the
finite trees), so the block says the order: *the textual order is the nesting order, the first
declaration outermost*. All declarations share their parameters, names included, and their
universe where it is written, as in `mutual`, which must be that of the closed types; the section
variables any of them uses are parameters of all. The names the block declares, the internal ones
below included, must be free, and no type may occur twice. A *run* is a maximal sequence of
adjacent declarations of the same kind; it is declared as one type, or as one `mutual` block (a
family over its index `Blk.Ix`). The runs `R₁ ⊃ R₂ ⊃ … ⊃ Rₖ` are declared from the innermost out:

* a run inside the first is declared *open*, under internal names: `Forest.Open` for a single
  type, with its whole interface under `Forest.Open.*`, and for a block `Rose.Open`,
  `Forest.Open` for its types and `Rose_Forest.Open` for the block, over the index
  `Rose_Forest.Ix`. It takes one extra parameter per outer run it needs, after the declared
  ones: per run outside whose types it mentions, or that a run inside it which it mentions needs
  (it passes the parameter on). The parameter `X` is a type at a universe of its own (`u_Tree`)
  for a run of one type without indices, and a family over the run's packed index, or over its
  `Blk.Ix`, otherwise; every occurrence of a type of that run becomes `X` (at the index). An
  occurrence of a type of a run further inside becomes that run's open type at the families of
  the runs it needs, this run's own types among them: a nested occurrence through the open type,
  whose `PolyIso` instance in its extra parameters step 5 generates (`Gen/Derive.lean`); a
  failure there is an error, when a run outside nests through it;
* the first run is declared as written, `Tree` nesting through `Forest.Open α (Tree α)`. As soon
  as its types exist, the closed types of the runs inside are declared, from the outermost of
  them in, as abbreviations `Forest α := Forest.Open α (Tree α)` (and `Rose α`, `Rose_Forest α`
  for a block) at the closed families of the runs each needs, and with them the instances
  `Membership (Tree α) (Forest α)` for each run that nests through them; the rest of the first
  run is stated with the closed types (`Tree.node : α → Forest α → Tree α`) and its recursor's
  hypotheses by membership in them (`∀ t, t ∈ cs → motive t`);
* then the interface of every run inside is restated at the closed types, under the names the
  user wrote: `Forest.F` (the open functor at the outer types; for a block, the layer per type),
  the constructors, `casesOn` as the `cases` eliminator, `fold`, `rec` (the `induction`
  eliminator for a single type, the recursors per type for a block), `dtor`, `ctor`, `corec`,
  `dtor_corec`, `bisim` (per type for a block, as above), the injectivity,
  disjointness and computation rules, `contract`, …, each the open declaration at the closed
  families (`Gen/Mixed.lean`), with its attributes; and the `simp` lemmas `Forest.mem_cons`,
  computing membership on the constructors.

So the user sees the types as declared, with the interface of standalone declarations:
`Forest.cons : Tree α → Forest α → Forest α`, `Forest.rec`, `Tree.corec`, `Tree.bisim`. What
remains open is the functor of an outer run at its state, which has the inner types at that
state: `Tree.F.node : α → Forest.Open α X → Tree.F α X`, so the corecursion of trees builds
open forests of states, with the constructors of `Forest.Open`, which dot notation finds
(`.node a (.cons () .nil)`), and the rules of the outer run that map through the inner ones are
stated with the open types' instances (`Occ.ofIso (Forest.Open α)`), through which `simp`
computes on the closed constructors, abbreviations of the open ones. The closed types are
abbreviations so that `simp` and `rw` see a term of the open type at the outer types as one of
the closed type; `cases` and `induction` find their eliminators by the head of the target's type,
so they take the closed ones (`Forest.casesOn`).

Scope: the instances of an open run in its extra parameters are those of step 5, so a run inside
another needs extra parameters that are types, used in fields with an occurrence structure in
them, with the block's parameters (`c : C.Open α X`, a run passing an outer type on to a run
further inside) or with the run's own type, through products and sums (`p : Tree α × Forest α`)
or inside a named type constructor where the field has a structure in both
(`List (Tree α × Forest α)`, `List (Tree α ⊕ Forest α)`). An outer run with indices, or a block,
makes the parameter a family (`IPolyIso` instances, not generated), and an outer type with the
run's own type in a field without a structure in both (`Two (Tree α) (Forest α)`) cannot vary:
these blocks stop with the error of step 5 for the inner run. A `mixed_mutual` block of one kind
is a `mutual` block, with a warning.
-/

open Lean Meta Elab Command Tactic

namespace Codata

@[command_elab Lean.Parser.Command.mutual] def elabMutualCodata : CommandElab := fun stx => do
  let cmds := stx[1].getArgs
  let decls := cmds.filterMap Gen.DeclStx.read?
  if decls.isEmpty then throwUnsupportedSyntax
  unless decls.size == cmds.size do
    throwError "a mutual block must consist of `codatatype` and `datatype` declarations only"
  if let some (ns, cmds) := Gen.blockNamespace? cmds then
    return ← Gen.elabInNamespace stx[0] ns (stx.setArg 1 (mkNullNode cmds))
  if decls.size == 1 then
    elabCommand cmds[0]!
    return
  unless decls.all (·.co == decls[0]!.co) do
    throwError "a `mutual` block may not mix `datatype` and `codatatype` declarations: the block \
      is a nested fixpoint and the nesting order is a choice; use `mixed_mutual … end`, which \
      nests the declarations in the order written, the first outermost"
  Gen.elabDecls decls stx

/-- The commands of a `mixed_mutual` block, in order. -/
private partial def commandsOf (stx : Syntax) : Array Syntax :=
  if stx.isOfKind nullKind then stx.getArgs.flatMap commandsOf else #[stx]

/-- `induction t` without `using`, for `t` in a type `T` of a `datatype` block: an error, as for a
mutual inductive, with the recursor per type `T.rec` and its other motives given by name as the
hint. Without it, `induction` would unfold `T` to its encoding. Anything else goes on to Lean's
`induction`. -/
@[tactic Lean.Parser.Tactic.induction, no_fallback]
def evalInductionBlockType : Tactic := fun stx => do
  unless stx[2].isNone do throwUnsupportedSyntax
  let some target := stx[1].getSepArgs[0]? | throwUnsupportedSyntax
  unless stx[1].getSepArgs.size == 1 do throwUnsupportedSyntax
  let some (T, others) ← (withMainContext do
      let t ← elabTerm target[1] none
      if (← getCustomEliminator? #[t] true).isSome then return none
      let .const T _ := (← instantiateMVars (← inferType t)).headBeta.getAppFn | return none
      let some ci := (← getEnv).find? (T ++ `rec) | return none
      unless Gen.mutualRecAttr.hasTag (← getEnv) ci.name do return none
      forallTelescope ci.type fun xs body => do
        let own := body.getAppFn
        let others ← xs.filterMapM fun x => do
          let n ← x.fvarId!.getUserName
          return if x != own && "motive_".isPrefixOf n.toString then some n else none
        return some (T, others)) <|> throwUnsupportedSyntax
    | throwUnsupportedSyntax
  let args := ", ".intercalate (others.map (s!"{·} := …")).toList
  throwError m!"The `induction` tactic does not support the type `{.ofConstName T}` because it \
    is a type of a mutual `datatype` block" ++ .hint' m!"Use its recursor, with the other motives \
    given by name: `induction {target} using {.ofConstName (T ++ `rec)} ({args})`, or the \
    `cases` tactic"

@[command_elab mixedMutualCmd] def elabMixedMutual : CommandElab := fun stx => do
  let cmds := commandsOf stx[1]
  let decls := cmds.filterMap Gen.DeclStx.read?
  if decls.isEmpty then throwUnsupportedSyntax
  unless decls.size == cmds.size do
    throwError "a `mixed_mutual` block must consist of `codatatype` and `datatype` declarations \
      only"
  if let some (ns, cmds) := Gen.blockNamespace? cmds then
    return ← Gen.elabInNamespace stx[0] ns (stx.setArg 1 (mkNullNode cmds))
  if decls.all (·.co == decls[0]!.co) then
    logWarningAt stx[0] m!"all declarations of this `mixed_mutual` block are \
      `{if decls[0]!.co then "codatatype" else "datatype"}`; use `mutual`"
    if decls.size == 1 then elabCommand cmds[0]!
    else Gen.elabDecls decls stx
    return
  Gen.elabMixed decls stx

end Codata
