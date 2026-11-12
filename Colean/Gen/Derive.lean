import Colean.Gen.Surface
import Colean.Model.Poly
import Colean.Model.IOcc2

/-!
# Generators on `Expr`, step 5: deriving `PolyIso` for a declared type

*Spec.* Input: a type that is already completely declared, a single type, a family or the types
of a block, with its context: the analysis of its declaration and its public declarations (`T`,
`T.F`, `T.dtor`, `T.corec`, `T.fold`, `T.contract`, …). Output: the instances `PolyIso` and
`PolyMap` for `fun X => T (H₁ X) … (Hₙ X) idx` at every index `idx`, for `H₁`, …, `Hₙ` themselves
instances (`PolyMap` from `PolyMap` instances of the `Hᵢ`, as the instances of the built-in
forms), so that later declarations can nest through `T`; and for every constructor `c` the
`simp` lemmas `T.Poly.map_c` and `T.Poly.mem_c`, the map and membership on `T.c` (see "The simp
lemmas" below), so that `simp` computes through the instances.

This step is separate from the declaration of the type. It runs after it, nothing in the
declaration depends on it, and it cannot affect it: on failure every declaration of this step is
rolled back and a warning is logged, and the type is simply not available for nesting. The warning
gives a short reason: a limit of the step or of the analysis as it is, an error of the generator by
what it failed to generate (`stepPhase`), with the error itself under
`set_option codata.deriveDetails true`. When no parameter may vary because of a field, an info
says so and why. A failure of the `simp` lemmas alone rolls back only them, with a warning; the
instances stay. In an open
run of a `mixed_mutual` block that an outer run nests through, the outer run needs the
instances in the run's extra parameters: a failure, or such a parameter that cannot vary, is an
error, which stops the block.

The parameters of `T` that may vary, the *holes*, are those of sort `Type u` that no other
parameter's type and no index's type depends on and that are used, outside the occurrences of
`T` and their indices, only in fields whose type has an occurrence structure in them
(`Gen/Occ.lean`, with the parameters as the holes) and that no later argument and no result index
depends on. Such a field is at a *parameter position*; it may mention several holes, and its
structure in the premises is that structure with `Occ.ofIso Hᵢ` at the occurrences of the `i`-th
hole (`Holes.atHole?`, `fieldOcc`). When a field has no structure in all the holes it mentions,
the fewest are dropped, the first ones first, so that the others have one (`refineHoles`).
A nested argument that mentions a hole outside the occurrences counts too when it splits through
products and sums into parts with only holes or only occurrences, or into such parts and parts
with both under a named type constructor or a function that have a structure in two variables
(`splitParts`, `mixOcc`, `imixOcc`).

With the holes fixed, the constructors of the presentation are those of `T` with such nested
arguments split (`VCtor`, `withVCtors`): an argument `p : α × T α` becomes its parts `p.1`, a field
at a parameter position, and `p.2`, a recursive argument, and through a sum `f : T α ⊕ α` the
constructor becomes one constructor of the presentation per side, `app_inl` and `app_inr` (with a
suffix when a name is taken, as are the names of the parts). With indices a nested argument is
split as well when its positions are at an index only after cases on them (`severalIdx`,
`T n × T (n + 1)`, `A × B` in a block). Through sums, at most `maxSplit` constructors of the
presentation come from one constructor: beyond, the arguments through sums are not split, and
have a structure in two variables or their indexed structure. A part with both a hole and the
type under a named type constructor or a function (`p : List (α × T α)`, `k : Nat → α × T α`,
`p : List (α ⊕ T α)`) has a structure in two variables (`Occ₂`, `Model/Occ2.lean`, a
`MixField`): its structure in the occurrences alone, the holes constant, gone through by its
combinators down to parts in the holes (`Occ₂.ofX`, at their structure in the premises) and parts
in the occurrences (`Occ₂.ofY`). It is data of the presentation with a shape, a position in `P`
and one in `B`, its layer `Occ₂.toC`, and `T.F.map`, which maps it by its structure in the
occurrences, is its map in them by `Occ₂.AgreeY` (`ofL_map`). With indices the structure is over
the index of the presentation (`IOcc₂`, `Model/IOcc2.lean`, `imixOcc`), and in a block a nested
argument whose positions are at a type of the block only after cases on them inside a named type
constructor (`p : List (RA α × Nat)`) has one too, with no part in the holes: its positions then
carry the presentation's index by construction. When its positions are at one index after cases
(`oneIdx`, the recursor's analysis too), it is the plain structure at that index
(`IOcc₂.ofOcc₂`, `flatOcc?`, `mixOcc`), and its rules are stated as without indices; `T.F.map` is
its map by `IOcc₂.AgreeY`, through a sum too (`proveMapFlat`). The layer `T.F (H X) Y` is then
presented as `Lay P B X Y` (`T.Poly.S`, `T.Poly.P`, `T.Poly.B`, `T.Poly.toL`, `T.Poly.ofL` and
their laws; `toL` through the products by projections and through the sums by `Sum.casesOn`,
`ofL` building the pairs and injections, `polyDispatch`, `applyVCtor`), and the generic theorems
of `Model/Poly.lean` do the rest from the contract (`T.Poly.fix`, the instances
`T.Poly.instPolyIso`, `T.Poly.instPolyMap`, and when the last parameter is the last hole,
`T.Poly.instPolyIsoEta` and `T.Poly.instPolyMapEta` for `T a₁ … aₙ₋₁` itself, the latter across
universes when the universe of that parameter is its own, `u` or `u + 1` say).

With indices, the presentation is a family over an index `I`, with the index of a position
(`T.Poly.idx`) and the signature of the trees of shapes (`T.Poly.sig`): `I` is the packed index of
a family, and for a block `Blk.Poly.Ix`, the block's index without the parameters that vary
(`Blk.Ix` takes all the parameters). The layer at `i : I` is `T.F (H X) Y (ι i)` presented as
`ILay sig P X (fun j => Y (ι j)) i`, with `ι` the identity, or in a block `Blk.Poly.ixIn` into the
block's index at the premises. The presentation is per block (`Blk.Poly.*`), the instances per
type, with the type's indices as arguments: `Tₘ.Poly.instPolyIso` for `fun X => Tₘ (H X) idx`
at the index `⟨idx⟩` (`Blk.Poly.Ix.Tₘ idx`), `Tₘ.Poly.instPolyMap`, and the eta forms for a type of
a block without indices.

`toL` and the positions of its layers are by cases (`casesOn`, `MVarId.cases`, with indices
`casesPos` for the positions and in a block cases on the index first), `ofL` by cases on the
shape, and the laws by cases (on the split arguments too, `polyDestructure`) and rewriting with
the laws of `Model/Occ.lean`; the proof arguments of `coFix` and `inFix` (`icoFix`, `iinFix`) are
`rw` scripts on goal metavariables, everything else instantiates a theorem of `Model/Poly.lean`.

Scope: in a block, a nested argument with positions at several types of the block inside a named
type constructor (`List (Ping × Pong)`) gets its instances, but not its `simp` lemmas, which
state the members by the type of each, and the step warns. A hole in the same field as `T` has a
structure in two variables unless it is in another argument of a leaf than `T` (`E α (T α)` inside
a list), or under a functor on families: the hole is constant there. A hole that is a family (an
`IPolyIso` instance) is not supported: `Model/Poly.lean` has the fixpoint for a parameter that is
a type.
-/

open Lean Meta Elab Term

register_option codata.deriveDetails : Bool := {
  defValue := false
  descr := "show the error itself when the instances of a declared type are not generated \
    (step 5 of the `codata` and `data` commands)"
}

namespace Codata.Gen

/-- An error of step 5 worded for the declaration, a limit of the step, which the report of a
failure keeps as it is (`stepPhase`). -/
def throwLimit (msg : MessageData) : MetaM α :=
  throwError (MessageData.tagged `Codata.Gen.limit msg)

/-- Is `e` an internal error of the generators, rather than an expected failure of the analysis
(no occurrence structure, no instance)? Those are not caught. -/
def isInternalError (e : Exception) : MetaM Bool := do
  return (← e.toMessageData.toString).startsWith "internal error"

/-- Run the part `k` of step 5, which generates `what`. A limit of the step (`throwLimit`), a
timeout, and with `worded` any error but an internal one (those of the analysis are worded for the
declaration), go through as they are; any other error, of the generator, is reported by what
failed, with the error itself under `set_option codata.deriveDetails true`. -/
def stepPhase (what : MessageData) (k : TermElabM α) (worded := false) : TermElabM α := do
  try k catch e =>
    if e.toMessageData.hasTag (· == `Codata.Gen.limit) then throw e
    if worded && !(← isInternalError e) then throw e
    if codata.deriveDetails.get (← getOptions) then
      throwError "generating {what} failed:\n{e.toMessageData}"
    throwError "generating {what} failed, an error of the generator \
      (`set_option codata.deriveDetails true` shows it)"

/-- The holes of the structure of a field in the parameters `as`: their occurrences, with the
structure `atHole?` put at each; without, a single parameter `a : Type lvl` as the hole. -/
def paramHoles (as : Array Expr) (lvl : Level) (atHole? : Option ((Expr → Expr) × Level) := none) :
    Holes where
  holeOf? e := if as.contains e then some #[] else none
  isTypeApp e := as.contains e.getAppFn
  mentions e := as.any (e.containsFVar ·.fvarId!)
  lvl
  fam? := none
  atHole?

/-- The structure of the field type `ty` in the parameters among `holes` that it mentions, each at
the structure of its premise, `oHs` (`Occ.ofIso Hᵢ`, in the order of `holes`), for the variable
at the universe `lx`. -/
def fieldOcc (holes oHs : Array Expr) (lx : Level) (ty : Expr) : MetaM Expr := do
  let hs := holes.filter (ty.containsFVar ·.fvarId!)
  let some h := hs[0]? | throwError "internal error: no parameter in the field{indentExpr ty}"
  let atH (e : Expr) : Expr := match holes.findIdx? (· == e) with
    | some i => oHs[i]!
    | none => e
  occOf (paramHoles hs (← typeLevel h) (some (atH, lx))) ty

/-- The universes of an occurrence structure `o : Occ Sh Pos G`, by the names of those of `Occ`. -/
def occLevels (o : Expr) : MetaM (List (Name × Level)) := do
  let ty ← whnfR (← inferType o)
  unless ty.isAppOfArity ``Codata.Occ 3 do
    throwError "internal error: not an occurrence structure{indentExpr o}"
  return (← getConstInfo ``Codata.Occ).levelParams.zip ty.getAppFn.constLevels!

/-- The structure in two variables (`Occ₂`) of a nested argument that mentions the parameters
`holes` outside the occurrences, from its structure `o` in the occurrences alone (the parameters
constant, at the occurrences' universe `ly`): a part without the parameters is its structure in
the occurrences (`Occ₂.ofY`), a constant with them its structure in the parameters at their
premises `oHs`, of variable at `lx` (`Occ₂.ofX`, `fieldOcc`), and products, sums, functions,
dependent pairs and named type constructors in one variable are gone through. Not through a leaf
whose functor mentions a parameter, or a domain that does. -/
partial def mixOcc (holes oHs : Array Expr) (lx ly : Level) (o : Expr) : TermElabM Expr := do
  let o ← instantiateMVars o
  let has (e : Expr) : Bool := holes.any (e.containsFVar ·.fvarId!)
  let lv (m : List (Name × Level)) (n : Name) : Level := (m.lookup n).getD Level.zero
  let at1 (o : Expr) (n : Name) (mk : List (Name × Level) → List (Name × Level)) :
      TermElabM Expr := do
    let ta := (← whnfR (← inferType o)).getAppArgs
    return mkAppN (← constAt n (mk (← occLevels o))) #[ta[0]!, ta[1]!, ta[2]!, o]
  if !has o then
    return ← at1 o ``Codata.Occ₂.ofY fun m =>
      [(`s, lv m `s), (`q, lv m `p), (`w, lv m `u), (`v, lv m `v), (`u, lx)]
  let ex ← explicitArgs o
  let under (n : Name) (A f : Expr) : TermElabM Expr := do
    if has A then throwError "a parameter in the domain of a function or of a dependent pair"
    let f' ← withLocalDeclD `x A fun x => do
      mkLambdaFVars #[x] (← mixOcc holes oHs lx ly (f.beta #[x]))
    mkAppM n #[A, f']
  match o.getAppFn.constName? with
  | some ``Codata.Occ.const =>
    let oX ← fieldOcc holes oHs lx ex[0]!
    at1 oX ``Codata.Occ₂.ofX fun m =>
      [(`s, lv m `s), (`p, lv m `p), (`u, lv m `u), (`v, lv m `v), (`w, ly)]
  | some ``Codata.Occ.prod =>
    mkAppM ``Codata.Occ₂.prod
      #[← mixOcc holes oHs lx ly ex[0]!, ← mixOcc holes oHs lx ly ex[1]!]
  | some ``Codata.Occ.sum =>
    mkAppM ``Codata.Occ₂.sum
      #[← mixOcc holes oHs lx ly ex[0]!, ← mixOcc holes oHs lx ly ex[1]!]
  | some ``Codata.Occ.pi => under ``Codata.Occ₂.pi ex[0]! ex[1]!
  | some ``Codata.Occ.piP => under ``Codata.Occ₂.piP ex[0]! ex[1]!
  | some ``Codata.Occ.sigma => under ``Codata.Occ₂.sigma ex[0]! ex[1]!
  | some ``Codata.Occ.comp =>
    if has ex[0]! then throwError "a parameter in a type constructor applied to the type"
    mkAppM ``Codata.Occ₂.comp #[ex[0]!, ← mixOcc holes oHs lx ly ex[1]!]
  | _ => throwError "a parameter and the type in one argument of a type constructor"

/-- The universes of an indexed occurrence structure `o : IOcc Sh Pos pidx G`, by the names of
those of `IOcc`. -/
def ioccLevels (o : Expr) : MetaM (List (Name × Level)) := do
  let ty ← whnfR (← inferType o)
  unless ty.isAppOfArity ``Codata.IOcc 5 do
    throwError "internal error: not an indexed occurrence structure{indentExpr o}"
  return (← getConstInfo ``Codata.IOcc).levelParams.zip ty.getAppFn.constLevels!

/-- The structure in two variables over the index `I` of the presentation (`IOcc₂`) of a nested
argument of a family or of a type of a block, from its indexed structure `o` in the occurrences
alone, over the family's own index, as `mixOcc`: a constant with the parameters `holes` is its
structure in them at their premises `oHs` (`IOcc₂.ofX`), without them a constant; an occurrence,
or a plain leaf applied to one, is a part in `Y` alone at its index read in `I` by `tr`
(`IOcc₂.ofY`); products, sums, functions, dependent pairs and plain type constructors are gone
through. Not through a functor on families, a leaf whose functor mentions a parameter, or a
domain that does. -/
partial def imixOcc (holes oHs : Array Expr) (lx ly : Level) (I : Expr) (tr : Expr → Expr)
    (o : Expr) : TermElabM Expr := do
  let o ← instantiateMVars o
  let has (e : Expr) : Bool := holes.any (e.containsFVar ·.fvarId!)
  let lv (m : List (Name × Level)) (n : Name) : Level := (m.lookup n).getD Level.zero
  let lI ← typeLevel I
  let go := imixOcc holes oHs lx ly I tr
  let ex ← explicitArgs o
  -- A part in `Y` alone, an indexed structure over `I`.
  let ofY (h : Expr) : TermElabM Expr := do
    let ta := (← whnfR (← inferType h)).getAppArgs
    let m ← ioccLevels h
    return mkAppN (← constAt ``Codata.IOcc₂.ofY
      [(`u, lx), (`w, lv m `u), (`v, lv m `v), (`s, lv m `s), (`q, lv m `p), (`j, lI)])
      #[I, ta[1]!, ta[2]!, ta[3]!, ta[4]!, h]
  let under (n : Name) (A f : Expr) : TermElabM Expr := do
    if has A then throwError "a parameter in the domain of a function or of a dependent pair"
    let f' ← withLocalDeclD `x A fun x => do mkLambdaFVars #[x] (← go (f.beta #[x]))
    mkAppM n #[A, f']
  match o.getAppFn.constName? with
  | some ``Codata.IOcc.const =>
    let A := ex[0]!
    if has A then
      let oX ← fieldOcc holes oHs lx A
      let ta := (← whnfR (← inferType oX)).getAppArgs
      let m ← occLevels oX
      return mkAppN (← constAt ``Codata.IOcc₂.ofX
        [(`u, lv m `u), (`w, ly), (`v, lv m `v), (`s, lv m `s), (`p, lv m `p), (`j, lI)])
        #[I, ta[0]!, ta[1]!, ta[2]!, oX]
    return mkApp2 (← constAt ``Codata.IOcc₂.const
      [(`u, lx), (`w, ly), (`v, ← typeLevel A), (`j, lI)]) I A
  | some ``Codata.IOcc.hole =>
    ofY (mkApp2 (← constAt ``Codata.IOcc.hole [(`u, ly), (`j, lI)]) I (tr ex[0]!))
  | some ``Codata.IOcc.ofOcc =>
    if has ex[0]! then throwError "a parameter in a type constructor applied to the type"
    ofY (← mkAppOptM ``Codata.IOcc.ofOcc #[I, none, none, none, ex[0]!, tr ex[1]!])
  | some ``Codata.IOcc.prod => mkAppM ``Codata.IOcc₂.prod #[← go ex[0]!, ← go ex[1]!]
  | some ``Codata.IOcc.sum => mkAppM ``Codata.IOcc₂.sum #[← go ex[0]!, ← go ex[1]!]
  | some ``Codata.IOcc.pi => under ``Codata.IOcc₂.pi ex[0]! ex[1]!
  | some ``Codata.IOcc.piP => under ``Codata.IOcc₂.piP ex[0]! ex[1]!
  | some ``Codata.IOcc.sigma => under ``Codata.IOcc₂.sigma ex[0]! ex[1]!
  | some ``Codata.IOcc.compC =>
    if has ex[0]! then throwError "a parameter in a type constructor applied to the type"
    mkAppM ``Codata.IOcc₂.comp #[ex[0]!, ← go ex[1]!]
  | _ => throwError "a parameter and the type in one argument of a functor on families"

/-- The plain structure, at the occurrences' universe `ly`, of an indexed structure whose
positions are all at one index (`oneIdx`): an occurrence is the occurrence, a plain leaf at the
index the leaf, the combinators the plain ones; `none` through a functor on families. -/
partial def flatOcc? (ly : Level) (o : Expr) : TermElabM (Option Expr) := do
  let ex ← explicitArgs o
  let under (n : Name) (A f : Expr) : TermElabM (Option Expr) := do
    let f'? ← withLocalDeclD `x A fun x => do
      (← flatOcc? ly (f.beta #[x])).mapM fun b => mkLambdaFVars #[x] b
    f'?.mapM fun f' => mkAppM n #[A, f']
  let two (n : Name) : TermElabM (Option Expr) := do
    let some l ← flatOcc? ly ex[0]! | return none
    let some r ← flatOcc? ly ex[1]! | return none
    some <$> mkAppM n #[l, r]
  match o.getAppFn.constName? with
  | some ``Codata.IOcc.const =>
    return mkApp (← constAt ``Codata.Occ.const [(`u, ly), (`v, ← typeLevel ex[0]!)]) ex[0]!
  | some ``Codata.IOcc.hole => constAt ``Codata.Occ.hole [(`u, ly)]
  | some ``Codata.IOcc.ofOcc => return ex[0]!
  | some ``Codata.IOcc.prod => two ``Codata.Occ.prod
  | some ``Codata.IOcc.sum => two ``Codata.Occ.sum
  | some ``Codata.IOcc.pi => under ``Codata.Occ.pi ex[0]! ex[1]!
  | some ``Codata.IOcc.piP => under ``Codata.Occ.piP ex[0]! ex[1]!
  | some ``Codata.IOcc.sigma => under ``Codata.Occ.sigma ex[0]! ex[1]!
  | some ``Codata.IOcc.compC =>
    let some r ← flatOcc? ly ex[1]! | return none
    some <$> mkAppM ``Codata.Occ.comp #[ex[0]!, r]
  | _ => return none

/-- Run `k` on `n` local variables, the `i`-th with the name, binder info and type `mk i`. -/
def withLocalsN (n : Nat) (mk : Nat → TermElabM (Name × BinderInfo × Expr))
    (k : Array Expr → TermElabM α) : TermElabM α :=
  let rec go (i : Nat) (acc : Array Expr) : TermElabM α := do
    if _h : i < n then
      let (nm, bi, ty) ← mk i
      withLocalDecl nm bi ty fun x => go (i + 1) (acc.push x)
    else k acc
  go 0 #[]

/-- `f a`, where `a` is built from the type `f` expects (`mk`), and checked against it. -/
def fillArg (f : Expr) (mk : Expr → TermElabM Expr) : TermElabM Expr := do
  let ty ← whnf (← inferType f)
  let .forallE _ dom _ _ := ty | throwError "internal error: not a function{indentExpr f}"
  let dom ← instantiateMVars dom
  let a ← mk dom
  unless ← isDefEq dom (← inferType a) do
    throwError "internal error: ill-typed argument{indentExpr a}\nexpected{indentExpr dom}"
  return mkApp f a

/-- The constant `n` applied to new metavariables for its first `k` arguments, which `fillArg`
determines. -/
def mkAppMVars (n : Name) (k : Nat) : MetaM Expr := do
  let f ← mkConstWithFreshMVarLevels n
  let (xs, _, _) ← forallMetaBoundedTelescope (← inferType f) k
  return mkAppN f xs

/-- The constant `n` applied to new metavariables for its first `k` arguments, the first of them
assigned `args`. -/
def mkAppFirst (n : Name) (args : Array Expr) (k : Nat) : MetaM Expr := do
  let f ← mkAppMVars n k
  for x in f.getAppArgs, a in args do
    unless ← isDefEq x a do throwError "internal error: ill-typed argument{indentExpr a}"
  instantiateMVars f

/-- `fun xs => body xs` on the binders of the function type `ty`. -/
def lamOf (ty : Expr) (body : Array Expr → TermElabM Expr) : TermElabM Expr :=
  forallTelescope ty fun xs _ => do mkLambdaFVars xs (← body xs)

/-- A proof of `ty` by the tactic `tac`, on the binders of `ty`, beta-reduced. -/
def proveOn (ty : Expr) (tac : TSyntax `tactic) : TermElabM Expr :=
  forallTelescope ty fun xs body => do
    mkLambdaFVars xs (← proveHere (← Core.betaReduce body) (runTac · tac))

namespace Ctx

variable (ctx : Ctx)

/-- `T.Poly.s`. -/
def polyName (s : String) : Name := .str (.str ctx.name "Poly") s

/-! ### The holes -/

/-- Run `k` with local instances `PolyMap Hᵢ Hᵢ` for the premises `Hs` with their instances
`insts`: a leaf at the premises (`fun X => E (H₁ X) (H₂ X)`) has a `PolyMap` instance only with
those of its premises, which the analysis of a field checks (`leafOcc`). Nothing generated
mentions them. -/
def withSelfMaps (Hs Ss Rs insts : Array Expr) (k : TermElabM α) : TermElabM α :=
  withLocalsN Hs.size (fun i => return (`map, .instImplicit, ← mkAppOptM ``Codata.PolyMap
    (#[Hs[i]!, Hs[i]!, Ss[i]!, Rs[i]!, insts[i]!, insts[i]!].map some))) fun _ => k

/-- Run `k` on premises for the parameters `cands`, as the instances will have them: for each
`Hᵢ : Type x → Aᵢ` with an instance `PolyIso Hᵢ Sᵢ Rᵢ`, given to `k` as `Occ.ofIso Hᵢ`, and the
universe `x`. For the checks of `refineHoles` only. -/
def withCheckPremises (cands : Array Expr) (k : Array Expr → Level → TermElabM α) :
    TermElabM α := do
  let n := cands.size
  let fresh := ctx.freshLevels (1 + 2 * n)
  let lv (i : Nat) : Level := .param fresh[i]!
  withLocalsN n (fun i => do
      return (`H, .default, ← mkArrow (mkSort (lv 0).succ) (← inferType cands[i]!))) fun Hs => do
  withLocalsN n (fun i => return (`S, .default, mkSort (lv (1 + 2 * i)).succ)) fun Ss => do
  withLocalsN n (fun i => return (`R, .default, ← mkArrow Ss[i]! (mkSort (lv (2 + 2 * i)).succ)))
    fun Rs => do
  withLocalsN n (fun i => return (`inst, .instImplicit,
      ← mkAppM ``Codata.PolyIso #[Hs[i]!, Ss[i]!, Rs[i]!])) fun insts => do
  withSelfMaps Hs Ss Rs insts do
  k (← Hs.mapM fun H => mkAppOptM ``Codata.Occ.ofIso #[some H, none, none, none]) (lv 0)

/-- The parameters among `cands` that `ty` mentions outside the occurrences of the types being
defined and their indices. -/
def outside (cands : Array Expr) (ty : Expr) : Array Expr :=
  let ty := ctx.replaceOccU ty (fun _ idx => mkAppN (Lean.mkConst ``Unit) idx) ctx.lvl
  cands.filter (ty.containsFVar ·.fvarId!)

/-- The parts of the type `ty` of a nested argument, split through products and sums as far as
needed for each to mention either the types being defined or the parameters among `cands`, not
both outside the occurrences, or else to be a part with both under a named type constructor or a
function, with a structure in two variables (`mixOcc`, `imixOcc`); `none` if it does not split
so. -/
partial def splitParts (cands : Array Expr) (ty : Expr) : TermElabM (Option (Array Expr)) := do
  if !ctx.mentions ty || (ctx.outside cands ty).isEmpty then return some #[ty]
  let e ← whnfOcc ty
  if e.isAppOfArity ``Prod 2 || e.isAppOfArity ``Sum 2 then
    let some l ← splitParts cands e.appFn!.appArg! | return none
    let some r ← splitParts cands e.appArg! | return none
    return some (l ++ r)
  return some #[ty]

/-- The structure in two variables of a part `ty` of a nested argument with the parameters
`holes` outside the occurrences (`mixOcc`), at the premises `oHs` of variable at `lx`; with
indices over the family's own index (`imixOcc`), which suffices to check that it has one. -/
def mixOf (holes oHs : Array Expr) (lx : Level) (ty : Expr) : TermElabM Expr := do
  let o ← occOf (ctx.holes ctx.famIdx?) ty
  if ctx.idxed then return ← imixOcc holes oHs lx ctx.lvl ctx.J id o
  mixOcc holes oHs lx ctx.lvl o

/-- The sublists of `k` elements of `l`, in lexicographic order: those with the first ones first.
-/
def sublistsOf {α : Type} : List α → Nat → List (List α)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | x :: xs, k + 1 => (sublistsOf xs k).map (x :: ·) ++ sublistsOf xs (k + 1)

/-- Remove the candidates that may not vary, until none is removed. A field may mention several:
it has a structure in all of them, each at its premise (`fieldOcc`). When it has none, the fewest
candidates are dropped so that the others have one, the first ones first (in an open run of a
`mixed_mutual` block the parameters for the outer types come last): one, the first that will do,
then two, …; if none can be dropped so, all of them are. A nested argument with candidates outside
the occurrences splits into parts (`splitParts`), those with candidates checked as fields. With
the reason each dropped candidate may not vary, for the message when none may. -/
partial def refineHoles (cands : Array Expr) (why : Array (Expr × MessageData) := #[]) :
    TermElabM (Array Expr × Array (Expr × MessageData)) := do
  let hasOcc (ms : Array Expr) (ty : Expr) : TermElabM Bool := do
    try
      if ctx.mentions ty then
        ctx.withCheckPremises ms fun oHs lx => do discard <| ctx.mixOf ms oHs lx ty
      else if let #[h] := ms then
        discard <| occOf (paramHoles #[h] (← typeLevel h)) ty
      else
        ctx.withCheckPremises ms fun oHs lx => do discard <| fieldOcc ms oHs lx ty
      pure true
    catch e => if ← isInternalError e then throw e else pure false
  -- The candidates to drop for the field `ty` with the candidates `ms`: none if it has a structure
  -- in all, else the fewest, the first ones first (beyond a few candidates, only the first ones).
  let dropFor (ms : Array Expr) (ty : Expr) : TermElabM (Array Expr) := do
    if ← hasOcc ms ty then return #[]
    for k in [1:ms.size] do
      let drops := if ms.size ≤ 5 then sublistsOf ms.toList k else [ms.toList.take k]
      for d in drops do
        let drop := d.toArray
        if ← hasOcc (ms.filter (!drop.contains ·)) ty then return drop
    return ms
  let mut bad : Array (Expr × MessageData) := #[]
  for c in ctx.ctors do
    let field (a : ArgInfo) : MessageData := m!"the field `{a.name}` of `{c.name}`"
    -- In an index of the result, a parameter is fixed by the constructor.
    bad := bad ++ (cands.filter fun h => c.uidx.any (·.containsFVar h.fvarId!)).map
      (·, m!"the result index of `{c.name}`")
    for a in c.args, i in [0:c.args.size] do
      if a.kind.isData then
        let ms := cands.filter (a.type.containsFVar ·.fvarId!)
        if ms.isEmpty then continue
        let later := (c.args.extract (i + 1) c.args.size).any
            (·.type.containsFVar a.fvar.fvarId!) ||
          c.uidx.any (·.containsFVar a.fvar.fvarId!)
        if later then
          bad := bad ++ ms.map (·, m!"{field a}, which a later argument or the result index \
            depends on")
        else
          bad := bad ++ (← dropFor ms a.type).map (·, m!"{field a}, without an occurrence \
            structure in it")
      else
        -- Outside the occurrences of the type, and in their indices: only in a nested argument
        -- that splits through products and sums into parts with the candidates and parts with
        -- the type (`splitParts`), the former as fields, or parts with both that have a structure
        -- in two variables.
        let ms := ctx.outside cands a.type
        if ms.isEmpty then continue
        let parts? ← if a.kind.isNest then ctx.splitParts cands a.type else pure none
        let both := m!"{field a}, with the type, without an occurrence structure in both"
        match parts? with
        | none => bad := bad ++ ms.map (·, both)
        | some parts =>
          for part in parts do
            let ms := if ctx.mentions part then ctx.outside cands part
              else cands.filter (part.containsFVar ·.fvarId!)
            if ms.isEmpty then continue
            bad := bad ++ (← dropFor ms part).map (·, both)
  if bad.isEmpty then return (cands, why)
  let why := why ++ bad.filter fun (h, _) => !why.any (·.1 == h)
  refineHoles (cands.filter fun h => !bad.any (·.1 == h)) why

/-- The parameters that may vary, with the reason each other parameter that is a type may not, in
order, and whether one may not because of a field (`refineHoles`). -/
def polyHoles : TermElabM (Array Expr × Array (Expr × MessageData) × Bool) := do
  let mut cands := #[]
  let mut why := #[]
  for p in ctx.params do
    let isType := match ← instantiateMVars (← inferType p) with
      | .sort (.succ _) => true
      | _ => false
    if !isType then continue
    let used ← ctx.params.anyM fun q => do
      return q != p && (← instantiateMVars (← inferType q)).containsFVar p.fvarId!
    -- An index's type may not mention it: the index is fixed per instance.
    let inIdx ← ctx.types.anyM fun t => t.idx.anyM fun i => do
      return (← instantiateMVars (← inferType i)).containsFVar p.fvarId!
    if used then why := why.push (p, m!"the type of another parameter")
    else if inIdx then why := why.push (p, m!"the type of an index")
    else cands := cands.push p
  let (holes, dropped) ← ctx.refineHoles cands
  let all := why ++ dropped
  return (holes, ctx.params.filterMap (fun p => all.find? (·.1 == p)), !dropped.isEmpty)

/-! ### The context of the instances -/

/-- A field at a parameter position: its position among the constructor's arguments, and its
structure in the premise, with its shapes and positions. -/
structure HoleField where
  k : Nat
  occ : Expr
  sh : Expr
  pos : Expr
  deriving Inhabited

/-- A nested argument with a parameter that varies outside the occurrences under a named type
constructor or a function (`p : List (α × T α)`, `k : Nat → α × T α`), or in a block one whose
positions are at a type of the block only after cases on them (`p : List (RA α × Nat)`): its
position among the constructor's arguments, its structure in two variables (`Occ₂`, `mixOf`;
with indices `IOcc₂` over the index of the presentation, `imixOcc`) over the premises, the
occurrences at the analysis' universe, with its shapes and positions of both kinds (and with
indices the index of a position in `Y`), and the argument as the analysis has it, with its
structure in the occurrences alone. -/
structure MixField where
  k : Nat
  occ : Expr
  sh : Expr
  px : Expr
  py : Expr
  arg : ArgInfo
  nest : Nest
  /-- With indices, the index of a position in `Y`, in the index of the presentation. -/
  pidx? : Option Expr := none
  /-- With indices, when the positions in `Y` are all at one index after cases on them: the
  structure is the plain one `o₂` at that index `i₀` of the presentation (`IOcc₂.ofOcc₂`), and
  the rules are stated with `o₂`, as without indices. -/
  flat? : Option (Expr × Expr) := none
  deriving Inhabited

/-- How an argument of a constructor is presented (`VCtor`): as an argument of the presentation,
or split through a product or a sum, whose two types (of the analysis) are kept. -/
inductive Tpl where
  | part (a : ArgInfo)
  | prod (l r : Tpl)
  | sum (l r : Tpl) (A B : Expr)
  deriving Inhabited

/-- Does the template split through a sum? -/
def Tpl.hasSum : Tpl → Bool
  | .part _ => false
  | .prod l r => l.hasSum || r.hasSum
  | .sum .. => true

/-- The ways through the template: the alternative taken at each sum on the way, and the parts
reached, in order. -/
def Tpl.paths : Tpl → Array (Array Bool × Array ArgInfo)
  | .part a => #[(#[], #[a])]
  | .prod l r => l.paths.flatMap fun (cl, al) => r.paths.map fun (cr, ar) => (cl ++ cr, al ++ ar)
  | .sum l r _ _ => l.paths.map (fun (c, as) => (#[true] ++ c, as)) ++
      r.paths.map (fun (c, as) => (#[false] ++ c, as))

/-- A constructor of the presentation: a constructor `real` of the type with an alternative at
each sum of its split arguments (`tpls`, per argument), its arguments the parts on the way, in
`ctor`. Without splits it is the constructor itself. The arguments of a constructor are split when
a nested one mentions a parameter that varies outside the occurrences (`α × T α`), or in a block
has its positions at several types (`A × B`), so that each part is a field at a parameter
position, a recursive argument or data. -/
structure VCtor where
  real : Nat
  tpls : Array Tpl
  choices : Array Bool
  ctor : Ctor
  deriving Inhabited

/-- Does the constructor split an argument? -/
def VCtor.split (v : VCtor) : Bool := v.tpls.any fun | .part _ => false | _ => true

/-- The local variables of the generated declarations: the holes and the other parameters (of
the analysis), the premises `Hᵢ : Type x → Aᵢ` (and `H'ᵢ`, at other universes, for `PolyMap`),
their presentations `Sᵢ`, `Rᵢ` and instances, the fields at parameter positions of each
constructor, and the universes. -/
structure Poly where
  holes : Array Expr
  consts : Array Expr
  Hs : Array Expr
  Hs' : Array Expr
  Ss : Array Expr
  Rs : Array Expr
  insts : Array Expr
  insts' : Array Expr
  /-- The premises `PolyMap Hᵢ H'ᵢ` of `instPolyMap`, so that it is a map between instantiations
  of one functor only when the premises are. -/
  maps : Array Expr := #[]
  fields : Array (Array HoleField)
  /-- The arguments with a structure in two variables of each constructor of the presentation,
  which there are of kind `.data`. -/
  mixed : Array (Array MixField) := #[]
  /-- The constructors of the presentation, `fields` and `mixed` by their position. -/
  vc : Array VCtor := #[]
  /-- The universes of this step: `x`, `x'`, `y`, `y'`, the primed universe of the last
  parameter (`instPolyMapEta`), then `sᵢ`, `pᵢ` per hole, then the primed universes. -/
  fresh : List Name
  /-- The user's universes of the holes and their primed versions, for `H'`. -/
  primes : List (Name × Level)
  /-- With indices, the index of the presentation: the packed index `J` over the constants, or in
  a block `Blk.Poly.Ix consts`, the block's index without the holes. -/
  I : Expr := Lean.mkConst ``Unit
  /-- An index of the analysis as an index of the presentation: in a block, `Blk.Ix.Tₘ params`
  becomes `Blk.Poly.Ix.Tₘ consts`. -/
  toPolyIdx : Expr → Expr := id
  deriving Inhabited

namespace Poly

variable (P : Poly)

def lvl (i : Nat) : Level := .param P.fresh[i]!
def lx : Level := P.lvl 0
def lx' : Level := P.lvl 1
def ly : Level := P.lvl 2
def ly' : Level := P.lvl 3

/-- `S₁ R₁ S₂ R₂ …`. -/
def SR : Array Expr := (P.Ss.zip P.Rs).flatMap fun (s, r) => #[s, r]

/-- The parameters of `T.Poly.S`, `P`, `B`. -/
def psB : Array Expr := P.consts ++ P.SR

/-- The premises of `toL`, `ofL`, `fix`, …: `{consts} (H…) {S R…} [insts]`. -/
def premises : Array Expr := P.consts ++ P.Hs ++ P.SR ++ P.insts

/-- `e` at the primed universes of the holes. -/
def prime (e : Expr) : Expr :=
  e.instantiateLevelParams (P.primes.map (·.1)) (P.primes.map (·.2))

/-- `e` with the holes at the premises `Hs` applied to `X`. -/
def subX (Hs : Array Expr) (X e : Expr) : Expr := e.replaceFVars P.holes (Hs.map (mkApp · X))

/-- The arguments with a structure in two variables of the `m`-th constructor. -/
def mixAt (m : Nat) : Array MixField := (P.mixed[m]?).getD #[]

end Poly

/-- The parameters at the premises applied to `X`: `consts`, `Hᵢ X` for the holes. -/
def polyParams (P : Poly) (Hs : Array Expr) (X : Expr) : Array Expr :=
  ctx.params.map fun p => match P.holes.findIdx? (· == p) with
    | some i => mkApp Hs[i]! X
    | none => p

/-- The constant `n` at its universes `σ` (by name; the others as they are). -/
def polyConst (n : Name) (σ : List (Name × Level) := []) : MetaM Expr := do
  let ci ← getConstInfo n
  return .const n (ci.levelParams.map fun p => (σ.lookup p).getD (.param p))

/-! ### Indices

With indices, the presentation is a family over the index `P.I`: the packed index `J` of a family,
or for a block `Blk.Poly.Ix consts`, the block's index `Blk.Ix params` without the parameters that
vary, which it takes although its constructors do not use them. The family of the type at the
premises lives over its own index `I'` (`J`, or `Blk.Ix (H X)`), read along `ι : P.I → I'`, the
identity or `Blk.Poly.ixIn`. -/

/-- The index of the presentation of the family-level index arguments `idx`. -/
def polyIdx (P : Poly) (idx : Array Expr) : MetaM Expr := return P.toPolyIdx (← ctx.pack idx)

/-- `ι j`, the index `j` of the presentation as an index of the family at the premises `Hs` and
`X`: `j`, or in a block `Blk.Poly.ixIn params j`. -/
def polyIota (P : Poly) (Hs : Array Expr) (X j : Expr) : MetaM Expr := do
  if !ctx.isBlock then return j
  return mkApp (mkAppN (← polyConst (ctx.polyName "ixIn")) (ctx.polyParams P Hs X)) j

/-- The universe `v` of a family `Y : … → Type v`. -/
def famLevel (Y : Expr) : MetaM Level := do
  forallTelescopeReducing (← inferType Y) fun _ body => do
    let .sort l ← whnf body | throwError "internal error: not a family{indentExpr Y}"
    let some v := l.dec | throwError "internal error: not a family of types{indentExpr Y}"
    return v

/-- In a block, `Blk.Poly.Ix consts`, the block's index without the holes, with a constructor per
type whose arguments are that type's indices, and `Blk.Poly.ixIn params` into `Blk.Ix params`;
returns `P` with the index of the presentation and the translation of the block's index. -/
def genPolyIx (P : Poly) : TermElabM Poly := do
  let name := ctx.polyName "Ix"
  let lvls ← ctx.types.foldlM (init := #[]) fun acc t => do
    return acc ++ (← t.idx.mapM fun i => do getLevel (← inferType i))
  let r := resultLevel lvls
  let ty ← mkForallFVars P.consts (mkSort r.succ)
  let ctorName (m : Nat) : Name :=
    name ++ Name.mkSimple (ctx.shortName m)
  let us ← withLocalDeclD `Ix ty fun Iv => do
    let ctorTys ← ctx.types.mapM fun t =>
      withBinderInfo P.consts .implicit do mkForallFVars (P.consts ++ t.idx) (mkAppN Iv P.consts)
    let us ← ctx.levelParamsOf [] (ctorTys.push ty)
    let Ic := Lean.mkConst name (us.map mkLevelParam)
    addInductive us P.consts.size [{
      name, type := ty
      ctors := (Array.range ctx.types.size).toList.map fun m =>
        { name := ctorName m, type := ctorTys[m]!.replaceFVar Iv Ic } }] ctx.ref
    pure us
  let I := mkAppN (Lean.mkConst name (us.map mkLevelParam)) P.consts
  let ctors := (Array.range ctx.types.size).map fun m =>
    mkAppN (Lean.mkConst (ctorName m) (us.map mkLevelParam)) P.consts
  -- `ixIn`, by cases.
  withLocalDeclD `i I fun i => do
    let value ← mkCasesOnApp name (us.map mkLevelParam) P.consts i (← getLevel ctx.J)
      (fun _ _ => pure ctx.J) fun cname xs => do
        let some m := (Array.range ctx.types.size).find? (ctorName · == cname)
          | throwError "internal error: unexpected constructor {cname}"
        return mkAppN ctx.ixCtors[m]! xs
    let xs := ctx.params.push i
    let (type, value) ← withBinderInfo ctx.params .implicit do
      return (← mkForallFVars xs ctx.J, ← mkLambdaFVars xs value)
    addDef (ctx.polyName "ixIn") (← ctx.levelParamsOf [] #[type, value]) type value ctx.ref
  let toPolyIdx (e : Expr) : Expr := e.replace fun t =>
    match ctx.ixCtors.findIdx? (· == t) with
    | some m => some ctors[m]!
    | none => if t == ctx.J then some I else none
  return { P with I, toPolyIdx }

/-! ### Split arguments -/

/-- The kind of a part of a split argument, as the front end classifies an argument. -/
def classifyPart (ty : Expr) : TermElabM ArgKind := do
  unless ctx.mentions ty do return .data
  let e ← whnfOcc ty
  if let some idx := ctx.holeOf? e then return .plain idx
  if ctx.isTypeApp e then throwError badOcc
  let arity? ← withReducible <| forallTelescopeReducing ty fun ys body => do
    if ys.isEmpty || (ctx.holeOf? (← whnfOcc body)).isNone then return none
    for y in ys do
      if ctx.mentions (← inferType y) then throwError badDomain
    return some ys.size
  if let some n := arity? then return .fn n
  let occ ← instantiateMVars (← occOf (ctx.holes ctx.famIdx?) ty)
  let args := (← whnfR (← inferType occ)).getAppArgs
  if ctx.idxed then
    return .nest { occ, sh := args[1]!, pos := args[2]!, pidx? := some args[3]! }
  return .nest { occ, sh := args[0]!, pos := args[1]!, pidx? := none }

/-- With indices, is `ty` nested with positions at an index only after cases on them (at several
indices, or through a product or a sum)? In a block the index of a position must be a type of the
block at variables (the presentation's index); in a family, the rules of the map and of
membership are stated by components then, each at the type at its index, rather than through the
indexed structure (`IOcc.map`, `IPolyIso.Mem` at an index). -/
def severalIdx (ty : Expr) : TermElabM Bool := do
  if !ctx.idxed || !ctx.mentions ty then return false
  let .nest n ← ctx.classifyPart ty | return false
  let some pidx := n.pidx? | return false
  withLocalDeclD `s n.sh fun s => withLocalDeclD `q (mkApp n.pos s).headBeta fun q => do
    let i ← Core.betaReduce (mkApp2 pidx s q)
    return i.containsFVar s.fvarId! || i.containsFVar q.fvarId!

/-- Does the type `ty` of a nested argument, or of a part of it, need to be split: does it mention
both the types and a hole outside the occurrences, or with indices is it at several indices? -/
def needsSplit (holes : Array Expr) (ty : Expr) : TermElabM Bool := do
  return ctx.mentions ty && (!(ctx.outside holes ty).isEmpty || (← ctx.severalIdx ty))

/-- The template of the argument `a` at its part `name : ty`, its parts new local variables. -/
partial def splitTpl (holes : Array Expr) (a : ArgInfo) (name : Name) (ty : Expr)
    (k : Tpl → TermElabM α) : TermElabM α := do
  let e ← whnfOcc ty
  if (← ctx.needsSplit holes ty) && (e.isAppOfArity ``Prod 2 || e.isAppOfArity ``Sum 2) then
    let (A, B) := (e.appFn!.appArg!, e.appArg!)
    if e.isAppOfArity ``Prod 2 then
      splitTpl holes a (name.appendAfter "_fst") A fun l =>
        splitTpl holes a (name.appendAfter "_snd") B fun r => k (.prod l r)
    else
      splitTpl holes a (name.appendAfter "_inl") A fun l =>
        splitTpl holes a (name.appendAfter "_inr") B fun r => k (.sum l r A B)
  else
    let kind ← ctx.classifyPart ty
    withLocalDeclD name ty fun x =>
      k (.part { a with fvar := x, name, bi := .default, type := ty, kind })

/-- The number of constructors of the presentation for a nested argument of type `ty` split
through its products and sums (`splitTpl`): the ways through its sums. -/
partial def splitCount (holes : Array Expr) (ty : Expr) : TermElabM Nat := do
  let e ← whnfOcc ty
  if (← ctx.needsSplit holes ty) && (e.isAppOfArity ``Prod 2 || e.isAppOfArity ``Sum 2) then
    let l ← splitCount holes e.appFn!.appArg!
    let r ← splitCount holes e.appArg!
    return if e.isAppOfArity ``Prod 2 then l * r else l + r
  return 1

/-- The most constructors of the presentation for one constructor of the type. Beyond, the
arguments through sums are not split: they have a structure in two variables (`mixOcc`), with
indices or in a block in two variables over the index (`imixOcc`), or without a parameter
outside the occurrences their indexed structure. -/
def maxSplit : Nat := 8

/-- `n`, or `n` with the first suffix `_1`, `_2`, … for which `ok` holds. -/
partial def freshSuffix (n : String) (ok : String → Bool) (k : Nat := 0) : String :=
  let n' := if k == 0 then n else n ++ "_" ++ toString k
  if ok n' then n' else freshSuffix n ok (k + 1)

/-- Run `k` on the constructors of the presentation (`VCtor`): a nested argument that needs it
split through products and sums (`needsSplit`), its parts new local variables, a constructor per
way through the sums, unless that makes more than `maxSplit` constructors, when the arguments
through sums are kept. Arguments that do not split are kept: in a block, a nested argument at
several types that is not a product or a sum fails later, at its positions. The names of the
constructors of the presentation and of the parts are internal: those taken, by a constructor or
an argument, get a suffix (`freshSuffix`). -/
partial def withVCtors (holes : Array Expr) (k : Array VCtor → TermElabM α) : TermElabM α := do
  let rec go (m : Nat) (acc : Array VCtor) : TermElabM α := do
    if h : m < ctx.ctors.size then
      let c := ctx.ctors[m]
      let splits ← c.args.mapM fun a => do
        let e ← whnfOcc a.type
        return a.kind.isNest && (← ctx.needsSplit holes a.type) &&
          (e.isAppOfArity ``Prod 2 || e.isAppOfArity ``Sum 2)
      -- Through sums, at most `maxSplit` constructors of the presentation.
      let counts ← (c.args.zip splits).mapM fun (a, sp) =>
        if sp then ctx.splitCount holes a.type else pure 1
      let keepSums := counts.foldl (· * ·) 1 > maxSplit
      let rec args (i : Nat) (tpls : Array Tpl) : TermElabM α := do
        if h : i < c.args.size then
          let a := c.args[i]
          if splits[i]! && !(keepSums && counts[i]! > 1) then
            ctx.splitTpl holes a a.name a.type fun t => args (i + 1) (tpls.push t)
          else args (i + 1) (tpls.push (.part a))
        else
          let paths := tpls.foldl (init := #[((#[] : Array Bool), (#[] : Array ArgInfo))])
            fun ps t => ps.flatMap fun (c₁, a₁) => t.paths.map fun (c₂, a₂) => (c₁ ++ c₂, a₁ ++ a₂)
          -- The names of the parts, unlike those of the arguments.
          let paths := paths.map fun (choices, as) => Id.run do
            let mut out : Array ArgInfo := #[]
            for a in as do
              if c.args.any (·.fvar == a.fvar) then out := out.push a
              else
                let taken (n : String) : Bool :=
                  c.args.any (·.name.toString == n) || out.any (·.name.toString == n)
                let n := freshSuffix a.name.toString (!taken ·)
                out := out.push { a with name := Name.mkSimple n }
            return (choices, out)
          -- The names of the constructors through sums, unlike those of the type and the others.
          let mut vs : Array VCtor := #[]
          for (choices, as) in paths do
            let sfx := if choices.isEmpty then "" else
              "_" ++ "_".intercalate (choices.map (if · then "inl" else "inr")).toList
            let ok (s : String) : Bool := sfx.isEmpty || (
              !ctx.ctors.any (fun c' => c'.name.toString == c.name.toString ++ s ||
                c'.fname.toString == c.fname.toString ++ s) &&
              !(acc ++ vs).any fun v => v.ctor.name.toString == c.name.toString ++ s ||
                v.ctor.fname.toString == c.fname.toString ++ s)
            let sfx := freshSuffix sfx ok
            let ctor := { c with
              name := Name.mkSimple (c.name.toString ++ sfx)
              fname := Name.mkSimple (c.fname.toString ++ sfx), args := as }
            vs := vs.push { real := m, tpls, choices, ctor }
          go (m + 1) (acc ++ vs)
      args 0 #[]
    else k acc
  go 0 #[]

/-! ### The presentation: `S`, `P`, `B` -/

/-- The data arguments of the `m`-th constructor that are not at parameter positions, nor with
a structure in two variables. -/
def polyPlain (P : Poly) (m : Nat) : Array ArgInfo :=
  (P.vc[m]!.ctor.args.zipIdx.filter fun (a, k) =>
    a.kind.isData && !P.fields[m]!.any (·.k == k) && !(P.mixAt m).any (·.k == k)).map (·.1)

/-- Run `k` on the shape binders of the `m`-th constructor: those of its nested arguments, then
of its fields at parameter positions, then of its arguments with a structure in two variables.
-/
def withPolyShapes (P : Poly) (m : Nat) (bi : BinderInfo) (k : Array Expr → TermElabM α) :
    TermElabM α :=
  let c := P.vc[m]!.ctor
  ctx.withShapeBinders c bi fun nshs =>
    withLocalsN P.fields[m]!.size (fun j => do
      let f := P.fields[m]![j]!
      return (c.args[f.k]!.name.appendAfter "_s", bi, f.sh)) fun fshs =>
    withLocalsN (P.mixAt m).size (fun j => do
      let f := (P.mixAt m)[j]!
      return (c.args[f.k]!.name.appendAfter "_s", bi, f.sh)) fun mshs => k (nshs ++ fshs ++ mshs)

/-- `T.Poly.S.c psB plain shapes`. -/
def polySCtor (P : Poly) (m : Nat) (args : Array Expr) : MetaM Expr := do
  return mkAppN (← polyConst (ctx.polyName "S" ++ P.vc[m]!.ctor.fname)) (P.psB ++ args)

/-- `T.Poly.S psB`, `T.Poly.P psB s`, `T.Poly.B psB s`. -/
def polyS (P : Poly) : MetaM Expr := return mkAppN (← polyConst (ctx.polyName "S")) P.psB
def polyP (P : Poly) : MetaM Expr := return mkAppN (← polyConst (ctx.polyName "P")) P.psB
def polyB (P : Poly) : MetaM Expr := return mkAppN (← polyConst (ctx.polyName "B")) P.psB

/-- The name of the constructor of `P` (`B`) for the argument `a` of `c`. -/
def polyPos (s : String) (c : Ctor) (a : ArgInfo) : Name :=
  ctx.polyName s ++ Name.mkSimple (c.fname.toString ++ "_" ++ a.name.toString)

/-- Declare the inductive `name` with the parameters `psB` (the premises explicit, the parameters
of the type with the binder infos the user wrote) and the constructors `mkCtors I` over a local
variable `I` for it: a type `S` (`idx := false`) or a family over `S`; with indices, `S` is a
family over the index `P.I`, and so are the families over it. Its universe is inferred from the
constructors. -/
def polyInductive (P : Poly) (name : Name) (idx : Bool)
    (mkCtors : Expr → TermElabM (Array (Name × Expr))) : TermElabM Unit := do
  let psB := P.psB
  let declare (lvl : Level) : TermElabM Expr := do
    withBinderInfo (psB.filter (!P.consts.contains ·)) .default do
    let withI (k : Array Expr → TermElabM Expr) : TermElabM Expr :=
      if ctx.idxed then withLocalDeclD `i P.I fun i => k #[i] else k #[]
    withI fun is => do
      if idx then
        withLocalDeclD `s (mkAppN (← ctx.polyS P) is) fun s =>
          mkForallFVars (psB ++ is |>.push s) (mkSort lvl)
      else mkForallFVars (psB ++ is) (mkSort lvl)
  withLocalDeclD `I (← declare Level.one) fun Iv => do
  let cs ← mkCtors Iv
  let lvls ← cs.foldlM (init := #[]) fun acc (_, t) => forallTelescope t fun xs _ => do
    return acc ++ (← (xs.extract psB.size xs.size).mapM fun x => do getLevel (← inferType x))
  let ty ← declare (resultLevel lvls).succ
  let us ← ctx.levelParamsOf P.fresh (cs.map (·.2) |>.push ty)
  let Ic := Lean.mkConst name (us.map mkLevelParam)
  addInductive us psB.size [{
    name, type := ty
    ctors := cs.toList.map fun (n, t) => { name := n, type := t.replaceFVar Iv Ic } }] ctx.ref

/-- `T.Poly.S`, `T.Poly.P` (a position per field at a parameter position, with a position of its
structure), `T.Poly.B` (a position per recursive argument, as in `T.B`); an argument with a
structure in two variables has one of each, with a position of either kind of its structure. -/
def genPolyShapes (P : Poly) : TermElabM Unit := do
  let ms := Array.range P.vc.size
  -- With indices, the index of the presentation of the result of the `m`-th constructor.
  let cIdx (m : Nat) : MetaM (Array Expr) := do
    if ctx.idxed then return #[← ctx.polyIdx P P.vc[m]!.ctor.idx] else return #[]
  -- `S`: the data, the shapes of the nested arguments and of the fields.
  ctx.polyInductive P (ctx.polyName "S") false fun Sv => ms.mapM fun m =>
    ctx.withPolyShapes P m .default fun shs => do
      let plain := (polyPlain P m).map (·.fvar)
      let t ← withBinderInfo P.psB .implicit do
        mkForallFVars (P.psB ++ plain ++ shs) (mkAppN Sv (P.psB ++ (← cIdx m)))
      return (ctx.polyName "S" ++ P.vc[m]!.ctor.fname, t)
  -- A constructor of `P` or `B` for the `m`-th constructor: data and shapes implicit, `extra`.
  let posCtor (Iv : Expr) (m : Nat) (extra : Array Expr → (Array Expr → TermElabM Expr) →
      TermElabM Expr) : TermElabM Expr :=
    ctx.withPolyShapes P m .implicit fun shs => extra shs fun ys => do
      let plain := (polyPlain P m).map (·.fvar)
      withBinderInfo (P.psB ++ plain) .implicit do
        mkForallFVars (P.psB ++ plain ++ shs ++ ys)
          (mkApp (mkAppN Iv (P.psB ++ (← cIdx m))) (← ctx.polySCtor P m (plain ++ shs)))
  -- The constructor of `P` (`B`) for the `j`-th argument with a structure in two variables.
  let mixCtor (Iv : Expr) (m j : Nat) (s : String) : TermElabM (Name × Expr) := do
    let c := P.vc[m]!.ctor
    let f := (P.mixAt m)[j]!
    let i := c.nests.size + P.fields[m]!.size + j
    let t ← posCtor Iv m fun shs k =>
      withLocalDeclD `q (mkApp (if s == "P" then f.px else f.py) shs[i]!).headBeta fun q => k #[q]
    return (ctx.polyPos s c c.args[f.k]!, t)
  ctx.polyInductive P (ctx.polyName "P") true fun Iv => ms.flatMapM fun m => do
    let c := P.vc[m]!.ctor
    let nn := c.nests.size
    let fs ← (Array.range P.fields[m]!.size).mapM fun j => do
      let f := P.fields[m]![j]!
      let t ← posCtor Iv m fun shs k =>
        withLocalDeclD `q (mkApp f.pos shs[nn + j]!).headBeta fun q => k #[q]
      return (ctx.polyPos "P" c c.args[f.k]!, t)
    return fs ++ (← (Array.range (P.mixAt m).size).mapM fun j => mixCtor Iv m j "P")
  ctx.polyInductive P (ctx.polyName "B") true fun Iv => ms.flatMapM fun m => do
    let c := P.vc[m]!.ctor
    let rs ← c.recArgs.mapM fun a => do
      let t ← posCtor Iv m fun shs k => withPosArgs c a (shs.extract 0 c.nests.size) k
      return (ctx.polyPos "B" c a, t)
    return rs ++ (← (Array.range (P.mixAt m).size).mapM fun j => mixCtor Iv m j "B")

/-- The index of the child at a position, from the arguments `bargs` of its constructor in
`T.Poly.B` (the plain data, the shapes, the extra arguments), as `posIdx` for `T.B`. A field at a
parameter position occurs in no index (`refineHoles`). -/
def polyPosIdx (P : Poly) (m : Nat) (a : ArgInfo) (bargs : Array Expr) : MetaM Expr := do
  let c := P.vc[m]!.ctor
  let plain := polyPlain P m
  let np := plain.size
  let nsh := c.nests.size + P.fields[m]!.size + (P.mixAt m).size
  let σ (e : Expr) := e.replaceFVars (plain.map (·.fvar)) (bargs.extract 0 np)
  let extra := bargs.extract (np + nsh) bargs.size
  match a.kind with
  | .plain idx => ctx.polyIdx P (idx.map σ)
  | .fn _ =>
    let mut ty := σ a.type
    for y in extra do
      ty ← whnfR ty
      ty := ty.bindingBody!.instantiate1 y
    let some idx := ctx.holeOf? (← whnfOcc ty)
      | throwError "internal error: no occurrence at the end of{indentExpr ty}"
    ctx.polyIdx P idx
  | .nest n =>
    let some j := c.nests.findIdx? (·.1.fvar == a.fvar) | unreachable!
    let some pidx := n.pidx? | throwError "internal error: a nested argument without indices"
    return P.toPolyIdx (mkApp2 (σ pidx) bargs[np + j]! extra[0]!).headBeta
  | .data => throwError "internal error: a data argument has no position"

/-- The index of the child at a position in `Y` of the `j`-th argument with a structure in two
variables of the `m`-th constructor, from the arguments `bargs` of its constructor in `T.Poly.B`
(the plain data, the shapes, the position of the structure): the index of that position. -/
def polyMixIdx (P : Poly) (m j : Nat) (bargs : Array Expr) : MetaM Expr := do
  let c := P.vc[m]!.ctor
  let f := (P.mixAt m)[j]!
  let plain := polyPlain P m
  let np := plain.size
  let some pidx := f.pidx?
    | throwError "internal error: a structure in two variables without indices"
  let σ (e : Expr) := e.replaceFVars (plain.map (·.fvar)) (bargs.extract 0 np)
  let i := np + c.nests.size + P.fields[m]!.size + j
  return (mkApp2 (σ pidx) bargs[i]! bargs.back!).headBeta

/-- With indices, `T.Poly.idx`, the index of the child at a position, by cases. -/
def genPolyIdx (P : Poly) : TermElabM Unit := do
  let B ← ctx.polyB P
  withLocalDecl `i .implicit P.I fun i => do
  withLocalDecl `s .implicit (mkApp (← ctx.polyS P) i) fun s => do
  withLocalDeclD `b (mkApp2 B i s) fun b => do
  let args := P.psB ++ #[i, s]
  let Bn := ctx.polyName "B"
  let value ← mkCasesOnApp Bn B.getAppFn.constLevels! args b (← getLevel P.I)
    (fun _ _ => pure P.I) fun cname xs => do
      -- An argument with a structure in two variables: the index of its position in `Y`.
      let mix? := (Array.range P.vc.size).findSome? fun m =>
        let c := P.vc[m]!.ctor
        ((P.mixAt m).findIdx? (ctx.polyPos "B" c c.args[·.k]! == cname)).map (m, ·)
      if let some (m, j) := mix? then
        let nargs ← ctx.withPolyShapes P m .implicit fun shs =>
          pure ((polyPlain P m).size + shs.size + 1)
        return ← polyMixIdx P m j (← ctorArgsOf Bn P.psB.size args xs nargs)
      let some (m, a) := (Array.range P.vc.size).findSome? fun m =>
          let c := P.vc[m]!.ctor
          (c.recArgs.find? (ctx.polyPos "B" c · == cname)).map (m, ·)
        | throwError "internal error: unexpected constructor {cname}"
      let c := P.vc[m]!.ctor
      let nargs ← ctx.withPolyShapes P m .implicit fun shs =>
        withPosArgs c a (shs.extract 0 c.nests.size) fun ys =>
          pure ((polyPlain P m).size + shs.size + ys.size)
      ctx.polyPosIdx P m a (← ctorArgsOf Bn P.psB.size args xs nargs)
  let xs := P.psB ++ #[i, s, b]
  let (type, value) ← withBinderInfo P.psB .implicit do
    return (← mkForallFVars xs P.I, ← mkLambdaFVars xs value)
  addDef (ctx.polyName "idx") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref

/-- `T.Poly.sig psB`, the signature of the presentation: the index `P.I`, `S`, `B` and `idx`. -/
def polySig (P : Poly) : MetaM Expr :=
  return mkAppN (← polyConst (ctx.polyName "sig")) P.psB

/-- With indices, `T.Poly.sig`, reducible as `T.sig`. -/
def genPolySig (P : Poly) : TermElabM Unit := do
  let S ← ctx.polyS P
  let B ← ctx.polyB P
  let rS ← withLocalDeclD `i P.I fun i => do typeLevel (mkApp S i)
  let rB ← withLocalDeclD `i P.I fun i => withLocalDeclD `s (mkApp S i) fun s => do
    typeLevel (mkApp2 B i s)
  let idxFn ← lam `i P.I (bi := .implicit) fun i => lam `s (mkApp S i) (bi := .implicit) fun s =>
    lam `b (mkApp2 B i s) fun b => do
      return mkAppN (← polyConst (ctx.polyName "idx")) (P.psB ++ #[i, s, b])
  let value := mkApp4 (.const ``Codata.Signature.mk [← typeLevel P.I, rS, rB]) P.I S B idxFn
  let type ← inferType value
  let (type, value) ← withBinderInfo (P.psB.filter (!P.consts.contains ·)) .default do
    return (← mkForallFVars P.psB type, ← mkLambdaFVars P.psB value)
  addDef (ctx.polyName "sig") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref
    (reducible := true)

/-! ### The layer: `toL`, `ofL` and their laws -/

/-- `T.F (H X) Y`, at the universe `w` of `Y`. -/
def polyF (P : Poly) (X Y : Expr) (w : Level) : MetaM Expr := do
  return mkAppN (← ctx.constWith ctx.F [w]) (ctx.polyParams P P.Hs X |>.push Y)

/-- `Lay (T.Poly.P psB) (T.Poly.B psB) X Y`. -/
def polyLay (P : Poly) (X Y : Expr) : MetaM Expr := do
  mkAppOptM ``Codata.Lay #[none, ← ctx.polyP P, ← ctx.polyB P, X, Y]

/-- With indices, the type of the family `Y` that `T.F (H X)` takes: `∀ j₁ j₂, Type w`, or
`Blk.Ix (H X) → Type w`. -/
def polyYTy (P : Poly) (Hs : Array Expr) (X : Expr) (w : Level) : TermElabM Expr := do
  return P.subX Hs X (← ctx.famType w)

/-- The family of the children of a layer, on the index of the presentation, from the family `Y`
that `T.F` takes: `fun j => Y (ι j)`, curried; `Y` itself for one index. -/
def polyLayFam (P : Poly) (Hs : Array Expr) (X Y : Expr) : TermElabM Expr := do
  if !ctx.isBlock && ctx.k == 1 then return Y
  lam `j P.I fun j => do return mkAppN Y (← ctx.projs (← ctx.polyIota P Hs X j))

/-- `ILay (T.Poly.sig psB) (T.Poly.P psB) X (fun j => Y (ι j)) i`. -/
def polyILay (P : Poly) (X Y i : Expr) : TermElabM Expr := do
  mkAppOptM ``Codata.ILay
    #[← ctx.polySig P, ← ctx.polyP P, X, ← ctx.polyLayFam P P.Hs X Y, i]

/-- `T.F (H X) Y (ι i)` at the index `i` of the presentation, at the universe `w` of `Y`. -/
def polyFI (P : Poly) (X Y i : Expr) (w : Level) : TermElabM Expr := do
  return mkAppN (← ctx.polyF P X Y w) (← ctx.projs (← ctx.polyIota P P.Hs X i))

/-- `T.Poly.idx psB i s b`, the index of the child at `b`. -/
def polyIdxAt (P : Poly) (i s b : Expr) : MetaM Expr := do
  return mkAppN (← polyConst (ctx.polyName "idx")) (P.psB ++ #[i, s, b])

/-- `(b : T.Poly.B psB i s) → Y (ι (T.Poly.idx b))`, the children of a layer at `i` and `s`. -/
def polyKidsTy (P : Poly) (X Y i s : Expr) : TermElabM Expr := do
  let layY ← ctx.polyLayFam P P.Hs X Y
  withLocalDeclD `b (mkApp2 (← ctx.polyB P) i s) fun b => do
    mkForallFVars #[b] (mkApp layY (← ctx.polyIdxAt P i s b)).headBeta

/-- `Occ.ofC o ⟨sh, fun q => snd q⟩` for a plain structure, the structure of a field at a
parameter position, also when the type has indices. -/
def mkOfCPlain (o hole sh : Expr) (snd : Expr → TermElabM Expr) : TermElabM Expr :=
  ({ ctx with idx := #[] } : Ctx).mkOfC o hole sh snd

/-- `T.Poly.toL premises X Y a` (`ofL`, …): a declaration of this step over the premises, at
the universes `y` of `Y` (and `y'`) given by `σ`. -/
def polyAt (P : Poly) (s : String) (σ : List (Name × Level)) (args : Array Expr) : MetaM Expr := do
  return mkAppN (← polyConst (ctx.polyName s) σ) (P.premises ++ args)

/-- The substitution of the arguments of `c` by `ys`, and of the holes by `Hᵢ X`. -/
def polySubst (P : Poly) (c : Ctor) (ys : Array Expr) (X : Expr) (e : Expr) : Expr :=
  (e.replaceFVars c.fvars ys).replaceFVars P.holes (P.Hs.map (mkApp · X))

/-- The structure in two variables of `f`, its occurrences at `lvl`, under the substitution `σ`.
-/
def mixOccAt (f : MixField) (lvl : Level) (σ : Expr → Expr) : Expr :=
  substLevel ctx.uT lvl (σ f.occ)

/-- `Occ₂.toC o y`, at `X` and `Y`; for an indexed structure (`IOcc₂`) `IOcc₂.toC o y`, at `X`
and the family `Y` over the index of the presentation. -/
def toC₂ (o X Y y : Expr) : MetaM Expr := do
  if (← whnfR (← inferType o)).isAppOf ``Codata.IOcc₂ then
    return ← mkAppOptM ``Codata.IOcc₂.toC #[none, none, none, none, none, none, o, X, Y, y]
  mkAppOptM ``Codata.Occ₂.toC #[none, none, none, none, o, X, Y, y]

/-- `Occ₂.ofC o ⟨sh, fun q => c q, fun q => d q⟩`, at `X` and `Y`; for an indexed structure
`IOcc₂.ofC`, at `X` and the family `Y`. -/
def mkOfC₂ (o X Y sh : Expr) (c d : Expr → TermElabM Expr) : TermElabM Expr := do
  let f ← if (← whnfR (← inferType o)).isAppOf ``Codata.IOcc₂ then
      mkAppOptM ``Codata.IOcc₂.ofC #[none, none, none, none, none, none, o, X, Y]
    else mkAppOptM ``Codata.Occ₂.ofC #[none, none, none, none, o, X, Y]
  let D ← whnf (← whnf (← inferType f)).bindingDomain!
  unless D.isAppOfArity ``Sigma 2 do
    throwError "internal error: expected a layer, got{indentExpr D}"
  let (α, β) := (D.appFn!.appArg!, D.appArg!)
  let pr ← whnf (mkApp β sh).headBeta
  let (A, B) := (pr.appFn!.appArg!, pr.appArg!)
  let fn (T : Expr) (k : Expr → TermElabM Expr) : TermElabM Expr := do
    withLocalDeclD `q (← whnf T).bindingDomain!.headBeta fun q => do mkLambdaFVars #[q] (← k q)
  let p ← mkAppOptM ``Prod.mk #[A, B, ← fn A c, ← fn B d]
  return mkApp f (mkApp4 (.const ``Sigma.mk D.getAppFn.constLevels!) α β sh p)

/-- The layer of `F.c ys` (`toL`): `(fun z… => ⟨S.c data z.1…, positions, children⟩) (toC o x)…`.
-/
def polyLayer (P : Poly) (m : Nat) (X Y : Expr) (ys : Array Expr) : TermElabM Expr := do
  let c := P.vc[m]!.ctor
  let fs := P.fields[m]!
  let σ := polySubst P c ys X
  let toC (o hole y : Expr) : MetaM Expr :=
    mkAppOptM ``Codata.Occ.toC #[none, none, none, o, hole, y]
  -- With indices, the structure of a nested argument is indexed, at `Y` on the packed index.
  let nestToC (o y : Expr) : TermElabM Expr := do
    if !ctx.idxed then return ← toC o Y y
    mkAppOptM ``Codata.IOcc.toC
      #[none, none, none, none, none, o, P.subX P.Hs X (← ctx.packFam Y), y]
  let ms := P.mixAt m
  -- The family of a structure in two variables: with indices, on the index of the presentation.
  let Yfam ← if ctx.idxed then ctx.polyLayFam P P.Hs X Y else pure Y
  let toCs := (← c.nests.mapM fun (a, n) => do
      let some k := c.args.findIdx? (·.fvar == a.fvar) | unreachable!
      nestToC (ctx.nestAt n P.ly σ) ys[k]!) ++
    (← fs.mapM fun f => toC (σ f.occ) X ys[f.k]!) ++
    (← ms.mapM fun f => toC₂ (ctx.mixOccAt f P.ly σ) X Yfam ys[f.k]!)
  let names := c.nests.map (·.1.name) ++ fs.map (c.args[·.k]!.name) ++ ms.map (c.args[·.k]!.name)
  withLocalsN toCs.size (fun j => return (names[j]!.appendBefore "z_", .default,
      ← inferType toCs[j]!)) fun zs => do
  let plain := (c.args.zip ys).filterMap fun (a, y) =>
    if a.kind.isData && !fs.any (c.args[·.k]!.fvar == a.fvar) &&
      !ms.any (c.args[·.k]!.fvar == a.fvar) then some y else none
  -- The contents of the `j`-th argument with a structure in two variables: `fst` in `X`.
  let mixPart (sg : CasesSubgoal) (j : Nat) (fst : Bool) : TermElabM Expr := do
    let w ← mkAppM ``Sigma.snd #[sg.subst.apply zs[c.nests.size + fs.size + j]!]
    return mkApp (← mkAppM (if fst then ``Prod.fst else ``Prod.snd) #[w]) sg.fields.back!
  let shape ← ctx.polySCtor P m (plain ++ (← zs.mapM fun z => mkAppM ``Sigma.fst #[z]))
  -- With indices, the index of the layer (translated before the substitution, which changes the
  -- parameters of the block's index).
  let i? ← if ctx.idxed then some <$> σ <$> ctx.polyIdx P c.idx else pure none
  let atIdx (fam : Expr) : Expr := match i? with
    | some i => mkApp fam i
    | none => fam
  -- The positions and the children, by cases (in general position with indices).
  let byCases (ty : Expr) (val : Name → CasesSubgoal → TermElabM Expr) : TermElabM Expr := do
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (b, g') ← g.mvarId!.intro1
    for sg in ← if ctx.idxed then casesPos g' b else g'.cases b do
      let some n := sg.ctorName | throwError "internal error: no constructor"
      let v ← val n sg
      sg.mvarId.withContext do
        unless ← isDefEq (← sg.mvarId.getType) (← inferType v) do
          throwError "internal error: ill-typed position{indentExpr v}"
        sg.mvarId.assign v
    instantiateMVars g
  let pf ← byCases (← mkArrow (mkApp (atIdx (← ctx.polyP P)) shape) X) fun n sg => do
    if let some j := ms.findIdx? fun f => n == ctx.polyPos "P" c c.args[f.k]! then
      return ← mixPart sg j true
    let some j := fs.findIdx? fun f => n == ctx.polyPos "P" c c.args[f.k]!
      | throwError "internal error: unexpected position {n}"
    return mkApp (← mkAppM ``Sigma.snd #[sg.subst.apply zs[c.nests.size + j]!]) sg.fields.back!
  let bTy ← match i? with
    | some i => ctx.polyKidsTy P X Y i shape
    | none => mkArrow (mkApp (← ctx.polyB P) shape) Y
  let bf ← byCases bTy fun n sg => do
    if let some j := ms.findIdx? fun f => n == ctx.polyPos "B" c c.args[f.k]! then
      return ← mixPart sg j false
    let some k := c.args.findIdx? fun a => !a.kind.isData && n == ctx.polyPos "B" c a
      | throwError "internal error: unexpected position {n}"
    let a := c.args[k]!
    match a.kind with
    | .nest _ =>
      let some j := c.nests.findIdx? (·.1.fvar == a.fvar) | unreachable!
      let v := mkApp (← mkAppM ``Sigma.snd #[sg.subst.apply zs[j]!]) sg.fields.back!
      -- In a block, the child's index must be the block's index of the presentation's.
      if ctx.isBlock then
        let ok ← sg.mvarId.withContext do isDefEq (← sg.mvarId.getType) (← inferType v)
        unless ok do
          throwLimit m!"the positions of the nested argument `{a.name}` of `{c.name}` are at a \
            type of the block only after cases on them, as through a product or a sum inside a \
            named type constructor, which is not supported for the types of a block"
      return v
    | .fn n => return mkAppN (sg.subst.apply ys[k]!) (sg.fields.extract (sg.fields.size - n))
    | _ => return sg.subst.apply ys[k]!
  let lay ← match i? with
    | some i =>
      let layTy ← whnfR (← ctx.polyILay P X Y i)
      mkAppOptM ``Sigma.mk
        #[layTy.appFn!.appArg!, layTy.appArg!, shape, ← mkAppM ``Prod.mk #[pf, bf]]
    | none =>
      let β ← lam `s (← ctx.polyS P) fun s => do
        mkAppM ``Prod
          #[← mkArrow (mkApp (← ctx.polyP P) s) X, ← mkArrow (mkApp (← ctx.polyB P) s) Y]
      mkAppOptM ``Sigma.mk #[← ctx.polyS P, β, shape, ← mkAppM ``Prod.mk #[pf, bf]]
  return mkAppN (← mkLambdaFVars zs lay) toCs

/-- The value of an argument with template `t` and type `D` (of `F.c` or `T.c`, read through
`whnfOcc`) from the values of the parts on the way through it, `valOf vi D'` for the `vi`-th
argument of the presentation, at its type `D'`: pairs and injections. Returns the next `vi` and
the next position in the alternatives `choices`. -/
partial def buildArg (choices : Array Bool) (valOf : Nat → Expr → TermElabM Expr) :
    Tpl → Expr → Nat → Nat → TermElabM (Expr × Nat × Nat)
  | .part _, D, vi, ci => do return (← valOf vi D, vi + 1, ci)
  | .prod l r, D, vi, ci => do
    let D ← whnfOcc D
    let (A, B) := (D.appFn!.appArg!, D.appArg!)
    let (x, vi, ci) ← buildArg choices valOf l A vi ci
    let (y, vi, ci) ← buildArg choices valOf r B vi ci
    return (← mkAppOptM ``Prod.mk #[A, B, x, y], vi, ci)
  | .sum l r _ _, D, vi, ci => do
    let D ← whnfOcc D
    let (A, B) := (D.appFn!.appArg!, D.appArg!)
    if choices[ci]! then
      let (x, vi, ci) ← buildArg choices valOf l A vi (ci + 1)
      return (← mkAppOptM ``Sum.inl #[A, B, x], vi, ci)
    else
      let (x, vi, ci) ← buildArg choices valOf r B vi (ci + 1)
      return (← mkAppOptM ``Sum.inr #[A, B, x], vi, ci)

/-- The constructor `fn`, a function of the arguments of the real constructor of `v`, applied to
the values of the arguments of `v` (`valOf vi D`, at the type `D` of the part): each argument
built from its parts (`buildArg`). -/
def applyVCtor (v : VCtor) (fn : Expr) (valOf : Nat → Expr → TermElabM Expr) :
    TermElabM Expr := do
  let mut fn := fn
  let mut ty ← inferType fn
  let mut vi := 0
  let mut ci := 0
  for t in v.tpls do
    ty ← whnf ty
    let (val, vi', ci') ← buildArg v.choices valOf t ty.bindingDomain! vi ci
    vi := vi'
    ci := ci'
    fn := mkApp fn val
    ty := ty.bindingBody!.instantiate1 val
  return fn

/-- `F.c (H X) Y args` from the shape arguments `sargs` of `S.c` and the contents `v`, `k` of a
layer (`ofL`): a field at a parameter position is `Occ.ofC o ⟨x_s, fun q => v (P.c_x q)⟩`, a
recursive argument `k (B.c_y)`, under its telescope or through its structure, an argument with a
structure in two variables `Occ₂.ofC o ⟨p_s, fun q => v (P.c_p q), fun q => k (B.c_p q)⟩`; a
split argument the pair or injection of its parts. -/
def polyOfLBody (P : Poly) (m : Nat) (X Y v k : Expr) (sargs : Array Expr) :
    TermElabM Expr := do
  let vc := P.vc[m]!
  let c := vc.ctor
  let fs := P.fields[m]!
  let plainArgs := polyPlain P m
  let np := plainArgs.size
  let shs := sargs.extract np sargs.size
  let σd (e : Expr) : Expr :=
    (e.replaceFVars (plainArgs.map (·.fvar)) (sargs.extract 0 np)).replaceFVars P.holes
      (P.Hs.map (mkApp · X))
  let posApp (s : String) (a : ArgInfo) (extra : Array Expr) : MetaM Expr := do
    return mkAppN (← polyConst (ctx.polyPos s c a)) (P.psB ++ sargs ++ extra)
  -- The occurrences of the nested structures: `Y`, or with indices `Y` on the packed index; of
  -- the structures in two variables `Y`, or with indices on the index of the presentation.
  let hole ← if ctx.idxed then pure (P.subX P.Hs X (← ctx.packFam Y)) else pure Y
  let Yfam ← if ctx.idxed then ctx.polyLayFam P P.Hs X Y else pure Y
  let valOf (i : Nat) (D : Expr) : TermElabM Expr := do
    let a := c.args[i]!
    match a.kind with
    | .data =>
      if let some j := fs.findIdx? (·.k == i) then
        ctx.mkOfCPlain (σd fs[j]!.occ) X shs[c.nests.size + j]! fun q => do
          return mkApp v (← posApp "P" a #[q])
      else if let some j := (P.mixAt m).findIdx? (·.k == i) then
        mkOfC₂ (ctx.mixOccAt (P.mixAt m)[j]! P.ly σd) X Yfam shs[c.nests.size + fs.size + j]!
          (fun q => do return mkApp v (← posApp "P" a #[q]))
          (fun q => do return mkApp k (← posApp "B" a #[q]))
      else
        let some di := plainArgs.findIdx? (·.fvar == a.fvar) | unreachable!
        pure sargs[di]!
    | .plain _ => pure (mkApp k (← posApp "B" a #[]))
    | .fn n => withTele n D fun zs _ => do
      mkLambdaFVars zs (mkApp k (← posApp "B" a zs))
    | .nest n =>
      let some j := c.nests.findIdx? (·.1.fvar == a.fvar) | unreachable!
      ctx.mkOfC (substLevel ctx.uT P.ly (σd n.occ)) hole shs[j]! fun q => do
        return mkApp k (← posApp "B" a #[q])
  let cr := ctx.ctors[vc.real]!
  applyVCtor vc (mkAppN (← ctx.constWith (ctx.fCtor cr) [P.ly])
    (ctx.polyParams P P.Hs X |>.push Y)) valOf

/-- The term `k vi vs` at the constructor `vi` of the presentation of the `mr`-th constructor
with arguments `ys`, `vs` its arguments: through a product the projections, through a sum
`Sum.casesOn`, at the type of the term, which must not depend on the alternative. -/
partial def polyDispatch (P : Poly) (mr : Nat) (ys : Array Expr)
    (k : Nat → Array Expr → TermElabM Expr) : TermElabM Expr := do
  let some v := P.vc.find? (·.real == mr) | throwError "internal error: no constructor {mr}"
  let rec go : List (Tpl × Expr) → Array Bool → Array Expr → TermElabM Expr
    | [], cs, vs => do
      let some vi := P.vc.findIdx? fun v => v.real == mr && v.choices == cs
        | throwError "internal error: no constructor of the presentation"
      k vi vs
    | (.part _, y) :: rest, cs, vs => go rest cs (vs.push y)
    | (.prod l r, y) :: rest, cs, vs => do
      go ((l, ← mkAppM ``Prod.fst #[y]) :: (r, ← mkAppM ``Prod.snd #[y]) :: rest) cs vs
    | (.sum l r _ _, y) :: rest, cs, vs => do
      let D ← whnfOcc (← inferType y)
      let (A, B) := (D.appFn!.appArg!, D.appArg!)
      let lb ← withLocalDeclD `a A fun a => do
        mkLambdaFVars #[a] (← go ((l, a) :: rest) (cs.push true) vs)
      let rb ← withLocalDeclD `b B fun b => do
        mkLambdaFVars #[b] (← go ((r, b) :: rest) (cs.push false) vs)
      let mty ← withLocalDeclD `a A fun a => do inferType (mkApp lb a).headBeta
      let motive ← withLocalDeclD `t D fun t => mkLambdaFVars #[t] mty
      mkAppOptM ``Sum.casesOn #[A, B, motive, y, lb, rb]
  go (v.tpls.toList.zip ys.toList) #[] #[]

/-- Split the arguments `ys` of the `mr`-th constructor, in the goal `g`, along their templates:
`cases` on the local variables of the products and sums. The goals, each with its constructor of
the presentation and the values of its arguments. -/
partial def polyDestructure (P : Poly) (mr : Nat) (g : MVarId) (ys : Array Expr) :
    MetaM (Array (MVarId × Nat × Array Expr)) := do
  let some v := P.vc.find? (·.real == mr) | throwError "internal error: no constructor {mr}"
  let rec go : MVarId → List (Tpl × Expr) → Array Bool → Array Expr →
      MetaM (Array (MVarId × Nat × Array Expr))
    | g, [], cs, vs => do
      let some vi := P.vc.findIdx? fun v => v.real == mr && v.choices == cs
        | throwError "internal error: no constructor of the presentation"
      return #[(g, vi, vs)]
    | g, (.part _, y) :: rest, cs, vs => go g rest cs (vs.push y)
    | g, (t, y) :: rest, cs, vs => do
      let sgs ← g.cases y.fvarId!
      let sub (sg : CasesSubgoal) (e : Expr) : Expr := sg.subst.apply e
      match t, sgs with
      | .prod l r, #[sg] =>
        go sg.mvarId ((l, sg.fields[0]!) :: (r, sg.fields[1]!) ::
          rest.map fun (t, e) => (t, sub sg e)) cs (vs.map (sub sg))
      | .sum l r _ _, #[sl, sr] =>
        return (← go sl.mvarId ((l, sl.fields[0]!) :: rest.map fun (t, e) => (t, sub sl e))
            (cs.push true) (vs.map (sub sl))) ++
          (← go sr.mvarId ((r, sr.fields[0]!) :: rest.map fun (t, e) => (t, sub sr e))
            (cs.push false) (vs.map (sub sr)))
      | _, _ => throwError "internal error: cases on a split argument"
  go g (v.tpls.toList.zip ys.toList) #[] #[]

/-- The type `T.F (H X) Y idx…` of `a` once the index of the presentation is split into its
components: the indices reduced, `⟨i₁, i₂⟩.1` to `i₁`, in a block `ι (Blk.Poly.Ix.Tₘ idx)` to
`Blk.Ix.Tₘ idx`, so that cases on `a` see them. -/
def polyWhnfIdx (ty : Expr) : MetaM Expr := do
  let np := ctx.params.size + 1
  let args ← ty.getAppArgs.mapIdxM fun k e => if k < np then pure e else whnf e
  return mkAppN ty.getAppFn args

/-- `toL` in a block, on the goal `g : ILay … i` with `a : Blk.F (H X) Y (ι i)`: by cases on the
index `i`, then on `a`, whose index `ι i` is then `Blk.Ix.Tₘ idx`, which drops the constructors of
the other types and solves the equations of the indices (the `idx` are variables). -/
def polyToLBlock (P : Poly) (X Y : Expr) (g : MVarId) (i : FVarId) : TermElabM Unit := do
  for sg in ← g.cases i do
    sg.mvarId.withContext do
    let some a := (← getLCtx).lastDecl | throwError "internal error: no layer to destructure"
    let g ← sg.mvarId.replaceLocalDeclDefEq a.fvarId (← ctx.polyWhnfIdx (← instantiateMVars a.type))
    for sg in ← g.cases a.fvarId do
      sg.mvarId.withContext do
      let some m := ctx.ctors.findIdx? fun c => sg.ctorName == some (ctx.fCtor c)
        | throwError "internal error: unexpected case {sg.ctorName}"
      let v ← polyDispatch P m sg.fields fun vi vs => ctx.polyLayer P vi X Y vs
      unless ← isDefEq (← sg.mvarId.getType) (← inferType v) do
        throwError "internal error: ill-typed layer{indentExpr v}"
      sg.mvarId.assign v

/-- With indices, `T.Poly.toL` and `T.Poly.ofL` at an index `i` of the presentation, between
`T.F (H X) Y (ι i)` and the layer at `i`. `toL` is by cases on `F` (in a block `polyToLBlock`),
`ofL` by cases on the shape. -/
def genIPolyLayer (P : Poly) : TermElabM Unit := do
  let close (xs : Array Expr) (type value : Expr) : TermElabM (Expr × Expr) :=
    withBinderInfo (P.consts ++ P.SR) .implicit do
      return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  withLocalDecl `X .implicit (mkSort P.lx.succ) fun X => do
  withLocalDecl `Y .implicit (← ctx.polyYTy P P.Hs X P.ly) fun Y => do
  withLocalDecl `i .implicit P.I fun i => do
  let FXY ← ctx.polyFI P X Y i P.ly
  let lay ← ctx.polyILay P X Y i
  -- `toL`
  withLocalDeclD `a FXY fun a => do
    let value ← if ctx.isBlock then do
        let g ← mkFreshExprSyntheticOpaqueMVar lay
        ctx.polyToLBlock P X Y g.mvarId! i.fvarId!
        instantiateMVars g
      else do
        let np := ctx.params.size + 1
        mkCasesOnApp ctx.F (← ctx.levelsWith ctx.F [P.ly]) FXY.getAppArgs a (← getLevel lay)
          (fun is _ => do
            ctx.polyILay P X Y (← ctx.pack (← fullIdx ctx.F np FXY.getAppArgs is)))
          fun cname xs => do
            let some m := ctx.ctors.findIdx? (ctx.fCtor · == cname)
              | throwError "internal error: unexpected constructor {cname}"
            polyDispatch P m
              (← ctorArgsOf ctx.F np FXY.getAppArgs xs ctx.ctors[m]!.args.size)
              fun vi vs => ctx.polyLayer P vi X Y vs
    let (type, value) ← close (P.premises ++ #[X, Y, i, a]) lay value
    addDef (ctx.polyName "toL") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref
  -- `ofL`
  withLocalDeclD `z lay fun z => do
    let S ← ctx.polyS P
    let Sn := ctx.polyName "S"
    let s ← mkAppM ``Sigma.fst #[z]
    let w ← mkAppM ``Sigma.snd #[z]
    let motive (j s : Expr) : TermElabM Expr := do
      mkArrow (← mkArrow (mkApp2 (← ctx.polyP P) j s) X)
        (← mkArrow (← ctx.polyKidsTy P X Y j s) (← ctx.polyFI P X Y j P.ly))
    let args := P.psB.push i
    let value ← mkCasesOnApp Sn S.getAppFn.constLevels! args s (← getLevel (← motive i s))
      (fun is s => do motive (← fullIdx Sn P.psB.size args is)[0]! s) fun cname xs => do
        let some m := P.vc.findIdx? (Sn ++ ·.ctor.fname == cname)
          | throwError "internal error: unexpected constructor {cname}"
        let nsh := P.vc[m]!.ctor.nests.size + P.fields[m]!.size + (P.mixAt m).size
        let sargs ← ctorArgsOf Sn P.psB.size args xs ((polyPlain P m).size + nsh)
        let shape := mkAppN (← polyConst cname) (P.psB ++ sargs)
        let j := (← whnf (← inferType shape)).appArg!
        lam `v (← mkArrow (mkApp2 (← ctx.polyP P) j shape) X) fun v => do
          lam `k (← ctx.polyKidsTy P X Y j shape) fun k =>
            ctx.polyOfLBody P m X Y v k sargs
    let value := mkApp2 value (← mkAppM ``Prod.fst #[w]) (← mkAppM ``Prod.snd #[w])
    let (type, value) ← close (P.premises ++ #[X, Y, i, z]) FXY value
    addDef (ctx.polyName "ofL") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref

/-- `T.Poly.toL` and `T.Poly.ofL`. -/
def genPolyLayer (P : Poly) : TermElabM Unit := do
  if ctx.idxed then return ← ctx.genIPolyLayer P
  let close (xs : Array Expr) (type value : Expr) : TermElabM (Expr × Expr) :=
    withBinderInfo (P.consts ++ P.SR) .implicit do
      return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  withLocalDecl `X .implicit (mkSort P.lx.succ) fun X => do
  withLocalDecl `Y .implicit (mkSort P.ly.succ) fun Y => do
  let FXY ← ctx.polyF P X Y P.ly
  let lay ← ctx.polyLay P X Y
  -- `toL`, by cases on `F`.
  withLocalDeclD `a FXY fun a => do
    let np := ctx.params.size + 1
    let value ← mkCasesOnApp ctx.F (← ctx.levelsWith ctx.F [P.ly]) FXY.getAppArgs a
      (← getLevel lay) (fun _ _ => pure lay) fun cname xs => do
        let some m := ctx.ctors.findIdx? (ctx.fCtor · == cname)
          | throwError "internal error: unexpected constructor {cname}"
        polyDispatch P m (← ctorArgsOf ctx.F np FXY.getAppArgs xs ctx.ctors[m]!.args.size)
          fun vi vs => ctx.polyLayer P vi X Y vs
    let (type, value) ← close (P.premises ++ #[X, Y, a]) lay value
    addDef (ctx.polyName "toL") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref
  -- `ofL`, by cases on the shape.
  withLocalDeclD `z lay fun z => do
    let S ← ctx.polyS P
    let s ← mkAppM ``Sigma.fst #[z]
    let w ← mkAppM ``Sigma.snd #[z]
    let motive (s : Expr) : TermElabM Expr := do
      mkArrow (← mkArrow (mkApp (← ctx.polyP P) s) X)
        (← mkArrow (← mkArrow (mkApp (← ctx.polyB P) s) Y) FXY)
    let value ← mkCasesOnApp (ctx.polyName "S") (S.getAppFn.constLevels!) P.psB s
      (← getLevel (← motive s)) (fun _ s => motive s) fun cname xs => do
        let some m := P.vc.findIdx? (ctx.polyName "S" ++ ·.ctor.fname == cname)
          | throwError "internal error: unexpected constructor {cname}"
        let shape := mkAppN (mkAppN (.const cname S.getAppFn.constLevels!) P.psB) xs
        lam `v (← mkArrow (mkApp (← ctx.polyP P) shape) X) fun v => do
          lam `k (← mkArrow (mkApp (← ctx.polyB P) shape) Y) fun k =>
            ctx.polyOfLBody P m X Y v k xs
    let value := mkApp2 value (← mkAppM ``Prod.fst #[w]) (← mkAppM ``Prod.snd #[w])
    let (type, value) ← close (P.premises ++ #[X, Y, z]) FXY value
    addDef (ctx.polyName "ofL") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref

/-- Destructure a layer `z = ⟨s, v, k⟩` and run `k` on each case of the shape, with its
constructor. -/
def polyCasesLay (P : Poly) (g : MVarId) (z : Expr) (k : Nat → MVarId → TermElabM Unit)
    (i? : Option Expr := none) : TermElabM Unit := do
  let #[sg] ← g.cases z.fvarId! | throwError "internal error: cases on a layer"
  let #[sg'] ← sg.mvarId.cases sg.fields[1]!.fvarId! | throwError "internal error: cases on a pair"
  let s := sg'.subst.apply sg.fields[0]!
  -- With indices, the shape is at the variable `i`, which the cases instantiate.
  let S ← match i? with
    | some i => pure (mkApp (← ctx.polyS P) (sg'.subst.apply (sg.subst.apply i)))
    | none => ctx.polyS P
  let g ← sg'.mvarId.withContext do sg'.mvarId.replaceLocalDeclDefEq s.fvarId! S
  for sg in ← g.cases s.fvarId! do
    let some m := P.vc.findIdx? fun v => sg.ctorName == some (ctx.polyName "S" ++ v.ctor.fname)
      | throwError "internal error: unexpected shape {sg.ctorName}"
    k m sg.mvarId

/-- Split the index `i` of the presentation into its components by cases, for cases on
`a : T.F (H X) Y (ι i)`: nothing for one index, the dependent pairs for several, in a block the
type and its indices. Returns the goals with `a`, its type at the components (`polyWhnfIdx`). -/
def polyCasesIdx (g : MVarId) (i a : FVarId) : MetaM (Array (MVarId × FVarId)) := do
  if !ctx.isBlock && ctx.k == 1 then return #[(g, a)]
  let rec split (g : MVarId) (i : FVarId) : Nat → MetaM (Array MVarId)
    | n + 1 => do
      let sgs ← g.cases i
      if ctx.isBlock || n ≤ 1 then return sgs.map (·.mvarId)
      sgs.flatMapM fun sg => split sg.mvarId sg.fields.back!.fvarId! n
    | 0 => return #[g]
  (← split g i ctx.k).mapM fun g => g.withContext do
    let some a := (← getLCtx).lastDecl | throwError "internal error: no layer to destructure"
    let g ← g.replaceLocalDeclDefEq a.fvarId (← ctx.polyWhnfIdx (← instantiateMVars a.type))
    return (g, a.fvarId)

/-- `IOcc.map o o' g y` pushed through the products and sums of `o` at a pair or an injection
`y`, down to the maps of their components: definitionally equal, without `simp` lemmas for these
maps. Other terms are kept. -/
partial def pushIMap (e : Expr) : MetaM Expr := do
  unless e.isAppOf ``Codata.IOcc.map do return e
  let ex ← explicitArgs e
  let #[o, o', g, y] := ex | return e
  let y ← whnfR y
  let comps (o : Expr) : MetaM (Expr × Expr) := do
    let ex ← explicitArgs o
    return (ex[0]!, ex[1]!)
  let types : MetaM (Expr × Expr) := do
    let ty ← whnfOcc (← inferType e)
    return (ty.appFn!.appArg!, ty.appArg!)
  let head := o.getAppFn.constName?.getD .anonymous
  if head == ``Codata.IOcc.prod && y.isAppOfArity ``Prod.mk 4 then
    let (A, B) ← types
    let ((o₁, o₂), (o₁', o₂')) := (← comps o, ← comps o')
    let x₁ ← pushIMap (← mkAppM ``Codata.IOcc.map #[o₁, o₁', g, y.appFn!.appArg!])
    let x₂ ← pushIMap (← mkAppM ``Codata.IOcc.map #[o₂, o₂', g, y.appArg!])
    return ← mkAppOptM ``Prod.mk #[A, B, x₁, x₂]
  if head == ``Codata.IOcc.sum && (y.isAppOfArity ``Sum.inl 3 || y.isAppOfArity ``Sum.inr 3) then
    let (A, B) ← types
    let ((o₁, o₂), (o₁', o₂')) := (← comps o, ← comps o')
    if y.isAppOfArity ``Sum.inl 3 then
      let x ← pushIMap (← mkAppM ``Codata.IOcc.map #[o₁, o₁', g, y.appArg!])
      return ← mkAppOptM ``Sum.inl #[A, B, x]
    if y.isAppOfArity ``Sum.inr 3 then
      let x ← pushIMap (← mkAppM ``Codata.IOcc.map #[o₂, o₂', g, y.appArg!])
      return ← mkAppOptM ``Sum.inr #[A, B, x]
  return e

/-- A proof of `AgreeY o o' X oY oY'` in the goal `g`, by the lemma of each combinator of `o`. -/
partial def proveAgreeY (g : MVarId) : MetaM Unit := do
  let ex ← explicitArgs (← instantiateMVars (← g.getType))
  let some o := ex[0]? | throwError "internal error: not an agreement{indentExpr (← g.getType)}"
  let (n, binder) ← match o.getAppFn.constName? with
    | some ``Codata.Occ₂.ofY => pure (``Codata.Occ₂.AgreeY.ofY, false)
    | some ``Codata.Occ₂.ofX => pure (``Codata.Occ₂.AgreeY.ofX, false)
    | some ``Codata.Occ₂.const => pure (``Codata.Occ₂.AgreeY.const, false)
    | some ``Codata.Occ₂.prod => pure (``Codata.Occ₂.AgreeY.prod, false)
    | some ``Codata.Occ₂.sum => pure (``Codata.Occ₂.AgreeY.sum, false)
    | some ``Codata.Occ₂.comp => pure (``Codata.Occ₂.AgreeY.comp, false)
    | some ``Codata.Occ₂.pi => pure (``Codata.Occ₂.AgreeY.pi, true)
    | some ``Codata.Occ₂.piP => pure (``Codata.Occ₂.AgreeY.piP, true)
    | some ``Codata.Occ₂.sigma => pure (``Codata.Occ₂.AgreeY.sigma, true)
    | _ => throwError "internal error: no agreement for the structure{indentExpr o}"
  for g in ← g.apply (← mkConstWithFreshMVarLevels n) do
    if ← g.isAssigned then continue
    if binder then proveAgreeY (← g.intro1).2 else proveAgreeY g

/-- Rewrite in the goal `g` every map of the command's functor on an argument with a structure in
two variables, `Occ.map oY oY' f (Occ₂.ofC o z)`, by `AgreeY.map_ofC` (the structure `o'` at the
universe `ly'` of the other side, `o` at `ly`). -/
partial def agreeRewrite (P : Poly) (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let some e := tgt.find? fun e =>
      e.isAppOfArity ``Codata.Occ.map 10 && e.appArg!.isAppOfArity ``Codata.Occ₂.ofC 8
    | return g
  let ex ← explicitArgs e
  let xa := e.appArg!.getAppArgs
  let (o, X) := (xa[4]!, xa[5]!)
  let o' := o.instantiateLevelParams [P.fresh[2]!] [P.ly']
  let h ← mkFreshExprMVar (← mkAppM ``Codata.Occ₂.AgreeY #[o, o', X, ex[0]!, ex[1]!])
  proveAgreeY h.mvarId!
  let r ← g.rewrite tgt (← mkAppM ``Codata.Occ₂.AgreeY.map_ofC #[← instantiateMVars h])
  agreeRewrite P (← g.replaceTargetEq r.eNew r.eqProof)

/-- A proof of `∀ {Y Y'} g y, IOcc.map oA oA' g y = Occ.map oY oY' (g i) y` in the goal `g`, under
the binder of a point first for a combinator under a binder: the map of an indexed structure
whose positions are all at the index `i` is the map at `i` of the plain structure of the same form
(the hypothesis of `IOcc₂.AgreeY.ofOcc₂`). By definition without a sum; across one only after
cases on the value, so through the lemma of each combinator (`IOcc.map_flat_sum`, …), whose
arguments are the components of the two structures. -/
partial def proveMapFlat (g : MVarId) : MetaM Unit := do
  let ty ← instantiateMVars (← g.getType)
  let (n, isEq) ← forallTelescopeReducing ty fun xs b => return (xs.size, b.isEq)
  unless isEq do throwError "internal error: not a map at one index{indentExpr ty}"
  -- Under the binder of a point: at that point.
  if n > 4 then
    let (_, g) ← g.intro1
    return ← proveMapFlat g
  let (oA, oA', oY, oY', i) ← forallTelescopeReducing ty fun _ b => do
    let some (_, lhs, rhs) := b.eq? | unreachable!
    let l ← explicitArgs lhs
    let r ← explicitArgs rhs
    return (l[0]!.headBeta, l[1]!.headBeta, r[0]!.headBeta, r[1]!.headBeta, r[2]!.appArg!)
  if (oA.find? (·.isConstOf ``Codata.IOcc.sum)).isNone then
    return ← withUnfolding do
      let (_, g) ← g.intros
      g.refl
  let (exA, exA', exY, exY') := (← explicitArgs oA, ← explicitArgs oA', ← explicitArgs oY,
    ← explicitArgs oY')
  let (thm, args) ← match oA.getAppFn.constName? with
    | some ``Codata.IOcc.prod => pure (``Codata.IOcc.map_flat_prod,
        #[exY[0]!, exY'[0]!, exY[1]!, exY'[1]!, exA[0]!, exA'[0]!, exA[1]!, exA'[1]!])
    | some ``Codata.IOcc.sum => pure (``Codata.IOcc.map_flat_sum,
        #[exY[0]!, exY'[0]!, exY[1]!, exY'[1]!, exA[0]!, exA'[0]!, exA[1]!, exA'[1]!])
    | some ``Codata.IOcc.pi =>
      pure (``Codata.IOcc.map_flat_pi, #[exY[1]!, exY'[1]!, exA[1]!, exA'[1]!])
    | some ``Codata.IOcc.piP =>
      pure (``Codata.IOcc.map_flat_piP, #[exY[1]!, exY'[1]!, exA[1]!, exA'[1]!])
    | some ``Codata.IOcc.sigma =>
      pure (``Codata.IOcc.map_flat_sigma, #[exY[1]!, exY'[1]!, exA[1]!, exA'[1]!])
    | some ``Codata.IOcc.compC => pure (``Codata.IOcc.map_flat_compC,
        #[exA[0]!, exA'[0]!, exY[1]!, exY'[1]!, exA[1]!, exA'[1]!])
    | _ => throwError "internal error: no map at one index through{indentExpr oA}"
  -- The lemma up to its family `Y`: its explicit arguments the index, the structures, then the
  -- hypotheses of the components, proved the same way.
  let f ← mkConstWithFreshMVarLevels thm
  let fTy ← inferType f
  let k ← forallTelescope fTy fun ys _ => do
    let some k ← ys.findIdxM? fun y => return (← y.fvarId!.getUserName) == `Y
      | throwError "internal error: no family in `{thm}`"
    return k
  let (xs, bis, _) ← forallMetaBoundedTelescope fTy k
  let explicit := (xs.zip bis).filterMap fun (x, bi) => if bi.isExplicit then some x else none
  withUnfolding do
    for x in explicit, a in #[i] ++ args do
      unless ← isDefEq x a do
        throwError "internal error: ill-typed argument of `{thm}`{indentExpr a}"
    let pf ← instantiateMVars (mkAppN f xs)
    unless ← isDefEq (← inferType pf) ty do
      throwError "internal error: `{thm}` does not prove{indentExpr ty}"
    for h in explicit.extract (1 + args.size) explicit.size do
      proveMapFlat h.mvarId!
    g.assign (← instantiateMVars pf)

/-- A proof of `IOcc₂.AgreeY o o' X ι oY oY'` in the goal `g`, by the lemma of each combinator of
`o`; a part in `Y` alone is an occurrence or a plain leaf at an index. -/
partial def proveIAgreeY (g : MVarId) : MetaM Unit := do
  let ex ← explicitArgs (← instantiateMVars (← g.getType))
  let some o := ex[0]? | throwError "internal error: not an agreement{indentExpr (← g.getType)}"
  if o.isAppOf ``Codata.IOcc₂.ofOcc₂ then
    -- The plain structures agree, and the indexed structure in `Y` alone is the plain one at the
    -- index of the positions (`proveMapFlat`).
    for g in ← g.apply (← mkConstWithFreshMVarLevels ``Codata.IOcc₂.AgreeY.ofOcc₂) do
      if ← g.isAssigned then continue
      if (← whnfR (← instantiateMVars (← g.getType))).isAppOf ``Codata.Occ₂.AgreeY then
        proveAgreeY g
      else proveMapFlat g
    return
  let (n, binder) ← match o.getAppFn.constName? with
    | some ``Codata.IOcc₂.ofY =>
      match o.appArg!.getAppFn.constName? with
      | some ``Codata.IOcc.hole => pure (``Codata.IOcc₂.AgreeY.hole, false)
      | some ``Codata.IOcc.ofOcc => pure (``Codata.IOcc₂.AgreeY.ofOcc, false)
      | _ => pure (``Codata.IOcc₂.AgreeY.reidx, false)
    | some ``Codata.IOcc₂.ofX => pure (``Codata.IOcc₂.AgreeY.ofX, false)
    | some ``Codata.IOcc₂.const => pure (``Codata.IOcc₂.AgreeY.const, false)
    | some ``Codata.IOcc₂.prod => pure (``Codata.IOcc₂.AgreeY.prod, false)
    | some ``Codata.IOcc₂.sum => pure (``Codata.IOcc₂.AgreeY.sum, false)
    | some ``Codata.IOcc₂.comp => pure (``Codata.IOcc₂.AgreeY.comp, false)
    | some ``Codata.IOcc₂.pi => pure (``Codata.IOcc₂.AgreeY.pi, true)
    | some ``Codata.IOcc₂.piP => pure (``Codata.IOcc₂.AgreeY.piP, true)
    | some ``Codata.IOcc₂.sigma => pure (``Codata.IOcc₂.AgreeY.sigma, true)
    | _ => throwError "internal error: no agreement for the structure{indentExpr o}"
  for g in ← g.apply (← mkConstWithFreshMVarLevels n) do
    if ← g.isAssigned then continue
    if binder then proveIAgreeY (← g.intro1).2 else proveIAgreeY g

/-- With indices, rewrite in the goal `g` every map of the command's functor on an argument with a
structure in two variables, `IOcc.map oY oY' f (IOcc₂.ofC o z)`, by `IOcc₂.AgreeY.map_ofC`, the
index of the presentation read in the family's along `ι` (the structure `o'` at the universe
`ly'` of the other side, `o` at `ly`). -/
partial def iagreeRewrite (P : Poly) (ι : Expr) (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let some e := tgt.find? fun e =>
      e.isAppOfArity ``Codata.IOcc.map 12 && e.appArg!.isAppOfArity ``Codata.IOcc₂.ofC 10
    | return g
  let ex ← explicitArgs e
  let xa := e.appArg!.getAppArgs
  let (o, X) := (xa[6]!, xa[7]!)
  let o' := o.instantiateLevelParams [P.fresh[2]!] [P.ly']
  let h ← mkFreshExprMVar (← mkAppM ``Codata.IOcc₂.AgreeY #[o, o', X, ι, ex[0]!, ex[1]!])
  proveIAgreeY h.mvarId!
  let r ← g.rewrite tgt (← mkAppM ``Codata.IOcc₂.AgreeY.map_ofC #[← instantiateMVars h])
  iagreeRewrite P ι (← g.replaceTargetEq r.eNew r.eqProof)

/-- With indices, `T.Poly.ofL_toL`, `T.Poly.toL_ofL`, `T.Poly.ofL_map` at an index `i` of the
presentation, as without: `cases` on `a` after `polyCasesIdx`, the positions by `casesPos`, and
the indexed structures of the nested arguments. -/
def genIPolyLaws (P : Poly) : TermElabM Unit := do
  let close (xs : Array Expr) (type value : Expr) : TermElabM (Expr × Expr) :=
    withBinderInfo (P.consts ++ P.SR) .implicit do
      return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  let add (s : String) (xs : Array Expr) (stmt pf : Expr) : TermElabM Unit := do
    let (type, value) ← close xs stmt pf
    addThm (ctx.polyName s) (← ctx.levelParamsOf P.fresh #[type]) type value ctx.ref
  let hasLayer (m : Nat) : Bool :=
    P.vc[m]!.ctor.hasNest || !P.fields[m]!.isEmpty || !(P.mixAt m).isEmpty
  withLocalDecl `X .implicit (mkSort P.lx.succ) fun X => do
  withLocalDecl `Y .implicit (← ctx.polyYTy P P.Hs X P.ly) fun Y => do
  withLocalDecl `i .implicit P.I fun i => do
  let FXY ← ctx.polyFI P X Y i P.ly
  let lay ← ctx.polyILay P X Y i
  let toL (a : Expr) := ctx.polyAt P "toL" [] #[X, Y, i, a]
  let ofL (z : Expr) := ctx.polyAt P "ofL" [] #[X, Y, i, z]
  let hole := P.subX P.Hs X (← ctx.packFam Y)
  let Yfam ← ctx.polyLayFam P P.Hs X Y
  -- `ofL_toL`
  withLocalDeclD `a FXY fun a => do
    let pf ← proveHere (← mkEq (← ofL (← toL a)) a) fun g => do
      for (g, a) in ← ctx.polyCasesIdx g i.fvarId! a.fvarId! do
      for sg in ← g.cases a do
        let some mr := ctx.ctors.findIdx? fun c => sg.ctorName == some (ctx.fCtor c)
          | throwError "internal error: unexpected case {sg.ctorName}"
        let ys ← sg.mvarId.withContext do
          let some (_, _, rhs) := (← instantiateMVars (← sg.mvarId.getType)).eq?
            | throwError "internal error: expected an equation"
          -- The arguments of `F.c`, those `T.F` takes as parameters too.
          pure (rhs.getAppArgs.extract (ctx.params.size + 1) rhs.getAppNumArgs)
        for (g, m, vs) in ← polyDestructure P mr sg.mvarId ys do
        if !hasLayer m then
          g.refl
          continue
        g.withContext do
        let c := P.vc[m]!.ctor
        let some (_, _, rhs) := (← instantiateMVars (← g.getType)).eq?
          | throwError "internal error: expected an equation"
        let σ := polySubst P c vs X
        let trips ← (c.args.zip vs).zipIdx.filterMapM fun ((a, y), k) => do
          if let some f := P.fields[m]!.find? (·.k == k) then
            let t ← mkAppOptM ``Codata.Occ.toC #[none, none, none, σ f.occ, X, y]
            return some (y, ← ctx.mkOfCPlain (σ f.occ) X (← mkAppM ``Sigma.fst #[t]) fun q => do
              return mkApp (← mkAppM ``Sigma.snd #[t]) q)
          if let some f := (P.mixAt m).find? (·.k == k) then
            let o := ctx.mixOccAt f P.ly σ
            let t ← toC₂ o X Yfam y
            let w ← mkAppM ``Sigma.snd #[t]
            return some (y, ← mkOfC₂ o X Yfam (← mkAppM ``Sigma.fst #[t])
              (fun q => do return mkApp (← mkAppM ``Prod.fst #[w]) q)
              (fun q => do return mkApp (← mkAppM ``Prod.snd #[w]) q))
          match a.kind with
          | .nest n =>
            let o := ctx.nestAt n P.ly σ
            let t ← mkAppOptM ``Codata.IOcc.toC #[none, none, none, none, none, o, hole, y]
            return some (y, ← ctx.mkOfC o hole (← mkAppM ``Sigma.fst #[t]) fun q => do
              return mkApp (← mkAppM ``Sigma.snd #[t]) q)
          | _ => return none
        let lhs := rhs.replaceFVars (trips.map (·.1)) (trips.map (·.2))
        let g ← g.replaceTargetDefEq (← mkEq lhs rhs)
        withUnfolding <| simpOnly g
          #[``Codata.Occ.ofC_toC', ``Codata.IOcc.ofC_toC', ``Codata.IOcc₂.ofC_toC']
    add "ofL_toL" (P.premises ++ #[X, Y, i, a]) (← mkEq (← ofL (← toL a)) a) pf
  -- `toL_ofL`
  withLocalDeclD `z lay fun z => do
    let pf ← proveHere (← mkEq (← toL (← ofL z)) z) fun g => (ctx.polyCasesLay P g z · (some i))
      fun m g => g.withContext do
      let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
        | throwError "internal error: expected an equation"
      let mut g ← g.replaceTargetDefEq (← mkEq (← whnf lhs) rhs)
      let thms := (P.vc[m]!.ctor.nests.map fun _ => ``Codata.IOcc.toC_ofC) ++
        (P.fields[m]!.map fun _ => ``Codata.Occ.toC_ofC) ++
        (P.mixAt m).map fun _ => ``Codata.IOcc₂.toC_ofC
      for thm in thms do
        let r ← g.rewrite (← g.getType) (← mkConstWithFreshMVarLevels thm)
        g ← g.replaceTargetEq r.eNew r.eqProof
      let shape := (← whnf rhs).appFn!.appArg!
      let j := (← whnf (← inferType shape)).appArg!
      let gs ← Tactic.run g do
        Tactic.evalTactic (← `(tactic|
          refine congrArg (Sigma.mk _) (Prod.ext (funext fun p => ?_) (funext fun b => ?_))))
      for (g', fam) in gs.zip [← ctx.polyP P, ← ctx.polyB P] do
        g'.withContext do
        let p := (← getLCtx).lastDecl.get!.toExpr
        let g' ← g'.replaceLocalDeclDefEq p.fvarId! (mkApp2 fam j shape)
        for sg in ← casesPos g' p.fvarId! do sg.mvarId.refl
    add "toL_ofL" (P.premises ++ #[X, Y, i, z]) (← mkEq (← toL (← ofL z)) z) pf
  -- `ofL_map`
  withLocalDecl `Y' .implicit (← ctx.polyYTy P P.Hs X P.ly') fun Y' => do
  withLocalDeclD `f (P.subX P.Hs X (← ctx.famFn Y Y')) fun f => do
  withLocalDeclD `z lay fun z => do
    let fι ← lam `j P.I fun j => do
      return mkAppN f (← ctx.projs (← ctx.polyIota P P.Hs X j))
    let mapped ← mkAppOptM ``Codata.ILay.map #[← ctx.polySig P, ← ctx.polyP P, X,
      ← ctx.polyLayFam P P.Hs X Y, ← ctx.polyLayFam P P.Hs X Y', fι, i, z]
    let lhs ← ctx.polyAt P "ofL" [(P.fresh[2]!, P.ly')] #[X, Y', i, mapped]
    let rhs := mkAppN (← ctx.constWith ctx.Fmap [P.ly, P.ly'])
      (ctx.polyParams P P.Hs X ++ #[Y, Y', f] ++ (← ctx.projs (← ctx.polyIota P P.Hs X i)) ++
        #[← ofL z])
    let stmt ← mkEq lhs rhs
    let ι ← lam `j P.I fun j => ctx.polyIota P P.Hs X j
    let pf ← proveHere stmt fun g => (ctx.polyCasesLay P g z · (some i)) fun m g => do
      if !hasLayer m then return ← g.refl
      g.withContext do
      let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
        | throwError "internal error: expected an equation"
      -- The map of a split argument pushed through its products and sums to its parts.
      let rhs ← whnf rhs
      let rhs ← if P.vc[m]!.split then
          pure (mkAppN rhs.getAppFn (← rhs.getAppArgs.mapM fun e => pushIMap e))
        else pure rhs
      let g ← g.replaceTargetDefEq (← mkEq (← whnf lhs) rhs)
      withUnfolding do
        -- An argument with a structure in two variables: its map by `IOcc₂.AgreeY.map_ofC`.
        let g ← if (P.mixAt m).isEmpty then pure g else iagreeRewrite P ι g
        if let some g ← simpOnlyStep g
            #[``Codata.ILay.map, ``Codata.Occ.map_ofC, ``Codata.IOcc.map_ofC] then
          g.refl
    add "ofL_map" (P.premises ++ #[X, Y, Y', f, i, z]) stmt pf

/-- `T.Poly.ofL_toL`, `T.Poly.toL_ofL`, `T.Poly.ofL_map`. -/
def genPolyLaws (P : Poly) : TermElabM Unit := do
  if ctx.idxed then return ← ctx.genIPolyLaws P
  let close (xs : Array Expr) (type value : Expr) : TermElabM (Expr × Expr) :=
    withBinderInfo (P.consts ++ P.SR) .implicit do
      return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  let add (s : String) (xs : Array Expr) (stmt pf : Expr) : TermElabM Unit := do
    let (type, value) ← close xs stmt pf
    addThm (ctx.polyName s) (← ctx.levelParamsOf P.fresh #[type]) type value ctx.ref
  let hasLayer (m : Nat) : Bool :=
    P.vc[m]!.ctor.hasNest || !P.fields[m]!.isEmpty || !(P.mixAt m).isEmpty
  withLocalDecl `X .implicit (mkSort P.lx.succ) fun X => do
  withLocalDecl `Y .implicit (mkSort P.ly.succ) fun Y => do
  let FXY ← ctx.polyF P X Y P.ly
  let lay ← ctx.polyLay P X Y
  let toL (a : Expr) := ctx.polyAt P "toL" [] #[X, Y, a]
  let ofL (z : Expr) := ctx.polyAt P "ofL" [] #[X, Y, z]
  -- `ofL_toL`: `ofL (toL (F.c ys))` unfolds to `F.c ys'` with `ofC o ⟨(toC o x).1, …⟩` for a
  -- field or a nested argument `x`, which `ofC_toC'` rewrites.
  withLocalDeclD `a FXY fun a => do
    let pf ← proveHere (← mkEq (← ofL (← toL a)) a) fun g => do
      for sg in ← g.cases a.fvarId! do
        let some mr := ctx.ctors.findIdx? fun c => sg.ctorName == some (ctx.fCtor c)
          | throwError "internal error: unexpected case {sg.ctorName}"
        for (g, m, vs) in ← polyDestructure P mr sg.mvarId sg.fields do
        if !hasLayer m then
          g.refl
          continue
        g.withContext do
        let c := P.vc[m]!.ctor
        let some (_, _, rhs) := (← instantiateMVars (← g.getType)).eq?
          | throwError "internal error: expected an equation"
        let σ := polySubst P c vs X
        let roundTrip (o hole y : Expr) : TermElabM Expr := do
          let t ← mkAppOptM ``Codata.Occ.toC #[none, none, none, o, hole, y]
          ctx.mkOfC o hole (← mkAppM ``Sigma.fst #[t]) fun q => do
            return mkApp (← mkAppM ``Sigma.snd #[t]) q
        let trips ← (c.args.zip vs).zipIdx.filterMapM fun ((a, y), i) => do
          if let some f := P.fields[m]!.find? (·.k == i) then
            return some (y, ← roundTrip (σ f.occ) X y)
          if let some f := (P.mixAt m).find? (·.k == i) then
            let o := ctx.mixOccAt f P.ly σ
            let t ← toC₂ o X Y y
            let w ← mkAppM ``Sigma.snd #[t]
            return some (y, ← mkOfC₂ o X Y (← mkAppM ``Sigma.fst #[t])
              (fun q => do return mkApp (← mkAppM ``Prod.fst #[w]) q)
              (fun q => do return mkApp (← mkAppM ``Prod.snd #[w]) q))
          match a.kind with
          | .nest n => return some (y, ← roundTrip (ctx.nestAt n P.ly σ) Y y)
          | _ => return none
        let lhs := rhs.replaceFVars (trips.map (·.1)) (trips.map (·.2))
        let g ← g.replaceTargetDefEq (← mkEq lhs rhs)
        withUnfolding <| simpOnly g #[``Codata.Occ.ofC_toC', ``Codata.Occ₂.ofC_toC']
    add "ofL_toL" (P.premises ++ #[X, Y, a]) (← mkEq (← ofL (← toL a)) a) pf
  -- `toL_ofL`: the layers `toC o (ofC o z)` rewritten one by one, then the positions by cases.
  withLocalDeclD `z lay fun z => do
    let pf ← proveHere (← mkEq (← toL (← ofL z)) z) fun g => ctx.polyCasesLay P g z fun m g =>
      g.withContext do
      let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
        | throwError "internal error: expected an equation"
      let mut g ← g.replaceTargetDefEq (← mkEq (← whnf lhs) rhs)
      for _ in [0:P.vc[m]!.ctor.nests.size + P.fields[m]!.size] do
        let r ← g.rewrite (← g.getType) (← mkConstWithFreshMVarLevels ``Codata.Occ.toC_ofC)
        g ← g.replaceTargetEq r.eNew r.eqProof
      for _ in [0:(P.mixAt m).size] do
        let r ← g.rewrite (← g.getType) (← mkConstWithFreshMVarLevels ``Codata.Occ₂.toC_ofC)
        g ← g.replaceTargetEq r.eNew r.eqProof
      let shape := (← whnf rhs).appFn!.appArg!
      let gs ← Tactic.run g do
        Tactic.evalTactic (← `(tactic|
          refine congrArg (Sigma.mk _) (Prod.ext (funext fun p => ?_) (funext fun b => ?_))))
      for (g', fam) in gs.zip [← ctx.polyP P, ← ctx.polyB P] do
        g'.withContext do
        let p := (← getLCtx).lastDecl.get!.toExpr
        let g' ← g'.replaceLocalDeclDefEq p.fvarId! (mkApp fam shape)
        for sg in ← g'.cases p.fvarId! do sg.mvarId.refl
    add "toL_ofL" (P.premises ++ #[X, Y, z]) (← mkEq (← toL (← ofL z)) z) pf
  -- `ofL_map`
  withLocalDecl `Y' .implicit (mkSort P.ly'.succ) fun Y' => do
  withLocalDeclD `f (← mkArrow Y Y') fun f => do
  withLocalDeclD `z lay fun z => do
    let mapped ← mkAppM ``Codata.Lay.map #[f, z]
    let lhs ← ctx.polyAt P "ofL" [(P.fresh[2]!, P.ly')] #[X, Y', mapped]
    let rhs := mkAppN (← ctx.constWith ctx.Fmap [P.ly, P.ly'])
      (ctx.polyParams P P.Hs X ++ #[Y, Y', f, ← ofL z])
    let stmt ← mkEq lhs rhs
    let pf ← proveHere stmt fun g => ctx.polyCasesLay P g z fun m g => do
      if !hasLayer m then return ← g.refl
      g.withContext do
      let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
        | throwError "internal error: expected an equation"
      let g ← g.replaceTargetDefEq (← mkEq (← whnf lhs) (← whnf rhs))
      -- The map of a split argument goes through its products and sums to its parts.
      let sums := #[``Codata.Occ.map_prod, ``Codata.Occ.map_sum_inl, ``Codata.Occ.map_sum_inr]
      let split := if P.vc[m]!.split then sums ++ #[``Codata.Occ.map_const, ``Codata.Occ.map_hole,
          ``Codata.Occ.map_pi] else #[]
      withUnfolding do
        if (P.mixAt m).isEmpty then
          if let some g ← simpOnlyStep g (#[``Codata.Lay.map, ``Codata.Occ.map_ofC] ++ split) then
            g.refl
          return
        -- With an argument with a structure in two variables: first through the products and
        -- sums of a split argument, then the map of that argument by `AgreeY.map_ofC`.
        let simpOr (g : MVarId) (lemmas : Array Name) : MetaM (Option MVarId) :=
          simpOnlyStep g lemmas (failIfUnchanged := false)
        let some g ← if P.vc[m]!.split then simpOr g sums else pure (some g) | return
        let g ← agreeRewrite P g
        if let some g ← simpOr g (#[``Codata.Lay.map, ``Codata.Occ.map_ofC] ++ split) then
          g.refl
    add "ofL_map" (P.premises ++ #[X, Y, Y', f, z]) stmt pf

/-! ### The fixpoint and the instances -/

/-- With indices, `T.Poly.fix (X) : IPolyFix P tree X (fun i => T (H X) (ι i))`: `icoFix`
(`iinFix`), whose `corec` (`fold`) on states over the index of the presentation is the type's on
the states `Along ι St` (`Over ι St`) over its own index, and the bisimulation (induction)
principle from the contract along `ι` (`ico_bisim`, `iin_ind`). The proof arguments are `rw` on
goal metavariables, as without indices. -/
def genIPolyFix (P : Poly) : TermElabM Unit := do
  let L ← ctx.tLvl
  let pX (X : Expr) := ctx.polyParams P P.Hs X
  let ident (n : Name) : Ident := mkCIdent n
  -- The layers maps composed by the states (`Along`, `Over`) are the expected ones by unfolding:
  -- `rfl` after the rewriting.
  let rwTac (steps : Array (Bool × Name)) : TermElabM (TSyntax `tactic) := do
    let rules ← steps.mapM fun (rev, n) =>
      if rev then `(Parser.Tactic.rwRule| ← $(ident n):ident)
      else `(Parser.Tactic.rwRule| $(ident n):ident)
    `(tactic| rw [$rules,*] <;> rfl)
  let σE ← ctx.polySig P
  let Pc ← ctx.polyP P
  withLocalDeclD `X (mkSort P.lx.succ) fun X => do
  -- The type at the premises, curried, and as a family over the index of the presentation.
  let T := mkAppN (← ctx.constWith ctx.name []) (pX X)
  let TI ← ctx.polyLayFam P P.Hs X T
  let I' := P.subX P.Hs X (← ctx.ixp)
  let ιf ← lam `j P.I fun j => ctx.polyIota P P.Hs X j
  let idxAt (i : Expr) : MetaM (Array Expr) := do ctx.projs (← ctx.polyIota P P.Hs X i)
  let yL (w : Level) := [(P.fresh[2]!, w)]
  let toL (Y i a : Expr) (w : Level) := ctx.polyAt P "toL" (yL w) #[X, Y, i, a]
  let ofL (Y i z : Expr) (w : Level) := ctx.polyAt P "ofL" (yL w) #[X, Y, i, z]
  let dtorAt (i t : Expr) : MetaM Expr := do
    return mkAppN (← ctx.constWith ctx.dtor []) (pX X ++ (← idxAt i) |>.push t)
  let dL ← lam `i P.I (bi := .implicit) fun i => do
    lam `a (mkApp TI i).headBeta fun a => do toL T i (← dtorAt i a) L
  let K := mkAppN (← ctx.constWith ctx.contract []) (pX X)
  -- The layer on families over `I'`, the contract's, curried for `T.F`.
  let curry (Y : Expr) : TermElabM Expr := do return P.subX P.Hs X (← ctx.curryFam Y)
  let ofLz (ty : Expr) : TermElabM Expr := lamOf ty fun xs => do
    ofL (← curry xs[0]!) xs[1]! xs[2]! (← famLevel xs[0]!)
  let toLz (ty : Expr) : TermElabM Expr := lamOf ty fun xs => do
    toL (← curry xs[0]!) xs[1]! xs[2]! (← famLevel xs[0]!)
  let ofL_toL (Y i a : Expr) : TermElabM Expr := do
    ctx.polyAt P "ofL_toL" (yL (← famLevel Y)) #[X, Y, i, a]
  let ofL_map (ty : Expr) : TermElabM Expr := lamOf ty fun xs => do
    ctx.polyAt P "ofL_map" [(P.fresh[2]!, ← famLevel xs[0]!), (P.fresh[3]!, ← famLevel xs[1]!)]
      #[X, ← curry xs[0]!, ← curry xs[1]!, P.subX P.Hs X (← ctx.curryN xs[2]! 1), xs[3]!, xs[4]!]
  -- `T.F (H X) Y` over `I'`, for the states.
  let FOn (Y : Expr) (w : Level) : TermElabM Expr := lam `j I' fun j => do
    return mkAppN (← ctx.polyF P X Y w) (← ctx.projs j)
  let value ← withUnfolding do
    if ctx.co then
      let f ← mkAppOptM ``Codata.icoFix #[σE, Pc, X, TI, dL]
      let f ← fillArg f fun ty => lamOf ty fun xs => do
        let (St, c, i, s) := (xs[0]!, xs[1]!, xs[2]!, xs[3]!)
        let lSt ← famLevel St
        let Al ← mkAppOptM ``Codata.Along #[σE, I', ιf, St]
        let AlC ← curry Al
        let ofL' ← lam `i P.I (bi := .implicit) fun i => do
          lam `z (← ctx.polyILay P X AlC i) fun z => ofL AlC i z lSt
        let co ← mkAppOptM ``Codata.Along.coalg
          #[σE, Pc, X, I', ιf, St, ← FOn AlC lSt, ofL', c]
        let mk ← mkAppOptM ``Codata.Along.mk #[σE, I', ιf, St, i, s]
        return mkAppN (← ctx.constWith ctx.corec [lSt])
          (pX X ++ #[AlC, P.subX P.Hs X (← ctx.curryN co 1)] ++ (← idxAt i) |>.push mk)
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.dtor_corec), (false, ``Codata.Along.coalg_mk),
          (true, ctx.polyName "ofL_map"), (false, ctx.polyName "toL_ofL")])
      let bis ← mkAppFirst ``Codata.ico_bisim #[σE, Pc, X] 6
      let bis ← fillArg bis fun _ => pure K
      let bis ← fillArg bis fun _ => pure ιf
      let bis ← fillArg bis fun _ => pure dL
      let bis ← fillArg bis ofLz
      let bis ← fillArg bis fun ty => lamOf ty fun xs => do
        ofL_toL T xs[0]! (← dtorAt xs[0]! xs[1]!)
      let bis ← fillArg bis ofL_map
      fillArg f fun _ => pure bis
    else
      let ctorL ← lam `i P.I (bi := .implicit) fun i => do
        lam `z (← ctx.polyILay P X T i) fun z => do
          return mkAppN (← ctx.constWith ctx.ctor []) (pX X ++ (← idxAt i) |>.push
            (← ofL T i z L))
      let f ← mkAppOptM ``Codata.iinFix #[σE, Pc, X, TI, ctorL, dL]
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.dtor_ctor), (false, ctx.polyName "toL_ofL")])
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.polyName "ofL_toL"), (false, ctx.ctor_dtor)])
      let f ← fillArg f fun ty => lamOf ty fun xs => do
        let (St, a, i, t) := (xs[0]!, xs[1]!, xs[2]!, xs[3]!)
        let lSt ← famLevel St
        let Ov ← mkAppOptM ``Codata.Over #[σE, I', ιf, St]
        let OvC ← curry Ov
        let toL' ← lam `i P.I (bi := .implicit) fun i => do
          lam `y (← ctx.polyFI P X OvC i lSt) fun y => toL OvC i y lSt
        let alg ← mkAppOptM ``Codata.Over.alg #[σE, Pc, X, I', ιf, St, ← FOn OvC lSt, toL', a]
        let folded := mkAppN (← ctx.constWith ctx.fold [lSt])
          (pX X ++ #[OvC, P.subX P.Hs X (← ctx.curryN alg 1)] ++ (← idxAt i) |>.push t)
        return mkApp2 folded i (← mkEqRefl (← ctx.polyIota P P.Hs X i))
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.fold_ctor), (false, ``Codata.Over.alg_apply),
          (true, ctx.polyName "ofL_map"), (false, ctx.polyName "toL_ofL")])
      let ind ← mkAppFirst ``Codata.iin_ind #[σE, Pc, X] 6
      let ind ← fillArg ind fun _ => pure K
      let ind ← fillArg ind fun _ => pure ιf
      let ind ← fillArg ind toLz
      let ind ← fillArg ind ofLz
      let ind ← fillArg ind fun ty => lamOf ty fun xs => do
        ofL_toL (← curry xs[0]!) xs[1]! xs[2]!
      let ind ← fillArg ind ofL_map
      fillArg f fun _ => pure ind
  let value ← instantiateMVars value
  let type ← inferType value
  let (type, value) ← withBinderInfo (P.consts ++ P.SR) .implicit do
    let xs := P.premises.push X
    return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  addDef (ctx.polyName "fix") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref

/-- `T.Poly.fix (X) : PolyFix P tree X (T (H X))`, from the public declarations of the type:
`coFix` (`inFix` for `data`), its proof arguments by `rw` on goal metavariables, and the
bisimulation (induction) principle from the contract (`co_bisim`, `in_ind`). -/
def genPolyFix (P : Poly) : TermElabM Unit := do
  if ctx.idxed then return ← ctx.genIPolyFix P
  let L ← ctx.tLvl
  let pX (X : Expr) := ctx.polyParams P P.Hs X
  let ident (n : Name) : Ident := mkCIdent n
  let rwTac (steps : Array (Bool × Name)) : TermElabM (TSyntax `tactic) := do
    let rules ← steps.mapM fun (rev, n) =>
      if rev then `(Parser.Tactic.rwRule| ← $(ident n):ident)
      else `(Parser.Tactic.rwRule| $(ident n):ident)
    `(tactic| rw [$rules,*])
  withLocalDeclD `X (mkSort P.lx.succ) fun X => do
  let TX := mkAppN (← ctx.constWith ctx.name []) (pX X)
  let yL (w : Level) := [(P.fresh[2]!, w)]
  let toL (Y a : Expr) (w : Level) := ctx.polyAt P "toL" (yL w) #[X, Y, a]
  let ofL (Y z : Expr) (w : Level) := ctx.polyAt P "ofL" (yL w) #[X, Y, z]
  let dtorAt (t : Expr) : MetaM Expr := return mkAppN (← ctx.constWith ctx.dtor []) (pX X |>.push t)
  let dL ← lam `a TX fun a => do toL TX (← dtorAt a) L
  let K := mkAppN (← ctx.constWith ctx.contract []) (pX X)
  let ofLz (ty : Expr) : TermElabM Expr := lamOf ty fun xs => do
    ofL xs[0]! xs[1]! (← typeLevel xs[0]!)
  let ofL_toL (Y a : Expr) : TermElabM Expr := do
    ctx.polyAt P "ofL_toL" (yL (← typeLevel Y)) #[X, Y, a]
  let ofL_map (ty : Expr) : TermElabM Expr := lamOf ty fun xs => do
    ctx.polyAt P "ofL_map" [(P.fresh[2]!, ← typeLevel xs[0]!), (P.fresh[3]!, ← typeLevel xs[1]!)]
      (#[X] ++ xs)
  let value ← withUnfolding do
    if ctx.co then
      let f ← mkAppOptM ``Codata.coFix #[none, none, none, none, none, dL]
      let f ← fillArg f fun ty => lamOf ty fun xs => do
        let (St, c, s) := (xs[0]!, xs[1]!, xs[2]!)
        let lSt ← typeLevel St
        let c' ← lam `st St fun st => ofL St (mkApp c st) lSt
        return mkAppN (← ctx.constWith ctx.corec [lSt]) (pX X ++ #[St, c', s])
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.dtor_corec), (true, ctx.polyName "ofL_map"),
          (false, ctx.polyName "toL_ofL")])
      let bis ← fillArg (← mkAppMVars ``Codata.co_bisim 6) fun _ => pure K
      let bis ← fillArg bis fun _ => pure dL
      let bis ← fillArg bis ofLz
      let bis ← fillArg bis fun ty => lamOf ty fun xs => do ofL_toL TX (← dtorAt xs[0]!)
      let bis ← fillArg bis ofL_map
      fillArg f fun _ => pure bis
    else
      let ctorL ← lam `z (← ctx.polyLay P X TX) fun z => do
        return mkAppN (← ctx.constWith ctx.ctor []) (pX X |>.push (← ofL TX z L))
      let f ← mkAppOptM ``Codata.inFix #[none, none, none, none, none, ctorL, dL]
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.dtor_ctor), (false, ctx.polyName "toL_ofL")])
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.polyName "ofL_toL"), (false, ctx.ctor_dtor)])
      let f ← fillArg f fun ty => lamOf ty fun xs => do
        let (St, a, t) := (xs[0]!, xs[1]!, xs[2]!)
        let lSt ← typeLevel St
        let a' ← lam `y (← ctx.polyF P X St lSt) fun y => do return mkApp a (← toL St y lSt)
        return mkAppN (← ctx.constWith ctx.fold [lSt]) (pX X ++ #[St, a', t])
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.fold_ctor), (true, ctx.polyName "ofL_map"),
          (false, ctx.polyName "toL_ofL")])
      let ind ← fillArg (← mkAppMVars ``Codata.in_ind 6) fun _ => pure K
      let ind ← fillArg ind fun ty => lamOf ty fun xs => do toL xs[0]! xs[1]! (← typeLevel xs[0]!)
      let ind ← fillArg ind ofLz
      let ind ← fillArg ind fun ty => lamOf ty fun xs => ofL_toL xs[0]! xs[1]!
      let ind ← fillArg ind ofL_map
      fillArg f fun _ => pure ind
  let value ← instantiateMVars value
  let type ← inferType value
  let (type, value) ← withBinderInfo (P.consts ++ P.SR) .implicit do
    let xs := P.premises.push X
    return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  addDef (ctx.polyName "fix") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref

/-- `T.Poly.fix` at the premises `Hs` (with their instances `insts`) and `X`, at the universes
`σ`. -/
def polyFixAt (P : Poly) (σ : List (Name × Level)) (Hs insts : Array Expr) (X : Expr) :
    MetaM Expr := do
  return mkAppN (← polyConst (ctx.polyName "fix") σ) (P.consts ++ Hs ++ P.SR ++ insts |>.push X)

/-- Add the instance `n` of type `type` with value `value`, closed over `xs`. -/
def addPolyInstance (P : Poly) (n : Name) (xs : Array Expr) (type value : Expr) :
    TermElabM Unit := do
  let (type, value) ← withBinderInfo (P.consts ++ P.Hs ++ P.Hs' ++ P.SR) .implicit do
    return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  addDef n (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref
  registerInstance n .global (eval_prio default)

/-- When the last parameter is the last hole, the instances `T.Poly.instPolyIsoEta`,
`T.Poly.instPolyMapEta` for `T a₁ … aₙ₋₁` itself, a type `T` without indices: `fun X => T a X` is
`T a`, the instances at the identity in the last parameter, the other holes constant. -/
def genPolyEta (P : Poly) (T : Name) : TermElabM Unit := do
  let isoN := T ++ `Poly ++ `instPolyIso
  let mapN := T ++ `Poly ++ `instPolyMap
  let some last := ctx.params.back? | return
  unless P.holes.back? == some last do return
  let others := P.holes.pop
  let lastLvl ← typeLevel last
  let lastTy ← inferType last
  let idH ← lam `X lastTy fun X => pure X
  let etaHs ← others.mapM fun a => lam `X lastTy fun _ => pure a
  let etaSR ← others.mapM fun a => do
    return #[a, ← lam `x a fun _ => pure (Lean.mkConst ``Empty)]
  let etaSR := etaSR.flatten ++
    #[Lean.mkConst ``Unit, ← lam `x (Lean.mkConst ``Unit) fun _ => pure (Lean.mkConst ``Unit)]
  let etaHs := etaHs.push idH
  let synth (Hs : Array Expr) : TermElabM (Array Expr) :=
    (Array.range Hs.size).mapM fun i => do
      synthInstance (← mkAppM ``Codata.PolyIso #[Hs[i]!, etaSR[2 * i]!, etaSR[2 * i + 1]!])
  let insts ← synth etaHs
  -- The universes of the instances at these premises.
  let levelsOf (es : Array Expr) : MetaM (List (Name × Level)) := do
    let mut σ := [(P.fresh[0]!, lastLvl)]
    for i in [0:P.holes.size] do
      σ := σ ++ [(P.fresh[5 + 2 * i]!, ← typeLevel es[2 * i]!), (P.fresh[6 + 2 * i]!, Level.zero)]
    return σ
  let σ ← levelsOf etaSR
  let isoE := mkAppN (← polyConst isoN σ) (P.consts ++ etaHs ++ etaSR ++ insts)
  -- The functors `fun X => T a X` of the types, eta-reduced.
  let etaType (ty : Expr) : Expr :=
    mkAppN ty.getAppFn (ty.getAppArgs.modify 0 Expr.eta |>.modify 1 Expr.eta)
  ctx.addPolyInstance P (T ++ `Poly ++ `instPolyIsoEta) (P.consts ++ others)
    (etaType (← whnfR (← inferType isoE))) isoE
  -- Across universes only when the universe of the last parameter is its own: a level in one
  -- universe parameter (`u`, `u + 1`, `max u 1`) that no other parameter's type mentions.
  let own? ← match (collectLevelParams {} (mkSort lastLvl)).params.toList with
    | [u] => do
      let shared ← others.anyM fun a => do
        return (collectLevelParams {} (← inferType a)).params.contains u
      pure (if !P.primes.any (·.1 == u) || shared then none else some u)
    | _ => pure none
  -- The primed universes of `instPolyMap`: that of the last parameter, if it is its own, the
  -- others unprimed (the other holes are fixed).
  let lastLvl' := match own? with
    | some u => lastLvl.instantiateParams [u] [P.lvl 4]
    | none => lastLvl
  let σu := P.primes.filterMap fun (v, v') => match v' with
    | .param n => some (n, if own? == some v then P.lvl 4 else .param v)
    | _ => none
  let idH' ← lam `X (mkSort lastLvl'.succ) fun X => pure X
  let etaHs' := (← others.mapM fun a => lam `X (mkSort lastLvl'.succ) fun _ => pure a).push idH'
  let insts' ← synth etaHs'
  -- The premises' maps: of the identity and of constants.
  let maps ← (Array.range etaHs.size).mapM fun i => do
    synthInstance (← mkAppOptM ``Codata.PolyMap (#[etaHs[i]!, etaHs'[i]!, etaSR[2 * i]!,
      etaSR[2 * i + 1]!, insts[i]!, insts'[i]!].map some))
  let σm := σ ++ [(P.fresh[1]!, lastLvl')] ++ σu
  let mapE := mkAppN (← polyConst mapN σm)
    (P.consts ++ etaHs ++ etaHs' ++ etaSR ++ insts ++ insts' ++ maps)
  let mapTy ← whnfR (← inferType mapE)
  ctx.addPolyInstance P (T ++ `Poly ++ `instPolyMapEta) (P.consts ++ others)
    (etaType mapTy) mapE

/-- With indices, for each type `Tₘ` (the family, or the types of a block) at its indices `idx`,
which are arguments of the instances: `Tₘ.Poly.instPolyIso` for `fun X => Tₘ (H X) idx`, at the
trees of shapes at its index `i` of the presentation (`⟨idx⟩`, or `Blk.Poly.Ix.Tₘ idx`), and
`Tₘ.Poly.instPolyMap`; for a type of a block without indices, the eta forms (`genPolyEta`). -/
def genIPolyInstances (P : Poly) : TermElabM Unit := do
  let σE ← ctx.polySig P
  let Pc ← ctx.polyP P
  let fam := if ctx.co then ``Codata.Signature.Cotype else ``Codata.Signature.Intype
  let tree ← mkAppM (if ctx.co then ``Codata.coITree else ``Codata.inITree) #[σE]
  for m in [0:ctx.types.size] do
    let t := ctx.types[m]!
    let i ← ctx.polyIdx P (ctx.wrap m t.idx)
    let W ← mkAppM fam #[σE, i]
    let path ← mkAppOptM ``Codata.IPath #[σE, Pc, none, tree, i]
    -- The functor `fun X => Tₘ (H X) idx`, and at the primed universes `fun X => Tₘ (H' X) idx`.
    let Tc ← ctx.constWith t.name []
    let funT ← lam `X (mkSort P.lx.succ) fun X =>
      return mkAppN Tc (ctx.polyParams P P.Hs X ++ t.idx)
    let funT' ← lam `X (mkSort P.lx'.succ) fun X =>
      return mkAppN (P.prime Tc) (ctx.polyParams P P.Hs' X ++ t.idx)
    let isoN := t.name ++ `Poly ++ `instPolyIso
    let mapN := t.name ++ `Poly ++ `instPolyMap
    -- `PolyIso`
    do
      let equiv ← lam `X (mkSort P.lx.succ) (bi := .implicit) fun X => do
        mkAppOptM ``Codata.IPolyFix.equiv #[none, none, none, none, none, none,
          ← ctx.polyFixAt P [] P.Hs P.insts X, i]
      let value ← mkAppOptM ``Codata.PolyIso.mk #[funT, W, path, equiv]
      ctx.addPolyInstance P isoN (P.premises ++ t.idx) (← mkAppM ``Codata.PolyIso #[funT, W, path])
        value
    -- `PolyMap`
    do
      let iso := mkAppN (← polyConst isoN) (P.premises ++ t.idx)
      let σ' := (P.fresh[0]!, P.lx') :: P.primes
      let iso' := mkAppN (← polyConst isoN σ') (P.consts ++ P.Hs' ++ P.SR ++ P.insts' ++ t.idx)
      let mp ← mkAppOptM ``Codata.PolyMap.mk #[funT, funT', W, path, iso, iso']
      let fix (X Y : Expr) : MetaM (Expr × Expr) := do
        return (← ctx.polyFixAt P [] P.Hs P.insts X, ← ctx.polyFixAt P σ' P.Hs' P.insts' Y)
      let along (n : Name) (xs : Array Expr) : TermElabM Expr := do
        let (M, M') ← fix xs[0]! xs[1]!
        mkAppOptM n #[none, none, none, none, none, none, M, none, none, M', xs[2]!, i, xs[3]!]
      let mp ← fillArg mp fun ty => lamOf ty (along ``Codata.IPolyFix.map)
      let mp ← withUnfolding <| fillArg mp fun ty => lamOf ty (along ``Codata.IPolyFix.equiv_map)
      let xs := P.consts ++ P.Hs ++ P.Hs' ++ P.SR ++ P.insts ++ P.insts' ++ P.maps ++ t.idx
      ctx.addPolyInstance P mapN xs (← inferType mp) (← instantiateMVars mp)
    if t.idx.isEmpty then ctx.genPolyEta P t.name

/-- `T.Poly.instPolyIso`, `T.Poly.instPolyMap`, and when the last parameter is the last hole,
the instances `T.Poly.instPolyIsoEta`, `T.Poly.instPolyMapEta` for `T a₁ … aₙ₋₁` itself. -/
def genPolyInstances (P : Poly) : TermElabM Unit := do
  if ctx.idxed then return ← ctx.genIPolyInstances P
  let B ← ctx.polyB P
  let fam := if ctx.co then ``Codata.Signature.Cotype else ``Codata.Signature.Intype
  let W ← mkAppM fam #[← mkAppOptM ``Codata.shapeSig #[none, B], mkConst ``Unit.unit]
  let tree ← mkAppM (if ctx.co then ``Codata.coTree else ``Codata.inTree) #[B]
  let path ← mkAppM ``Codata.Path #[← ctx.polyP P, tree]
  -- The functor `fun X => T (H X)`, and at the primed universes `fun X => T (H' X)`.
  let Tc ← ctx.constWith ctx.name []
  let funT ← lam `X (mkSort P.lx.succ) fun X => return mkAppN Tc (ctx.polyParams P P.Hs X)
  let funT' ← lam `X (mkSort P.lx'.succ) fun X =>
    return mkAppN (P.prime Tc) (ctx.polyParams P P.Hs' X)
  let isoN := ctx.polyName "instPolyIso"
  let mapN := ctx.polyName "instPolyMap"
  -- `PolyIso`
  do
    let equiv ← lam `X (mkSort P.lx.succ) (bi := .implicit) fun X => do
      mkAppM ``Codata.PolyFix.equiv #[← ctx.polyFixAt P [] P.Hs P.insts X]
    let value ← mkAppOptM ``Codata.PolyIso.mk #[funT, W, path, equiv]
    ctx.addPolyInstance P isoN P.premises (← mkAppM ``Codata.PolyIso #[funT, W, path]) value
  -- `PolyMap`
  do
    let iso := mkAppN (← polyConst isoN) P.premises
    let σ' := (P.fresh[0]!, P.lx') :: P.primes
    let iso' := mkAppN (← polyConst isoN σ') (P.consts ++ P.Hs' ++ P.SR ++ P.insts')
    let m ← mkAppOptM ``Codata.PolyMap.mk #[funT, funT', W, path, iso, iso']
    let fix (X Y : Expr) : MetaM (Expr × Expr) := do
      return (← ctx.polyFixAt P [] P.Hs P.insts X, ← ctx.polyFixAt P σ' P.Hs' P.insts' Y)
    let m ← fillArg m fun ty => lamOf ty fun xs => do
      let (M, M') ← fix xs[0]! xs[1]!
      mkAppM ``Codata.PolyFix.map #[M, M', xs[2]!, xs[3]!]
    let m ← withUnfolding <| fillArg m fun ty => lamOf ty fun xs => do
      let (M, M') ← fix xs[0]! xs[1]!
      mkAppM ``Codata.PolyFix.equiv_map #[M, M', xs[2]!, xs[3]!]
    let xs := P.consts ++ P.Hs ++ P.Hs' ++ P.SR ++ P.insts ++ P.insts' ++ P.maps
    ctx.addPolyInstance P mapN xs (← inferType m) (← instantiateMVars m)
  ctx.genPolyEta P ctx.name

/-! ### The simp lemmas

For every constructor `c` of a type `Tₘ`, two simp lemmas at the premises, so that `simp`
computes through the instances:

* `Tₘ.Poly.map_c`, the map on the constructor:
  `(Occ.ofIso fun X => Tₘ (H X) idx).map (Occ.ofIso fun X => Tₘ (H' X) idx) f (Tₘ.c args) =
  Tₘ.c args'`, the arguments mapped by kind: data unchanged, a field at a parameter position by
  the map of its structure in the premises (`(Occ.ofIso H).map (Occ.ofIso H') f a`, which `simp`
  makes `f a` at the identity, `Occ.map_ofIso_id`), a recursive argument by this map, a nested one
  by the map of its structure. The map is stated on the leaf `Occ.ofIso` of the instance, the form
  in which the generated rules of other types (`fold_c`, `F.map_c`) mention it. `PolyMap.map`
  takes the functor implicitly, so `simp` would unify the constructor's arguments first, at `H X`
  for an unknown `H` (`?H ?X =?= T` at the identity premise), and the rule would not apply;
  `Occ.ofIso` and `PolyIso.Mem` take it explicitly. It is `PolyFix.map_eq_of_d` at the constructor
  `ctor ∘ ofL`, after `dtor_c`; the right-hand side is the result by definition.
* `Tₘ.Poly.mem_c`, membership in the constructor: `PolyIso.Mem (fun X => Tₘ (H X) idx) x
  (Tₘ.c args) ↔ …`, a disjunct per field at a parameter position (membership through its
  structure in the premises) and per recursive argument (membership in it, under a telescope at
  some arguments, through a nested argument in some member of it), `False` without any. It is
  `PolyFix.exists_val_iff` after `dtor_c`, then cases on the positions of the layer.

The functors of the left-hand sides are not indexed (`no_index`): the leaves of other types'
rules are often eta-reduced (`Occ.ofIso Forest`). Both lemmas are stated for `codata` as for
`data`: a value of a `codata` type is the constructor of its `dtor` (`ctor_dtor`), and `corec_eq`
writes a corecursive value so; membership is one step for `codata` too, since a member is at a
finite depth.

The lemmas are per constructor of the presentation (`VCtor`): with a split argument they are
stated with its parts, the components `p.1`, `p.2` of a product, and for a sum one lemma per side,
on the constructor at an injection (`Tm.Poly.map_app_inl` for `Tm.app (Sum.inl t) arg`). An
argument with a structure in two variables is mapped by `Occ₂.map`, in the premise's variable by
`f` and in the occurrences by the map of the type's leaf, which `simp` computes through the
combinators (`Occ₂.map_comp`, …); its members are those of its structure in the holes alone, the
occurrences constant (`xStruct`), and through its structure in the occurrences, as for a nested
argument: two disjuncts, whose positions are the structure's by definition. Across a sum these
structures read as instances agree with it only after cases on the value, and the two disjuncts
are its members in each variable, `Occ₂.MemX` and `∃ t, Occ₂.MemY o t y ∧ …`, which `simp`
computes through the combinators. Without a hole (in a block, at one type after cases on the
positions), there are no members in the holes: the one disjunct of the occurrences, the other
refuted in the proof by `simp`. With indices, at one index after cases, the rules are the same,
at the type of the members (`mixPlain`); at several indices of a family, the map is `IOcc₂.map`
with the map of the family's leaf at each index, and a member in the occurrences is a pair with
its index (`IOcc₂.MemY`). A nested argument of a family at one index only after cases on its
positions has its members by `IPolyIso.Mem`, as at several indices: the cases on the positions of
the layer do not see the cases that bring them to one index (the recursor's `bridgeIH`). -/

/-- `e`, built at the premises `H`, their instances and `X`, at the primed premises `H'`, their
instances and `Y`, and the primed universes: the second instantiation of `PolyMap`. -/
def polyPrime (P : Poly) (X Y e : Expr) : Expr :=
  let e := e.replaceFVars (P.Hs ++ P.insts ++ #[X]) (P.Hs' ++ P.insts' ++ #[Y])
  P.prime (e.instantiateLevelParams [P.fresh[0]!] [P.lx'])

/-- `Tₘ.Poly.instPolyIso premises idx`, the instance of the `m`-th type at its index arguments. -/
def polyIsoOf (P : Poly) (m : Nat) (idx : Array Expr) : MetaM Expr := do
  return mkAppN (← polyConst (ctx.tyName m ++ `Poly ++ `instPolyIso)) (P.premises ++ idx)

/-- The functor of an instance `PolyIso F Sh Pos`, eta-reduced. -/
def isoFun (inst : Expr) : MetaM Expr := do
  return (← whnfR (← inferType inst)).getAppArgs[0]!.eta

/-- `Occ.ofIso (fun X => Tₘ (H X) idx)`: the `m`-th type at its index arguments as a leaf. -/
def polyLeaf (P : Poly) (m : Nat) (idx : Array Expr) : MetaM Expr := do
  let inst ← ctx.polyIsoOf P m idx
  mkAppOptM ``Codata.Occ.ofIso #[← isoFun inst, none, none, inst]

/-- The type `Tₘ ps idx` of a recursive argument, as `m` and `idx`. -/
def polyRecType (ty : Expr) : MetaM (Nat × Array Expr) := do
  let e ← whnfOcc ty
  let args := e.getAppArgs
  let some m := ctx.types.findIdx? (e.getAppFn.isConstOf ·.name)
    | throwError "internal error: not a type being defined{indentExpr ty}"
  return (m, args.extract ctx.params.size args.size)

/-- The parts of a value `y` of a template without sums: its projections. -/
partial def tplProjs : Tpl → Expr → MetaM (Array Expr)
  | .part _, y => pure #[y]
  | .prod l r, y => do
    return (← tplProjs l (← mkAppM ``Prod.fst #[y])) ++ (← tplProjs r (← mkAppM ``Prod.snd #[y]))
  | .sum .., _ => throwError "internal error: projections through a sum"

/-- A value of type `D` of the template `t` along the alternatives `choices` from the `ci`-th:
a local variable `name` for a template without sums, with its projections as its parts; through
a sum, its injection, of the value of the alternative taken; a pair of values otherwise. `k`
receives the value, its parts, the local variables and the next position in `choices`. -/
partial def withTplArg (choices : Array Bool) (t : Tpl) (name : Name) (bi : BinderInfo)
    (D : Expr) (ci : Nat) (k : Expr → Array Expr → Array Expr → Nat → TermElabM α) :
    TermElabM α := do
  if !t.hasSum then
    return ← withLocalDecl name bi D fun y => do k y (← tplProjs t y) #[y] ci
  let D ← whnfOcc D
  let (A, B) := (D.appFn!.appArg!, D.appArg!)
  match t with
  | .prod l r =>
    withTplArg choices l (name.appendAfter "_fst") .default A ci fun x px lx ci =>
      withTplArg choices r (name.appendAfter "_snd") .default B ci fun y py ly ci => do
        k (← mkAppOptM ``Prod.mk #[A, B, x, y]) (px ++ py) (lx ++ ly) ci
  | .sum l r _ _ =>
    if choices[ci]! then
      withTplArg choices l (name.appendAfter "_inl") .default A (ci + 1) fun x px lx ci => do
        k (← mkAppOptM ``Sum.inl #[A, B, x]) px lx ci
    else
      withTplArg choices r (name.appendAfter "_inr") .default B (ci + 1) fun x px lx ci => do
        k (← mkAppOptM ``Sum.inr #[A, B, x]) px lx ci
  | .part _ => throwError "internal error: a part with a sum"

/-- Run `k` on the arguments of the real constructor of `v` as those of `Tₘ.c` at the premises
applied to `X`: the occurrences `Tₘ params idx` become `Tₘ (H X) idx`, the holes `H X`; a split
argument down to the alternatives of `v` (`withTplArg`). `k` receives the local variables, the
arguments of the real constructor, those of `v`, and the substitution of the latter (of the
analysis' arguments of `v`) and of the holes. -/
def withPolyVArgs (P : Poly) (X : Expr) (v : VCtor)
    (k : Array Expr → Array Expr → Array Expr → (Expr → Expr) → TermElabM α) :
    TermElabM α := do
  let c := ctx.ctors[v.real]!
  let L ← ctx.tLvl
  let tys ← (Array.range ctx.types.size).mapM fun m => ctx.constWith (ctx.tyName m) []
  let ps := ctx.polyParams P P.Hs X
  let rec go (i ci : Nat) (reals vals locals : Array Expr) : TermElabM α := do
    if h : i < c.args.size then
      let a := c.args[i]
      let ty := ctx.replaceOccU (a.type.replaceFVars (c.fvars.extract 0 i) reals)
        (fun m idx => mkAppN tys[m]! (ps ++ idx)) L
      withTplArg v.choices v.tpls[i]! a.name a.bi (P.subX P.Hs X ty) ci fun y py ly ci =>
        go (i + 1) ci (reals.push y) (vals ++ py) (locals ++ ly)
    else k locals reals vals fun e => P.subX P.Hs X (e.replaceFVars v.ctor.fvars vals)
  go 0 0 #[] #[] #[]

/-- `e` under existentials over `zs`: `∃ z₁ z₂, e`. -/
def mkExistsOver (zs : Array Expr) (e : Expr) : MetaM Expr :=
  zs.foldrM (init := e) fun z b => do mkAppM ``Exists #[← mkLambdaFVars #[z] b]

/-- `⟨w, pf⟩` for the existential `ty`, a membership unfolded first. The type of `pf` is the
expected one up to unfolding, which the kernel checks. -/
def exIntro (ty w pf : Expr) : MetaM Expr := do
  let .app (.app (.const ``Exists [u]) α) p ← whnfD ty
    | throwError "internal error: not an existential{indentExpr ty}"
  return mkApp4 (.const ``Exists.intro [u]) α p w pf

/-- `⟨w₁, …, wₙ, pf⟩` for the existentials `ty`. -/
partial def exIntros (ty : Expr) (ws : Array Expr) (pf : Expr) : MetaM Expr := do
  let some w := ws[0]? | return pf
  let .app (.app (.const ``Exists _) _) p ← whnfD ty
    | throwError "internal error: not an existential{indentExpr ty}"
  exIntro ty w (← exIntros (mkApp p w).headBeta (ws.extract 1 ws.size) pf)

/-- The `j`-th of the `n` disjuncts of the right-nested disjunction `D`. -/
def orAt (D : Expr) (n j : Nat) : Expr := Id.run do
  let mut D := D
  for _ in [0:j] do D := D.appArg!
  return if j + 1 < n then D.appFn!.appArg! else D

/-- A proof of the right-nested disjunction `D` of `n` disjuncts from a proof of its `j`-th. -/
partial def orIntro (D : Expr) (n j : Nat) (pf : Expr) : Expr :=
  if n ≤ 1 then pf
  else
    let (A, B) := (D.appFn!.appArg!, D.appArg!)
    if j == 0 then mkApp3 (mkConst ``Or.inl) A B pf
    else mkApp3 (mkConst ``Or.inr) A B (orIntro B (n - 1) (j - 1) pf)

/-- Cases on a hypothesis `h` that is a right-nested disjunction of `n` disjuncts (`False` for
none): a goal per disjunct, with its hypothesis. -/
partial def splitOr (g : MVarId) (h : FVarId) (n : Nat) : MetaM (Array (MVarId × FVarId)) := do
  if n == 0 then
    unless (← g.cases h).isEmpty do throwError "internal error: cases on `False`"
    return #[]
  if n == 1 then return #[(g, h)]
  let #[l, r] ← g.cases h | throwError "internal error: cases on a disjunction"
  return #[(l.mvarId, l.fields[0]!.fvarId!)] ++ (← splitOr r.mvarId r.fields[0]!.fvarId! (n - 1))

/-- The constructor `n` of an inductive family at the type `ty`: its explicit arguments `args`,
the others by unification. -/
def mkCtorAt (n : Name) (ty : Expr) (args : Array Expr) : MetaM Expr := withUnfolding do
  let f ← mkConstWithFreshMVarLevels n
  let (xs, bis, rty) ← forallMetaTelescope (← inferType f)
  unless ← isDefEq rty ty do throwError "internal error: `{n}` is not of type{indentExpr ty}"
  let ex := (xs.zip bis).filterMap fun (x, bi) => if bi.isExplicit then some x else none
  for x in ex, a in args do
    unless ← isDefEq x a do throwError "internal error: ill-typed argument of `{n}`{indentExpr a}"
  let r ← instantiateMVars (mkAppN f xs)
  if r.hasMVar then throwError "internal error: undetermined arguments of `{n}`{indentExpr r}"
  return r

/-- `n`, or `n` with `₀` appended until it is not one of `taken`. -/
partial def avoidName (taken : Array Name) (n : Name) : Name :=
  if taken.contains n then avoidName taken (n.appendAfter "₀") else n

/-- The first of `names` that is not the name of an argument of `c`, for a binder of a lemma
about `c`; when all are, the first with `₀` appended (`avoidName`). -/
def freeName (c : Ctor) (names : List Name) : Name :=
  let taken := c.args.map (·.name)
  (names.find? fun n => !taken.contains n).getD (avoidName taken names.head!)

/-- The type and index arguments at an index `i` of the presentation that is a constructor
application: the family at `projs i`, or in a block the type of the constructor of
`Blk.Poly.Ix` with its arguments. -/
def polyIdxType (P : Poly) (i : Expr) : MetaM (Nat × Array Expr) := do
  if !ctx.isBlock then return (0, ← ctx.projs i)
  let n := ctx.polyName "Ix"
  let some m := (Array.range ctx.types.size).find? fun m =>
      i.isAppOf (n ++ Name.mkSimple (ctx.shortName m))
    | throwError "internal error: not an index of a type of the block{indentExpr i}"
  return (m, i.getAppArgs.extract P.consts.size i.getAppNumArgs)

/-- The plain structure in two variables of the argument `f`, at the universe `lvl` under the
substitution `σ`, with the type and index arguments of its positions in `Y`: without indices the
structure itself, with indices the plain one at one index (`MixField.flat?`); `none` for an
indexed structure with positions at several indices. -/
def mixPlain (P : Poly) (f : MixField) (lvl : Level) (σ : Expr → Expr) :
    MetaM (Option (Expr × Nat × Array Expr)) := do
  if !ctx.idxed then return some (ctx.mixOccAt f lvl σ, 0, #[])
  let some (o₂, i₀) := f.flat? | return none
  let (m, idx) ← ctx.polyIdxType P (σ i₀)
  return some (substLevel ctx.uT lvl (σ o₂), m, idx)

/-- The family of the types at the premises `Hs` and `X` on the index of the presentation,
`fun j => T (H X) (ι j)`, curried as the children of a layer (`polyLayFam`). -/
def polyTFam (P : Poly) (Hs : Array Expr) (X : Expr) : TermElabM Expr := do
  ctx.polyLayFam P Hs X (mkAppN (← ctx.constWith ctx.name []) (ctx.polyParams P Hs X))

/-- `Tₘ (H X) idx`, the `m`-th type at the premises and its index arguments. -/
def polyTyAt (P : Poly) (X : Expr) (m : Nat) (idx : Array Expr) : MetaM Expr := do
  return mkAppN (← ctx.constWith (ctx.tyName m) []) (ctx.polyParams P P.Hs X ++ idx)

/-- `PolyIso.Mem (fun X => T (H X) idx) x t`, membership in a member `t` of the family at the
index `j` of the presentation, its index arguments `projs j`. -/
def polyMemAt (P : Poly) (X x j t : Expr) : TermElabM Expr := do
  let inst ← ctx.polyIsoOf P 0 (← ctx.projs j)
  withUnfolding <| mkAppOptM ``Codata.PolyIso.Mem #[← isoFun inst, none, none, inst, X, x, t]

/-- `Occ.map (Occ.ofIso (fun X => Tₘ (H X) idx)) (Occ.ofIso (fun X => Tₘ (H' X) idx)) f x`. -/
def polyLeafMap (P : Poly) (X Y f : Expr) (m : Nat) (idx : Array Expr) (x : Expr) :
    TermElabM Expr := do
  let o ← ctx.polyLeaf P m idx
  mkAppOptM ``Codata.Occ.map #[none, none, none, o, none, polyPrime P X Y o, X, Y, f, x]

/-- The map of a nested argument `y` with structure `n`, `σ` the substitution of the analysis'
arguments: the map of its structure, at the members the map of the leaf of their type. In a
block, through the instance of the argument's type as a functor of its members, which are of one
type. -/
def polyNestMap (P : Poly) (X Y f : Expr) (a : ArgInfo) (n : Nest) (σ : Expr → Expr) (y : Expr) :
    TermElabM Expr := do
  let L ← ctx.tLvl
  let o := P.subX P.Hs X (ctx.nestAt n L σ)
  let TX := mkAppN (← ctx.constWith ctx.name []) (ctx.polyParams P P.Hs X)
  if !ctx.idxed then
    let g ← lam `t TX fun t => ctx.polyLeafMap P X Y f 0 #[] t
    return ← mkAppOptM ``Codata.Occ.map
      #[none, none, none, o, none, polyPrime P X Y o, none, none, g, y]
  if !ctx.isBlock then
    let g ← lam `p ctx.J fun p => do
      let idx ← ctx.projs p
      lam `t (mkAppN TX idx) fun t => ctx.polyLeafMap P X Y f 0 idx t
    return ← mkAppOptM ``Codata.IOcc.map
      #[none, none, none, none, none, o, none, polyPrime P X Y o, none, none, g, y]
  let nm ← ctx.nestMem a n σ
  let nm := { nm with fn := P.subX P.Hs X nm.fn, inst := P.subX P.Hs X nm.inst }
  if nm.idx?.isNone then
    throwLimit m!"the positions of the nested argument `{a.name}` are at several types of the \
      block"
  let elem := P.subX P.Hs X nm.elem
  let (m, idx) ← ctx.polyRecType elem
  let oF ← mkAppOptM ``Codata.Occ.ofIso #[← isoFun nm.inst, none, none, nm.inst]
  let g ← lam `t elem fun t => ctx.polyLeafMap P X Y f m idx t
  mkAppOptM ``Codata.Occ.map #[none, none, none, oF, none, polyPrime P X Y oF, none, none, g, y]

/-- `Tₘ.F (H X) Tₘ idx` of `dtor_c` at the arguments `ys`, with the proof of `dtor_c`, and the
fixpoint `T.Poly.fix` at `X`, its layer `toL` and its constructor `ctor ∘ ofL` (a function on
the index of the presentation with indices), with the proof that `d` undoes it if asked. -/
structure PolyCtorData where
  dtorc : Expr
  fc : Expr
  M : Expr
  toL : Expr
  ctorL : Expr
  hc? : Option Expr
  /-- The index of `Tₘ.c ys` in the presentation, with indices. -/
  i? : Option Expr

/-- The data of `PolyCtorData` for `c` at the arguments `ys` at `X`, with the proof that `d`
undoes `ctor ∘ ofL` when `inv`. -/
def polyCtorData (P : Poly) (X : Expr) (c : Ctor) (ys : Array Expr) (σ : Expr → Expr)
    (inv : Bool) : TermElabM PolyCtorData := do
  let L ← ctx.tLvl
  let pX := ctx.polyParams P P.Hs X
  let T := mkAppN (← ctx.constWith ctx.name []) pX
  let yL := [(P.fresh[2]!, L)]
  let M ← ctx.polyFixAt P [] P.Hs P.insts X
  let dtorc := mkAppN (← ctx.constWith (ctx.tName' c "dtor_" "") []) (pX ++ ys)
  let some (_, _, fc) := (← inferType dtorc).eq?
    | throwError "internal error: `dtor_{c.name}` is not an equation"
  let rwTac : TermElabM (TSyntax `tactic) := do
    `(tactic| rw [$(mkCIdent ctx.dtor_ctor):ident, $(mkCIdent (ctx.polyName "toL_ofL")):ident]
      <;> rfl)
  if !ctx.idxed then
    let toL ← lam `y (← ctx.polyF P X T L) fun y => ctx.polyAt P "toL" yL #[X, T, y]
    let ctorL ← lam `z (← ctx.polyLay P X T) fun z => do
      return mkAppN (← ctx.constWith ctx.ctor []) (pX.push (← ctx.polyAt P "ofL" yL #[X, T, z]))
    let hcTy ← withLocalDeclD `z (← ctx.polyLay P X T) fun z => do
      let d := mkApp toL (mkAppN (← ctx.constWith ctx.dtor []) (pX.push (mkApp ctorL z)))
      mkForallFVars #[z] (← mkEq (← Core.betaReduce d) z)
    let hc? ← if inv then some <$> withUnfolding (proveOn hcTy (← rwTac)) else pure none
    return { dtorc, fc, M, toL, ctorL, hc?, i? := none }
  let idxAt (i : Expr) : MetaM (Array Expr) := do ctx.projs (← ctx.polyIota P P.Hs X i)
  let i ← σ <$> ctx.polyIdx P c.idx
  let toL ← lam `y (← inferType fc) fun y => ctx.polyAt P "toL" yL #[X, T, i, y]
  let ctorL ← lam `i P.I (bi := .implicit) fun i => do
    lam `z (← ctx.polyILay P X T i) fun z => do
      return mkAppN (← ctx.constWith ctx.ctor [])
        (pX ++ (← idxAt i) |>.push (← ctx.polyAt P "ofL" yL #[X, T, i, z]))
  let hcTy ← withLocalDecl `i .implicit P.I fun i => do
    withLocalDeclD `z (← ctx.polyILay P X T i) fun z => do
      let d ← ctx.polyAt P "toL" yL #[X, T, i, mkAppN (← ctx.constWith ctx.dtor [])
        (pX ++ (← idxAt i) |>.push (mkApp2 ctorL i z))]
      mkForallFVars #[i, z] (← mkEq (← Core.betaReduce d) z)
  let hc? ← if inv then some <$> withUnfolding (proveOn hcTy (← rwTac)) else pure none
  return { dtorc, fc, M, toL, ctorL, hc?, i? := some i }

/-- `M.d (Tₘ.c ys) = toL (F.c ys)`, from `dtor_c`, with the left-hand side `M.d (Tₘ.c ys)`. -/
def PolyCtorData.dEq (d : PolyCtorData) (capp : Expr) : MetaM (Expr × Expr) := do
  let dD ← match d.i? with
    | some i => mkAppOptM ``Codata.IPolyFix.d #[none, none, none, none, none, none, d.M, i, capp]
    | none => mkAppOptM ``Codata.PolyFix.d #[none, none, none, none, none, none, none, d.M, capp]
  let hD ← mkCongrArg d.toL d.dtorc
  return (dD, ← mkExpectedTypeHint hD (← mkEq dD (d.toL.beta #[d.fc])))

/-- `Tₘ.Poly.map_c`. -/
def genPolyMapRule (P : Poly) (mi : Nat) : TermElabM Unit := do
  let v := P.vc[mi]!
  let c := v.ctor
  let cr := ctx.ctors[v.real]!
  withLocalDecl (freeName c [`X]) .implicit (mkSort P.lx.succ) fun X => do
  withLocalDecl (freeName c [`Y]) .implicit (mkSort P.lx'.succ) fun Y => do
  withLocalDeclD (freeName c [`f, `g, `h]) (← mkArrow X Y) fun f => do
  ctx.withPolyVArgs P X v fun locals reals ys σ => do
  let σ₀ (e : Expr) := e.replaceFVars c.fvars ys
  let prime := polyPrime P X Y
  let args' ← (c.args.zip ys).zipIdx.mapM fun ((a, y), k) => do
    if let some fd := P.fields[mi]!.find? (·.k == k) then
      let o := σ fd.occ
      return ← mkAppOptM ``Codata.Occ.map #[none, none, none, o, none, prime o, X, Y, f, y]
    if let some fd := (P.mixAt mi).find? (·.k == k) then
      -- In `X` by `f`, in the occurrences by the map of the type's leaf; with indices, of the
      -- leaf of the type at each index of the presentation.
      let L ← ctx.tLvl
      if let some (o, m, idx) ← ctx.mixPlain P fd L σ then
        let g ← lam `t (← ctx.polyTyAt P X m idx) fun t => ctx.polyLeafMap P X Y f m idx t
        return ← mkAppM ``Codata.Occ₂.map #[o, prime o, f, g, y]
      -- At several indices of a family: the map of the family's leaf at each index.
      if ctx.isBlock then
        throwLimit m!"the positions of the nested argument `{a.name}` are at several types of the \
          block"
      let o := ctx.mixOccAt fd L σ
      let YF ← ctx.polyTFam P P.Hs X
      let YF' := prime YF
      let g ← lam `j P.I fun j => do
        let idx ← ctx.projs j
        lam `t (← ctx.polyTyAt P X 0 idx) fun t => ctx.polyLeafMap P X Y f 0 idx t
      return ← mkAppOptM ``Codata.IOcc₂.map
        #[none, none, none, none, none, none, o, none, prime o, X, YF, Y, YF', f, g, y]
    match a.kind with
    | .data => pure y
    | .plain _ =>
      let (m, idx) ← ctx.polyRecType (← inferType y)
      ctx.polyLeafMap P X Y f m idx y
    | .fn n => withReducible <| forallBoundedTelescope (← inferType y) n fun zs body => do
      let (m, idx) ← ctx.polyRecType body
      mkLambdaFVars zs (← ctx.polyLeafMap P X Y f m idx (mkAppN y zs))
    | .nest n => ctx.polyNestMap P X Y f a n σ₀ y
  let Tc ← ctx.constWith (ctx.tCtor cr) []
  let capp := mkAppN Tc (ctx.polyParams P P.Hs X ++ reals)
  let lhs ← ctx.polyLeafMap P X Y f cr.owner (cr.uidx.map σ) capp
  let rhs ← applyVCtor v (mkAppN (P.prime Tc) (ctx.polyParams P P.Hs' Y)) fun vi _ =>
    pure args'[vi]!
  let ty ← inferType rhs
  -- `M.map M' f (Tₘ.c ys) = c' ⟨(M.d (Tₘ.c ys)).1, …⟩` with `c' = ctor ∘ ofL` at `H'`, then
  -- `dtor_c` in it.
  let d ← ctx.polyCtorData P X cr reals σ (inv := true)
  let some hc := d.hc? | throwError "internal error: no inverse of the layer"
  let eqA ← withUnfolding <| match d.i? with
    | some i => mkAppOptM ``Codata.IPolyFix.map_eq_of_d #[none, none, none, none, none, none,
        d.M, none, none, prime d.M, f, prime d.ctorL, prime hc, i, capp]
    | none => mkAppOptM ``Codata.PolyFix.map_eq_of_d #[none, none, none, none, none, none,
        none, d.M, none, none, prime d.M, f, prime d.ctorL, prime hc, capp]
  let (dD, hD) ← d.dEq capp
  let some (_, _, rA) := (← inferType eqA).eq? | throwError "internal error: not an equation"
  let abs ← kabstract rA dD
  unless abs.hasLooseBVars do throwError "internal error: no layer in{indentExpr rA}"
  let pf ← mkEqTrans eqA (← mkCongrArg (.lam `d (← inferType dD) abs .default) hD)
  -- The right-hand side is the computed one by definition, which the kernel checks.
  let noIdx (o : Expr) := mkAppN o.getAppFn (o.getAppArgs.modify 0 DiscrTree.mkNoindexAnnotation)
  let lhs := mkAppN lhs.getAppFn (lhs.getAppArgs.modify 3 noIdx |>.modify 5 noIdx)
  let stmt := mkApp3 (.const ``Eq [← getLevel ty]) ty lhs rhs
  let xs := P.consts ++ P.Hs ++ P.Hs' ++ P.SR ++ P.insts ++ P.insts' ++ #[X, Y, f] ++ locals
  let (type, value) ← withBinderInfo (P.consts ++ P.Hs ++ P.Hs' ++ P.SR) .implicit do
    return (← mkForallFVars xs stmt, ← mkLambdaFVars xs pf)
  let n := ctx.tyName c.owner ++ `Poly ++ Name.mkSimple ("map_" ++ c.name.toString)
  addThm n (← ctx.levelParamsOf P.fresh #[type]) type value ctx.types[c.owner]!.ref
  addSimp n

/-- The disjunct of a nested argument `y` with structure `n` in `Tₘ.Poly.mem_c`:
`∃ t, Mem G t y ∧ Mem (fun X => Tₘ (H X) idx) x t`, or on the packed index
`∃ p t, IPolyIso.Mem G p t y ∧ …` when its positions are at several indices, also when they are
at one index only after cases on them, which the cases on the positions of a layer do not see;
with `bridge`, for an argument presented by its plain structure at one index (`MixField.flat?`),
by `PolyIso.Mem` at that index then too. -/
def polyNestMem (P : Poly) (X x : Expr) (c : Ctor) (a : ArgInfo) (n : Nest) (σ : Expr → Expr)
    (y : Expr) (bridge := false) : TermElabM Expr := do
  let nm ← ctx.nestMem a n σ bridge (anySum := bridge)
  let sub := P.subX P.Hs X
  let nm : NestMem := { nm with fn := sub nm.fn, inst := sub nm.inst, elem := sub nm.elem }
  let memT (t : Expr) : TermElabM Expr := do
    let (m, idx) ← ctx.polyRecType (← inferType t)
    let inst ← ctx.polyIsoOf P m idx
    withUnfolding <| mkAppOptM ``Codata.PolyIso.Mem #[← isoFun inst, none, none, inst, X, x, t]
  if nm.idx?.isSome then
    return ← withLocalDeclD (freeName c [`t]) nm.elem fun t => do
      mkExistsOver #[t] (mkAnd (← ctx.memProp nm y t #[]) (← memT t))
  if ctx.isBlock then
    throwLimit m!"the positions of the nested argument `{a.name}` are at several types of the \
      block"
  withLocalDeclD (freeName c [`p]) ctx.J fun p => do
  withLocalDeclD (freeName c [`t]) (mkApp nm.elem p).headBeta fun t => do
    let im ← withUnfolding <| mkAppOptM ``Codata.IPolyIso.Mem
      #[none, nm.fn, none, none, none, nm.inst, nm.elem, p, t, y]
    mkExistsOver #[p, t] (mkAnd im (← memT t))

/-- Does the structure in two variables `o` go through a sum? Then its membership is stated by
`Occ₂.MemX` and `Occ₂.MemY`. -/
def hasSum₂ (o : Expr) : Bool := (o.find? (·.isConstOf ``Codata.Occ₂.sum)).isSome

/-- The structure in `X` alone of a structure in two variables `o`, the occurrences at the
constant `Y₀` and the variable at `lx`: what its contents in `X` are the members of, read as an
instance (`isoOf`). Its positions and contents are those of `o` in `X` by definition, unless `o`
goes through a sum (`hasSum₂`). -/
partial def xStruct (o Y₀ : Expr) (lx : Level) : MetaM Expr := do
  let ex ← explicitArgs o
  let const (A : Expr) : MetaM Expr := do
    return mkApp (← constAt ``Codata.Occ.const [(`u, lx), (`v, ← typeLevel A)]) A
  let under (n : Name) : MetaM Expr := do
    let f ← withLocalDeclD `x ex[0]! fun x => do
      mkLambdaFVars #[x] (← xStruct (ex[1]!.beta #[x]) Y₀ lx)
    mkAppM n #[ex[0]!, f]
  match o.getAppFn.constName? with
  | some ``Codata.Occ₂.ofX => return ex[0]!
  | some ``Codata.Occ₂.ofY =>
    let GY := (← whnfR (← inferType ex[0]!)).getAppArgs[2]!
    const (← Core.betaReduce (mkApp GY Y₀))
  | some ``Codata.Occ₂.const => const ex[0]!
  | some ``Codata.Occ₂.prod =>
    mkAppM ``Codata.Occ.prod #[← xStruct ex[0]! Y₀ lx, ← xStruct ex[1]! Y₀ lx]
  | some ``Codata.Occ₂.sum =>
    mkAppM ``Codata.Occ.sum #[← xStruct ex[0]! Y₀ lx, ← xStruct ex[1]! Y₀ lx]
  | some ``Codata.Occ₂.comp => mkAppM ``Codata.Occ.comp #[ex[0]!, ← xStruct ex[1]! Y₀ lx]
  | some ``Codata.Occ₂.pi => under ``Codata.Occ.pi
  | some ``Codata.Occ₂.piP => under ``Codata.Occ.piP
  | some ``Codata.Occ₂.sigma => under ``Codata.Occ.sigma
  | _ => throwError "internal error: unexpected structure in two variables{indentExpr o}"

/-- Close the goal `g` by `simp` with the default `simp` set: the refutation of a membership
without positions. -/
def simpClose (g : MVarId) : TermElabM Unit := do
  let sctx ← Simp.mkContext (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r?, _) ← simpGoal g sctx #[← Simp.getSimprocs]
  if let some (_, g) := r? then
    throwError "internal error: `simp` did not close{indentD (MessageData.ofGoal g)}"

/-- `Tₘ.Poly.mem_c`. -/
def genPolyMemRule (P : Poly) (mi : Nat) : TermElabM Unit := do
  let vc := P.vc[mi]!
  let c := vc.ctor
  let cr := ctx.ctors[vc.real]!
  let L ← ctx.tLvl
  withLocalDecl (freeName c [`X]) .implicit (mkSort P.lx.succ) fun X => do
  withLocalDeclD (freeName c [`x, `y, `z]) X fun x => do
  ctx.withPolyVArgs P X vc fun locals reals ys σ => do
  let σ₀ (e : Expr) := e.replaceFVars c.fvars ys
  let memOf (inst y : Expr) : MetaM Expr := do
    withUnfolding <| mkAppOptM ``Codata.PolyIso.Mem #[← isoFun inst, none, none, inst, X, x, y]
  let TX := mkAppN (← ctx.constWith ctx.name []) (ctx.polyParams P P.Hs X)
  let mixOf (k : Nat) : Option MixField := (P.mixAt mi).find? (·.k == k)
  -- An argument with a structure in two variables but no parameter (in a block, at a type of the
  -- block after cases on its positions) has no members in `X`.
  let vacuous (fd : MixField) : Bool := (ctx.outside P.holes fd.arg.type).isEmpty
  -- Its disjunct for these, left out of the statement and refuted in the proof (`simp`).
  let vacuousX (k : Nat) : TermElabM (Option (Expr × Expr)) := do
    let some fd := mixOf k | return none
    if !vacuous fd then return none
    let some (o, m, idx) ← ctx.mixPlain P fd L σ | return none
    let y := ys[k]!
    let dX ← if hasSum₂ o then
        withUnfolding <| mkAppOptM ``Codata.Occ₂.MemX #[none, none, none, none, X,
          ← ctx.polyTyAt P X m idx, o, x, y]
      else memOf (← isoOf (← xStruct o (← ctx.polyTyAt P X m idx) P.lx) .plain) y
    return some (dX, ← proveHere (mkNot dX) simpClose)
  -- The disjuncts, with their arguments; an argument with a structure in two variables has two,
  -- its members in `X` (`false`) and the members of its occurrences (`true`).
  let ds ← (c.args.zip ys).zipIdx.flatMapM fun ((a, y), k) => do
    if let some fd := P.fields[mi]!.find? (·.k == k) then
      return #[((k, false), ← memOf (← isoOf (σ fd.occ) .plain) y)]
    if let some fd := mixOf k then
      -- The plain structure, at the type of its positions in `Y`: as without indices.
      if let some (o, m, idx) ← ctx.mixPlain P fd L σ then
        let TT ← ctx.polyTyAt P X m idx
        -- Across a sum the structures in each variable alone, read as instances, agree with the
        -- structure in two variables only after cases on the value: membership by the latter.
        if hasSum₂ o then
          let memY ← withLocalDeclD (freeName c [`t]) TT fun t => do
            let mY ← withUnfolding <| mkAppOptM ``Codata.Occ₂.MemY
              #[none, none, none, none, X, TT, o, t, y]
            mkExistsOver #[t] (mkAnd mY (← memOf (← ctx.polyIsoOf P m idx) t))
          if vacuous fd then return #[((k, true), memY)]
          return #[((k, false), ← withUnfolding <| mkAppOptM ``Codata.Occ₂.MemX
              #[none, none, none, none, X, TT, o, x, y]),
            ((k, true), memY)]
        let oX ← xStruct o TT P.lx
        let dY ← ctx.polyNestMem P X x c fd.arg fd.nest σ₀ y (bridge := true)
        if vacuous fd then return #[((k, true), dY)]
        return #[((k, false), ← memOf (← isoOf oX .plain) y), ((k, true), dY)]
      -- At several indices of a family: by the indexed structure, a member in `Y` with its index.
      if ctx.isBlock then
        throwLimit m!"the positions of the nested argument `{a.name}` are at several types of the \
          block"
      let o := ctx.mixOccAt fd L σ
      let YF ← ctx.polyTFam P P.Hs X
      let memY ← withLocalDeclD (freeName c [`t]) (← mkAppM ``Sigma #[YF]) fun t => do
        let mY ← withUnfolding <| mkAppOptM ``Codata.IOcc₂.MemY
          #[none, none, none, none, none, none, X, YF, o, t, y]
        mkExistsOver #[t]
          (mkAnd mY (← ctx.polyMemAt P X x (← mkAppM ``Sigma.fst #[t]) (← mkAppM ``Sigma.snd #[t])))
      return #[((k, false), ← withUnfolding <| mkAppOptM ``Codata.IOcc₂.MemX
          #[none, none, none, none, none, none, X, YF, o, x, y]),
        ((k, true), memY)]
    match a.kind with
    | .data => return #[]
    | .plain _ =>
      let (m, idx) ← ctx.polyRecType (← inferType y)
      return #[((k, false), ← memOf (← ctx.polyIsoOf P m idx) y)]
    | .fn n => withReducible <| forallBoundedTelescope (← inferType y) n fun zs body => do
      let (m, idx) ← ctx.polyRecType body
      return #[((k, false), ← mkExistsOver zs (← memOf (← ctx.polyIsoOf P m idx) (mkAppN y zs)))]
    | .nest n => return #[((k, false), ← ctx.polyNestMem P X x c a n σ₀ y)]
  let n := ds.size
  let D := if n == 0 then Lean.mkConst ``False
    else ds.pop.foldr (init := ds.back!.2) fun (_, d) acc => mkOr d acc
  let dIdx (k : Nat × Bool) : Nat := (ds.findIdx? (·.1 == k)).getD 0
  let Tc ← ctx.constWith (ctx.tCtor cr) []
  let capp := mkAppN Tc (ctx.polyParams P P.Hs X ++ reals)
  let lhs ← memOf (← ctx.polyIsoOf P cr.owner (cr.uidx.map σ)) capp
  -- `Mem x (Tₘ.c ys) ↔ (∃ q, v q = x) ∨ ∃ b r, …`, for the layer `⟨s, v, k⟩` of `F.c ys`.
  let d ← ctx.polyCtorData P X cr reals σ (inv := false)
  let lay ← whnf (d.toL.beta #[d.fc])
  let pr ← whnf lay.appArg!
  let (s, v, k) := (lay.appFn!.appArg!, pr.appFn!.appArg!, pr.appArg!)
  let (_, hD) ← d.dEq capp
  let pf₁ ← withUnfolding <| match d.i? with
    | some i => mkAppOptM ``Codata.IPolyFix.exists_val_iff
        #[none, none, none, none, none, none, d.M, i, capp, s, v, k, hD, x]
    | none => mkAppOptM ``Codata.PolyFix.exists_val_iff
        #[none, none, none, none, none, none, none, d.M, capp, s, v, k, hD, x]
  let some (_, AB) := (← inferType pf₁).iff? | throwError "internal error: not an equivalence"
  -- The positions of the layer: those of the fields, of the recursive arguments.
  let hole ← if ctx.idxed then ctx.packFam (mkAppN (← ctx.constWith ctx.name [])
      (ctx.polyParams P P.Hs X)) else pure (mkAppN (← ctx.constWith ctx.name [])
      (ctx.polyParams P P.Hs X))
  let nestToC (n : Nest) (y : Expr) : TermElabM Expr := do
    let o := P.subX P.Hs X (ctx.nestAt n L σ₀)
    if ctx.idxed then mkAppOptM ``Codata.IOcc.toC #[none, none, none, none, none, o, hole, y]
    else mkAppOptM ``Codata.Occ.toC #[none, none, none, o, hole, y]
  let YFi ← if ctx.idxed then ctx.polyTFam P P.Hs X else pure TX
  let vacs ← (P.mixAt mi).filterMapM fun fd => do
    return (← vacuousX fd.k).map fun (d, h) => (fd.k, d, h)
  let mp ← proveHere (← mkArrow AB D) fun g => do
    let (h, g) ← g.intro1
    let #[gl, gr] ← g.cases h | throwError "internal error: cases on a disjunction"
    -- A content of the layer: of a field.
    let #[sg] ← gl.mvarId.cases gl.fields[0]!.fvarId! | throwError "internal error: cases on `∃`"
    let (_, g) ← sg.mvarId.revert #[sg.fields[1]!.fvarId!]
    for sg in ← casesPos g sg.fields[0]!.fvarId! do
      let (hq, g) ← sg.mvarId.intro1
      g.withContext do
      let some fk := (P.fields[mi]!.map (·.k) ++ (P.mixAt mi).map (·.k)).find? fun k =>
          sg.ctorName == some (ctx.polyPos "P" c c.args[k]!)
        | throwError "internal error: unexpected position {sg.ctorName}"
      let D' ← instantiateMVars (← g.getType)
      if let some (_, dX, notX) := vacs.find? (·.1 == fk) then
        let (dX, notX) := (sg.subst.apply dX, sg.subst.apply notX)
        g.assign (← mkAbsurd D' (← exIntro dX sg.fields.back! (mkFVar hq)) notX)
      else
        let j := dIdx (fk, false)
        g.assign (orIntro D' n j (← exIntro (orAt D' n j) sg.fields.back! (mkFVar hq)))
    -- A content of a child.
    let #[sg] ← gr.mvarId.cases gr.fields[0]!.fvarId! | throwError "internal error: cases on `∃`"
    let (_, g) ← sg.mvarId.revert #[sg.fields[1]!.fvarId!]
    for sg in ← casesPos g sg.fields[0]!.fvarId! do
      let (hb, g) ← sg.mvarId.intro1
      g.withContext do
      let some (_, ki) := c.args.zipIdx.find? fun (a, k) =>
          (!a.kind.isData || (mixOf k).isSome) && sg.ctorName == some (ctx.polyPos "B" c a)
        | throwError "internal error: unexpected position {sg.ctorName}"
      let D' ← instantiateMVars (← g.getType)
      let mix? := mixOf ki
      let j := dIdx (ki, mix?.isSome)
      let dj := orAt D' n j
      let hb := mkFVar hb
      -- The kind of the argument: an argument with a structure in two variables is nested here.
      let kind := match mix? with
        | some fd => ArgKind.nest fd.nest
        | none => c.args[ki]!.kind
      let pf ← match kind with
        | .nest nst =>
          let q := sg.fields.back!
          let (tc, t₀) ← match mix? with
            | some fd => do
              let o := ctx.mixOccAt fd L σ
              let tc := sg.subst.apply (← toC₂ o X YFi ys[ki]!)
              let t₀ := mkApp (← mkAppM ``Prod.snd #[← mkAppM ``Sigma.snd #[tc]]) q
              if !ctx.idxed || fd.flat?.isSome then pure (tc, t₀) else
              -- At several indices, the member with its index.
              let some pidx := fd.pidx? | throwError "internal error: no index of a position"
              let j₀ := (mkApp2 (sg.subst.apply (σ pidx)) (← mkAppM ``Sigma.fst #[tc]) q).headBeta
              pure (tc, ← mkAppOptM ``Sigma.mk #[P.I, YFi, j₀, t₀])
            | none => do
              let tc := sg.subst.apply (← nestToC nst ys[ki]!)
              pure (tc, mkApp (← mkAppM ``Sigma.snd #[tc]) q)
          -- `⟨t₀, ⟨q, rfl⟩, hb⟩` for `∃ t, Mem G t y ∧ …`.
          let member (ty : Expr) : MetaM Expr := do
            let .app (.app (.const ``Exists _) _) pfun ← whnfD ty
              | throwError "internal error: not an existential{indentExpr ty}"
            let body := (mkApp pfun t₀).headBeta
            let memTy := body.appFn!.appArg!
            let .app (.app (.const ``Exists _) _) mfun ← whnfD memTy
              | throwError "internal error: not a membership{indentExpr memTy}"
            let some (_, _, r) := (mkApp mfun q).headBeta.eq?
              | throwError "internal error: not a membership{indentExpr memTy}"
            let mem ← exIntro memTy q (← mkEqRefl r)
            exIntro ty t₀ (mkApp4 (mkConst ``And.intro) memTy body.appArg! mem hb)
          let nm ← ctx.nestMem c.args[ki]! nst σ₀ (bridge := false)
          if mix?.isSome || nm.idx?.isSome then member dj
          else
            -- First the index of the position.
            let some pidx := nst.pidx? | throwError "internal error: no index of a position"
            let sub (e : Expr) := sg.subst.apply (P.subX P.Hs X (substLevel ctx.uT L (σ₀ e)))
            let p₀ := (mkApp2 (sub pidx) (← mkAppM ``Sigma.fst #[tc]) q).headBeta
            let .app (.app (.const ``Exists _) _) pfun ← whnfD dj
              | throwError "internal error: not an existential{indentExpr dj}"
            exIntro dj p₀ (← member (mkApp pfun p₀).headBeta)
        | .fn m => exIntros dj (sg.fields.extract (sg.fields.size - m) sg.fields.size) hb
        | _ => pure hb
      g.assign (orIntro D' n j pf)
  let mpr ← proveHere (← mkArrow D AB) fun g => do
    let (h, g) ← g.intro1
    for ((g, h), j) in (← splitOr g h n).zipIdx do
      g.withContext do
      let (ki, isY) := ds[j]!.1
      let a := c.args[ki]!
      let byB (g : MVarId) (args : Array Expr) (h : Expr) : MetaM Unit := g.withContext do
        let AB' ← instantiateMVars (← g.getType)
        let B := AB'.appArg!
        let b ← mkCtorAt (ctx.polyPos "B" c a) (← whnfD B).appFn!.appArg! args
        g.assign (mkApp3 (mkConst ``Or.inr) AB'.appFn!.appArg! B (← exIntro B b h))
      -- An argument with a structure in two variables: a field for its members in `X`, nested
      -- for the members of its occurrences.
      let kind := match mixOf ki, isY with
        | some fd, true => ArgKind.nest fd.nest
        | _, _ => a.kind
      match kind with
      | .data =>
        -- A field at a parameter position: a content of the layer.
        let g ← g.replaceLocalDeclDefEq h (← whnfD (← h.getType))
        let #[sg] ← g.cases h | throwError "internal error: cases on a membership"
        sg.mvarId.withContext do
        let AB' ← instantiateMVars (← sg.mvarId.getType)
        let A := AB'.appFn!.appArg!
        let q ← mkCtorAt (ctx.polyPos "P" c a) (← whnfD A).appFn!.appArg! #[sg.fields[0]!]
        sg.mvarId.assign (mkApp3 (mkConst ``Or.inl) A AB'.appArg! (← exIntro A q sg.fields[1]!))
      | .plain _ => byB g #[] (mkFVar h)
      | .fn m =>
        let mut g₁ := g
        let mut h₁ := h
        let mut zs := #[]
        for _ in [0:m] do
          let #[sg] ← g₁.cases h₁ | throwError "internal error: cases on `∃`"
          zs := zs.map sg.subst.apply |>.push sg.fields[0]!
          g₁ := sg.mvarId
          h₁ := sg.fields[1]!.fvarId!
        byB g₁ zs (mkFVar h₁)
      | .nest nst =>
        let several := (mixOf ki).isNone && (← ctx.nestMem a nst σ₀ (bridge := false)).idx?.isNone
        let mut g₁ := g
        let mut h₁ := h
        for _ in [0:if several then 2 else 1] do
          let #[sg] ← g₁.cases h₁ | throwError "internal error: cases on `∃`"
          g₁ := sg.mvarId
          h₁ := sg.fields[1]!.fvarId!
          -- With indices, a member in `Y` of a structure in two variables is a dependent pair of
          -- an index and a member there: its components.
          if ctx.idxed && (mixOf ki).any (·.flat?.isNone) then
            let #[sg'] ← g₁.cases sg.fields[0]!.fvarId!
              | throwError "internal error: cases on a member"
            g₁ := sg'.mvarId
            h₁ := (sg'.subst.apply (mkFVar h₁)).fvarId!
        let #[sg] ← g₁.cases h₁ | throwError "internal error: cases on `∧`"
        let (hm, hx) := (sg.fields[0]!.fvarId!, sg.fields[1]!.fvarId!)
        let g₂ ← sg.mvarId.withContext do
          sg.mvarId.replaceLocalDeclDefEq hm (← whnfD (← hm.getType))
        let #[sg] ← g₂.cases hm | throwError "internal error: cases on a membership"
        let hx := sg.subst.apply (mkFVar hx)
        let q := sg.fields[0]!
        let #[sg'] ← sg.mvarId.cases sg.fields[1]!.fvarId!
          | throwError "internal error: cases on the equation of a member"
        byB sg'.mvarId #[sg'.subst.apply q] (sg'.subst.apply hx)
  let pf₂ ← mkAppM ``Iff.intro #[mp, mpr]
  let pf ← mkAppM ``Iff.trans #[pf₁, pf₂]
  -- The statement is the proof's up to unfolding, which the kernel checks.
  let stmt := mkIff (mkAppN lhs.getAppFn (lhs.getAppArgs.modify 0 DiscrTree.mkNoindexAnnotation)) D
  let xs := P.consts ++ P.Hs ++ P.SR ++ P.insts ++ #[X, x] ++ locals
  let (type, value) ← withBinderInfo (P.consts ++ P.Hs ++ P.SR) .implicit do
    return (← mkForallFVars xs stmt, ← mkLambdaFVars xs pf)
  let n := ctx.tyName c.owner ++ `Poly ++ Name.mkSimple ("mem_" ++ c.name.toString)
  addThm n (← ctx.levelParamsOf P.fresh #[type]) type value ctx.types[c.owner]!.ref
  addSimp n

/-- The simp lemmas of the instances, `Tₘ.Poly.map_c` and `Tₘ.Poly.mem_c` for every constructor.
A failure is a warning: these are rolled back, and the instances stay. -/
def genPolySimp (P : Poly) : TermElabM Unit := do
  let s ← saveState
  tryCatchRuntimeEx
    (for mi in [0:P.vc.size] do
      -- Each with its own heartbeat budget, as the parts of the instances.
      let c := P.vc[mi]!.ctor
      let rule (s : String) : MessageData :=
        m!"`{ctx.tyName c.owner ++ `Poly ++ Name.mkSimple (s ++ c.name.toString)}`"
      withCurrHeartbeats <| stepPhase (rule "map_") <| ctx.genPolyMapRule P mi
      withCurrHeartbeats <| stepPhase (rule "mem_") <| ctx.genPolyMemRule P mi)
    fun e => do
      s.restore (restoreInfo := true)
      let ns ← getCurrNamespace
      let shorts := ctx.types.map fun t => m!"`{t.name.replacePrefix ns .anonymous}`"
      logWarning m!"no simp lemmas were generated for the instances of \
        {MessageData.joinSep shorts.toList ", "}; the instances are not affected.\n\
        {e.toMessageData}"

/-- Generate the instances for the holes. -/
def genPoly (holes : Array Expr) : TermElabM Unit := do
  let nh := holes.size
  let consts := ctx.params.filter (!holes.contains ·)
  let holeTys ← holes.mapM fun a => do instantiateMVars (← inferType a)
  -- The universes of the holes that change in the second instantiation (`PolyMap`): those no
  -- constant's type mentions.
  let constLvls := (← (consts ++ ctx.types.flatMap (·.idx)).foldlM (fun s c => do
    return collectLevelParams s (← instantiateMVars (← inferType c))) {}).params
  let primeable := (holeTys.foldl collectLevelParams {}).params.filter (!constLvls.contains ·)
  -- One more for the eta instance across universes.
  let fresh := ctx.freshLevels (5 + 2 * nh + primeable.size)
  let lv (i : Nat) : Level := .param fresh[i]!
  let primes := primeable.toList.zipIdx.map fun (u, j) => (u, lv (5 + 2 * nh + j))
  let P0 : Poly := {
    holes, consts, Hs := #[], Hs' := #[], Ss := #[], Rs := #[], insts := #[], insts' := #[]
    fields := #[], fresh, primes }
  -- The names of the premises, unlike those of the other parameters and of the arguments,
  -- binders of the same lemmas.
  let taken := (← consts.mapM fun p => p.fvarId!.getUserName) ++
    ctx.ctors.flatMap (·.args.map (·.name))
  let sub (s : String) (i : Nat) : Name := avoidName taken <|
    if nh == 1 then Name.mkSimple s else Name.mkSimple (s ++ Nat.toSubscriptString (i + 1))
  -- The constructors of the presentation, with their split arguments.
  ctx.withVCtors holes fun vc => do
  withLocalsN nh (fun i => return (sub "H" i, .default, ← mkArrow (mkSort (lv 0).succ) holeTys[i]!))
    fun Hs => do
  withLocalsN nh (fun i => return (sub "H'" i, .default,
      ← mkArrow (mkSort (lv 1).succ) (P0.prime holeTys[i]!))) fun Hs' => do
  withLocalsN nh (fun i => return (sub "S" i, .default, mkSort (lv (5 + 2 * i)).succ))
    fun Ss => do
  withLocalsN nh (fun i => return (sub "R" i, .default,
      ← mkArrow Ss[i]! (mkSort (lv (6 + 2 * i)).succ))) fun Rs => do
  withLocalsN nh (fun i => return (sub "inst" i, .instImplicit,
      ← mkAppM ``Codata.PolyIso #[Hs[i]!, Ss[i]!, Rs[i]!])) fun insts => do
  withLocalsN nh (fun i => return (sub "inst'" i, .instImplicit,
      ← mkAppM ``Codata.PolyIso #[Hs'[i]!, Ss[i]!, Rs[i]!])) fun insts' => do
  withLocalsN nh (fun i => return (sub "map" i, .instImplicit,
      ← mkAppOptM ``Codata.PolyMap (#[Hs[i]!, Hs'[i]!, Ss[i]!, Rs[i]!, insts[i]!, insts'[i]!].map
        some)))
    fun maps => do
  -- The fields at parameter positions, with their structures in the premises.
  let oHs ← Hs.mapM fun H => mkAppOptM ``Codata.Occ.ofIso #[some H, none, none, none]
  -- With `PolyMap Hᵢ Hᵢ` for the leaves at the premises (`withSelfMaps`).
  let fields ← withSelfMaps Hs Ss Rs insts <| vc.mapM fun v =>
    v.ctor.args.zipIdx.filterMapM fun (a, k) => do
    unless a.kind.isData do return none
    unless holes.any (a.type.containsFVar ·.fvarId!) do return none
    let o ← instantiateMVars (← fieldOcc holes oHs (lv 0) a.type)
    let oty ← whnfR (← inferType o)
    unless oty.isAppOfArity ``Codata.Occ 3 do
      throwError "internal error: unexpected occurrence structure{indentExpr oty}"
    return some ({
      k, occ := o, sh := oty.getAppArgs[0]!, pos := oty.getAppArgs[1]! } : HoleField)
  let P := { P0 with Hs, Hs', Ss, Rs, insts, insts', maps, fields, vc }
  -- With indices, the index of the presentation: in a block a new one, without the holes.
  let P ← if ctx.isBlock then
      withCurrHeartbeats <| stepPhase m!"`{ctx.polyName "Ix"}`" <| ctx.genPolyIx P
    else pure { P with I := ctx.J }
  -- The nested arguments with the holes outside the occurrences, with their structures in two
  -- variables, and with indices over the index of the presentation; in a block also those whose
  -- positions are at a type of the block only after cases on them. Of kind `.data` in the
  -- presentation.
  let mixed ← withSelfMaps Hs Ss Rs insts <| vc.mapM fun v =>
    v.ctor.args.zipIdx.filterMapM fun (a, k) => do
    let .nest n := a.kind | return none
    let outside := !(ctx.outside holes a.type).isEmpty
    if !ctx.idxed then
      if !outside then return none
      let o ← instantiateMVars (← mixOcc holes oHs (lv 0) ctx.lvl n.occ)
      let oty ← whnfR (← inferType o)
      unless oty.isAppOfArity ``Codata.Occ₂ 4 do
        throwError "internal error: unexpected structure in two variables{indentExpr oty}"
      let (sh, px, py) := (oty.getAppArgs[0]!, oty.getAppArgs[1]!, oty.getAppArgs[2]!)
      for e in [sh, px, py] do discard <| ctx.ofStructure e
      return some ({ k, occ := o, sh, px, py, arg := a, nest := n } : MixField)
    unless outside || (ctx.isBlock && (← ctx.severalIdx a.type)) do return none
    -- At one index after cases: the plain structure there; otherwise the indexed one.
    let flat? ← match ← oneIdx n.occ, ← flatOcc? ctx.lvl n.occ with
      | some (some i₀), some oF => do
        let o₂ ← instantiateMVars (← mixOcc holes oHs (lv 0) ctx.lvl oF)
        pure (some (o₂, P.toPolyIdx i₀))
      | _, _ => pure none
    let o ← match flat? with
      | some (o₂, i₀) => mkAppM ``Codata.IOcc₂.ofOcc₂ #[o₂, i₀]
      | none => instantiateMVars (← imixOcc holes oHs (lv 0) ctx.lvl P.I P.toPolyIdx n.occ)
    let oty ← whnfR (← inferType o)
    unless oty.isAppOfArity ``Codata.IOcc₂ 6 do
      throwError "internal error: unexpected indexed structure in two variables{indentExpr oty}"
    let ta := oty.getAppArgs
    let (sh, px, py) := (ta[1]!, ta[2]!, ta[3]!)
    for e in [sh, px, py, ta[4]!] do discard <| ctx.ofStructure e
    return some ({ k, occ := o, sh, px, py, arg := a, nest := n, pidx? := some ta[4]!, flat? } :
      MixField)
  let vc := vc.mapIdx fun m v =>
    let args := v.ctor.args.mapIdx fun k a =>
      if mixed[m]!.any (·.k == k) then { a with kind := .data } else a
    { v with ctor := { v.ctor with args } }
  let P := { P with mixed, vc }
  -- Each part with its own heartbeat budget, as the steps of the pipeline.
  let n (s : String) : MessageData := m!"`{ctx.polyName s}`"
  withCurrHeartbeats <| stepPhase m!"the presentation {n "S"}, {n "P"}, {n "B"}" <|
    ctx.genPolyShapes P
  if ctx.idxed then
    withCurrHeartbeats <| stepPhase m!"{n "idx"}, {n "sig"}" do
      ctx.genPolyIdx P
      ctx.genPolySig P
  withCurrHeartbeats <| stepPhase m!"the layer {n "toL"}, {n "ofL"}" <| ctx.genPolyLayer P
  withCurrHeartbeats <| stepPhase m!"the laws {n "ofL_toL"}, {n "toL_ofL"}, {n "ofL_map"}" <|
    ctx.genPolyLaws P
  withCurrHeartbeats <| stepPhase m!"the fixpoint {n "fix"}" <| ctx.genPolyFix P
  withCurrHeartbeats <| stepPhase m!"the instances" <| ctx.genPolyInstances P
  ctx.genPolySimp P

/-- Step 5: the instances of the types of a declaration that has holes. Failure is a warning,
whatever the exception (a timeout too): the declarations of this step are rolled back, and the
types stay as they are. In an open run of a `mixed_mutual` block that an outer run nests through,
it is an error instead, and so is an extra parameter of such a run that cannot vary: the outer run
needs the instances in it. -/
def deriveInstances : TermElabM Unit := do
  let ns ← getCurrNamespace
  let short (n : Name) : MessageData := m!"`{n.replacePrefix ns .anonymous}`"
  let shorts := ctx.types.map (short ·.name)
  let strict? := ctx.mix?.filter fun mx => ctx.isOpen && mx.required.any id
  let s ← saveState
  tryCatchRuntimeEx
    (withCurrHeartbeats do
      let (holes, why, byField) ← ctx.polyHoles
      if let some mx := strict? then
        for x in mx.xs, req in mx.required, o in mx.outerNames do
          if req && !holes.contains x then
            let xn := (← x.fvarId!.getDecl).userName
            unless (← whnf (← inferType x)).isSort do
              throwError "its parameter `{xn}`, standing for {short o}, is a family over the \
                index of {short o}: nesting through it needs `Codata.IPolyIso` instances, which \
                are not generated"
            throwError "its parameter `{xn}`, standing for {short o}, cannot vary: it occurs in \
              a field without an occurrence structure in it, or together with the type itself in a \
              field without a structure in both, as in two arguments of a type constructor"
      if holes.isEmpty then
        -- Said when a parameter that is a type may not vary because of a field, outside a mixed
        -- block (whose outer types are not nested through, and the open ones have their errors).
        if byField && ctx.mix?.isNone then
          let reasons := why.map fun (p, r) => m!"`{p}` occurs in {r}"
          logInfo m!"{MessageData.joinSep shorts.toList ", "} \
            get{if ctx.isBlock then "" else "s"} no `Codata.PolyIso` instance, and cannot be \
            nested through: no parameter may vary \
            ({MessageData.joinSep reasons.toList "; "})"
        return
      stepPhase m!"the analysis of the fields" (worded := true) <| ctx.genPoly holes)
    fun e => do
      if let some mx := strict? then
        let outers := (mx.outerNames.zip mx.required).filterMap fun (n, b) =>
          if b then some (short n) else none
        throwError "{MessageData.joinSep (mx.closedNames.map short).toList ", "} cannot be \
          nested through in this `mixed_mutual` block: no `Codata.PolyIso` instance was \
          generated for {MessageData.joinSep shorts.toList ", "}, the open form that \
          {MessageData.joinSep outers.toList ", "} nest{if outers.size == 1 then "s" else ""} \
          through.\n{e.toMessageData}"
      s.restore (restoreInfo := true)
      let types := if ctx.isBlock then "The types themselves are" else "The type itself is"
      logWarning m!"{MessageData.joinSep shorts.toList ", "} cannot be nested through: no \
        `Codata.PolyIso` instance was generated. {types} not affected.\n{e.toMessageData}"

end Ctx

end Codata.Gen
