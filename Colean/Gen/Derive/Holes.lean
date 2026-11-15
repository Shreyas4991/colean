import Colean.Gen.Surface
import Colean.Model.Poly
import Colean.Model.IOcc2

/-!
# Generators on `Expr`, step 5: the holes

The option `codata.deriveDetails`, under which step 5 reports its failures (it is silent by
default), the failures of step 5 (`stepPhase`, `throwLimit`), the structures of a field in the parameters
(`fieldOcc`) and of a nested argument with a parameter outside the occurrences in two variables
(`mixOcc`, with indices `imixOcc`; at one index the plain structure, `flatOcc?`), helpers for
terms built by unification (`fillArg`, `proveOn`, `rwSteps`), and the parameters that may vary,
the holes (`polyHoles`, `refineHoles`). The step is described in `Gen/Derive.lean`.
-/

open Lean Meta Elab Term

register_option codata.deriveDetails : Bool := {
  defValue := false
  descr := "report why a declared type gets no `Codata.PolyIso` instance or its instances no \
    simp lemmas, with the error itself (step 5 of the `codatatype` and `datatype` commands); \
    by default step 5 is silent, and such a type simply cannot be nested through"
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
failed, with the error itself under `set_option codata.deriveDetails true`, the option under
which step 5 reports its failures at all. -/
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

/-- The tactic `rw [steps]`, a step `(true, n)` rewriting right to left, then `rfl` on what is left
when `close`. -/
def rwSteps (steps : Array (Bool × Name)) (close := false) : TermElabM (TSyntax `tactic) := do
  let rules ← steps.mapM fun (rev, n) =>
    if rev then `(Parser.Tactic.rwRule| ← $(mkCIdent n):ident)
    else `(Parser.Tactic.rwRule| $(mkCIdent n):ident)
  if close then `(tactic| rw [$rules,*] <;> rfl) else `(tactic| rw [$rules,*])

namespace Ctx

variable (ctx : Ctx)

/-- `T.Colean.Poly.s`. -/
def polyName (s : String) : Name := .str (ctx.colean "Poly") s

/-! ### The holes -/

/-- The universes of the variables of this step, in the order of `Poly.lvls`: `x`, `x'` (of `X`
and of the second instantiation's `X'`), `y`, `y'` (of the layer's `Y` and `Y'`), the primed
universe of the last parameter, then `sᵢ`, `pᵢ` per hole (of the premises' shapes and positions).
They are the fresh ones named `fresh`, unless a field fixes the universe of the occurrences to `l`
(`fixedLvl?`, nesting through a type at one universe: `NDet (Game α)` with
`NDet : Type → Type`). Then `T.F`, `T.corec` and `T.fold` take their families in `Type l`, so the
layer's `Y` and `Y'` are at `l`, and so must be the states of `corec` or `fold` by which the
fixpoint is built (`coFix`, `inFix`, `Model/Poly.lean`): the trees of shapes, made of the
premises' shapes among others, and for `codatatype` the contents at their paths, made of their
positions and of `X`. So the premises' shapes, and for `codatatype` their positions, are in `Type`,
the one universe at most any `l`, and for `codatatype` `X` is at `l` (`X'` at `prime l`, at the
primed universes of the holes); the others stay fresh. At `l = 0`, the common case, the instances
are as general as the type allows; above, those of `datatype` need trees of shapes at `l`
(`checkStateLevel`). -/
def stepLevels (fresh : List Name) (nh : Nat) (prime : Level → Level) : Array Level :=
  let w (i : Nat) : Level := .param fresh[i]!
  match ctx.fixedLvl? with
  | none => (Array.range (5 + 2 * nh)).map w
  | some l =>
    let (x, x') := if ctx.co then (l, prime l) else (w 0, w 1)
    #[x, x', l, l, w 4] ++ (Array.range nh).flatMap fun i =>
      #[.zero, if ctx.co then .zero else w (6 + 2 * i)]

/-- Run `k` with local instances `PolyMap Hᵢ Hᵢ` for the premises `Hs` with their instances
`insts`: a leaf at the premises (`fun X => E (H₁ X) (H₂ X)`) has a `PolyMap` instance only with
those of its premises, which the analysis of a field checks (`leafOcc`). Nothing generated
mentions them. -/
def withSelfMaps (Hs Ss Rs insts : Array Expr) (k : TermElabM α) : TermElabM α :=
  withLocalsN Hs.size (fun i => return (`map, .instImplicit, ← mkAppOptM ``Codata.PolyMap
    (#[Hs[i]!, Hs[i]!, Ss[i]!, Rs[i]!, insts[i]!, insts[i]!].map some))) fun _ => k

/-- Run `k` on premises for the parameters `cands`, as the instances will have them: for each
`Hᵢ : Type x → Aᵢ` with an instance `PolyIso Hᵢ Sᵢ Rᵢ`, given to `k` as `Occ.ofIso Hᵢ`, and the
universe `x`, at the universes of the instances (`stepLevels`). For the checks of `refineHoles`
only. -/
def withCheckPremises (cands : Array Expr) (k : Array Expr → Level → TermElabM α) :
    TermElabM α := do
  let n := cands.size
  let lvls := ctx.stepLevels (ctx.freshLevels (5 + 2 * n)) n id
  let lv (i : Nat) : Level := lvls[i]!
  withLocalsN n (fun i => do
      return (`H, .default, ← mkArrow (mkSort (lv 0).succ) (← inferType cands[i]!))) fun Hs => do
  withLocalsN n (fun i => return (`S, .default, mkSort (lv (5 + 2 * i)).succ)) fun Ss => do
  withLocalsN n (fun i => return (`R, .default, ← mkArrow Ss[i]! (mkSort (lv (6 + 2 * i)).succ)))
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

end Ctx

end Codata.Gen
