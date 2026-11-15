import Colean.Gen.Command

/-!
# Generators on `Expr`: mixed blocks

*Spec.* Input: the declarations of a `mixed_mutual` block with both kinds. Output: every run
declared, the runs inside the outermost one open and then closed, as `MutualCmd.lean` describes.

1. The runs, and their names (`mixRuns`): the outermost run under the names the user wrote, a run
   inside it under `Tₘ.Open` (and `Blk.Open` for a block, whose index is `Blk.Ix`), private with
   the types; none of them declared already, and no constructor named as a generated declaration
   (`checkMixNames`).
2. The section variables of the block, and which declaration mentions which (`mixedVars`, one
   elaboration of the whole block, discarded); from these, the outer runs each run needs
   (`mixReach`), innermost first, and the runs that nest through each.
3. The index `Blk.Ix` of every run that is a block (`declareMixIx`).
4. The runs inside, from the innermost out, each declared open by the pipeline (`withCtx` with
   the run, `Gen/Front.lean`): its extra parameters stand for the outer types it needs.
5. The outermost run, by the pipeline, after the declared sorts are checked against the universes
   of the closed types (`checkMixSorts`); once its types exist, the closed types of the runs
   inside (`closeTypes`), with which its constructors, lemmas and recursors are stated
   (`Ctx.foldTy`).
6. The rest of each run inside restated at the closed types (`restateRun`): every declaration of
   its public interface, `Tₘ.Open.d` at the closed types as `Tₘ.d`, with its attributes; the
   statements are those of `Tₘ.Open.d` at the closed families, written with the closed
   declarations (`foldClosed`), the values `Tₘ.Open.d` itself.
7. The internals of the closed types made `protected`, and the open types
   `Tₘ.Open` (`protectGenerated`); those of each run by the pipeline already.

All of it runs in one `TermElabM` run, after the modifiers (`prepareDecls`) and before the doc
comments and the attributes (`finishDecls`, `applyDeclAttrs`, `Gen/Command.lean`), and a failure
anywhere restores the state: a failed block declares nothing.
-/

open Lean Meta Elab Term Command

namespace Codata.Gen

/-- The runs of a block, `decls`, with their names: those of the types, private or not, and of
the blocks after them (`blockName`), as private as they are. -/
def mixRuns (decls : Array DeclStx) : Array MixRun := Id.run do
  let mut groups : Array (Bool × Array Nat) := #[]
  for d in decls, i in [0:decls.size] do
    if let some (co, ds) := groups.back? then
      if co == d.co then
        groups := groups.pop.push (co, ds.push i)
        continue
    groups := groups.push (d.co, #[i])
  return groups.mapIdx fun j (co, ds) =>
    let closedNames := ds.map (decls[·]!.declName)
    let isBlock := ds.size ≥ 2
    let blk := privateLike closedNames[0]! (blockName (ds.map (decls[·]!.userName)))
    let closedFam := if isBlock then blk else closedNames[0]!
    let opened (n : Name) : Name := if j == 0 then n else n ++ `Open
    { co, decls := ds, names := closedNames.map opened, fam := opened closedFam
      ix? := if isBlock then some (blk ++ `Ix) else none, closedNames, closedFam }

/-! ### Checks before the runs are declared -/

/-- The names of a mixed block, before anything is declared (`checkNames`): the types, the open
types `Tₘ.Open` of the runs inside, and for a run of several types, its name, open name and
index; the constructors of each run (`checkCtorNames`, with the types outside the run, through
which a run inside has membership instances). `ref` is the block's keyword. -/
def checkMixNames (decls : Array DeclStx) (runs : Array MixRun) (ref : Syntax) :
    TermElabM Unit := do
  checkNames decls none ref
  for run in runs, j in [0:runs.size] do
    let others := ((Array.range decls.size).filter (!run.decls.contains ·)).map
      (decls[·]!.declName)
    checkCtorNames (run.decls.map (decls[·]!)) (inner := j > 0) others
    if j > 0 then
      for n in run.names, d in run.decls do
        checkFree n decls[d]!.T "a type `T` of a run inside the first is declared open, as \
          `T.Open`; rename the type, or declare the block in another namespace"
    if let some ix := run.ix? then
      checkBlockShorts (run.decls.map (decls[·]!))
      for n in [run.closedFam, run.fam, ix].eraseDups do
        checkFree n ref "a run of several types is named after its types, joined by `_`, in their \
          common namespace, with its index `Ix` and, inside the first run, its open form `Open` in \
          the run's namespace; rename or reorder the types, or declare the block in another \
          namespace"

/-- The declared sorts of a mixed block (`checkSorts`), once the runs inside are declared and
before the outermost run is: the outermost run's types are in the universe of its model (`ctx`),
the closed types of a run inside in that of its open type at the universes of the runs it needs.
`xLevels` are the universes of the extra parameters of each run. -/
def checkMixSorts (ctx : Ctx) (decls : Array DeclStx) (runs : Array MixRun)
    (xLevels : Array (Array Name)) : TermElabM Unit := do
  if ctx.written.isEmpty then return
  let mut lvls : Array Level := #[← ctx.modelLevel]
  for j in [1:runs.size] do
    let run := runs[j]!
    let ty := (← getConstInfo run.fam).type
    let l ← forallTelescopeReducing ty fun _ body => do
      let .sort l := body | throwError "internal error: not a family{indentExpr ty}"
      return l.dec.getD l
    let need := run.need.map (lvls[·]!)
    lvls := lvls.push (l.instantiateParams xLevels[j]!.toList need.toList).normalize
  ctx.checkSorts ((Array.range decls.size).map fun d =>
    (runs.findIdx? (·.decls.contains d)).map (lvls[·]!))

/-! ### Restating a declaration at the closed types -/

/-- The internals of an open type (the model's, step 5's), under `T.Open.Colean`, which a closed
type does not restate. -/
def internalHeads : List String := ["Colean"]

/-- The auxiliary constructions of an inductive type and of its constructors. -/
def auxSuffixes : List String :=
  ["rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "ctorIdx", "ctorElim",
    "ctorElimType", "below", "brecOn", "binductionOn", "ibelow", "inj", "injEq", "elim",
    "sizeOf_spec"]

/-- Is `n`, under the name `pre` of an open type, part of the type's public interface: not a
declaration of the model or of step 5, not an auxiliary construction of an inductive type, not an
equation lemma? -/
def isPublic (pre n : Name) : MetaM Bool := do
  let rest := (n.replacePrefix pre .anonymous).components.map (·.toString)
  if rest.any (·.startsWith "_") then return false
  if let h :: _ := rest then
    if internalHeads.contains h then return false
  let some last := rest.getLast? | return true
  if last.startsWith "eq_" || last.startsWith "match_" || last.startsWith "proof_" then
    return false
  if auxSuffixes.contains last then
    if let some ci := (← getEnv).find? n.getPrefix then
      if ci.isInductive || ci.isCtor then return false
  return true

/-- Restate the declaration `C` of an open run at the closed families as `C'`: the first `np`
binders of `C` are the parameters, then come the extra parameters, at the closed families `args`
(functions of the parameters) and at the universes `xVals` for theirs, `xLevels`. The statement is
written with the closed declarations (`rules`), the value is `C` itself. An inductive type and its
constructors (`T.F`) become reducible definitions, the constructors usable in patterns; so do
reducible definitions, and those `reducible` asks for, and a definition usable in patterns (the
constructors `Tₘ.Open.F.c` of the layers per type of a block) stays so. Simp lemmas, eliminators
and `elab_as_elim` keep their attributes. Returns the fold rule of `C`. -/
def restate (C C' : Name) (np : Nat) (args : Array Expr) (xLevels : Array Name)
    (xVals : Array Level) (rules : Closed) (ref : Syntax) (reducible : Bool := false) :
    TermElabM FoldRule := do
  let ci ← getConstInfo C
  let lps := ci.levelParams
  let type := ci.type.instantiateLevelParams xLevels.toList xVals.toList
  let us := lps.map fun p => match xLevels.findIdx? (· == p) with
    | some i => xVals[i]!
    | none => .param p
  let lps' := lps.filter (!xLevels.contains ·)
  let dropLvls := (lps.zipIdx.filterMap fun (p, i) =>
    if xLevels.contains p then some i else none).toArray
  let (type', value') ← forallBoundedTelescope type np fun ps body => do
    let xs := args.map (·.beta ps)
    let body ← instantiateForall body xs
    return (← mkForallFVars ps (foldClosed rules body),
      ← mkLambdaFVars ps (mkAppN (.const C us) (ps ++ xs)))
  let used := (collectLevelParams (collectLevelParams {} type') value').params
  for u in used do
    unless lps'.contains u do
      throwError "internal error: unexpected universe `{u}` in the closed form of `{C}`"
  if ci.isTheorem then addThm C' lps' type' value' ref
  else addDef C' lps' type' value' ref (reducible := reducible || ci.isCtor || ci.isInductive ||
    (← getReducibilityStatus C) == .reducible)
  -- The attributes.
  let env ← getEnv
  let mut attrs : Array (TSyntax ``Parser.Term.attrInstance) := #[]
  if ci.isCtor || hasMatchPatternAttribute env C then
    attrs := attrs.push (← `(Parser.Term.attrInstance| match_pattern))
  if Lean.Elab.Term.elabAsElim.hasTag env C then
    attrs := attrs.push (← `(Parser.Term.attrInstance| elab_as_elim))
  for ((ind, _), n) in (← getCustomEliminators).map.toList do
    if n == C then
      attrs := attrs.push (← if ind then `(Parser.Term.attrInstance| induction_eliminator)
        else `(Parser.Term.attrInstance| cases_eliminator))
  unless attrs.isEmpty do addAttrs C' attrs
  if ci.isTheorem && (← getSimpTheorems).isLemma (.decl C) then addSimp C'
  if packAttr.hasTag env C then packAttr.setTag C'
  if mutualRecAttr.hasTag env C then mutualRecAttr.setTag C'
  return { openN := C, closedN := C', np, args, dropLvls }

/-- The names `ns`, ordered so that every one comes after those its type mentions. -/
partial def typeOrder (ns : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let set := ns.foldl (·.insert ·) ({} : NameSet)
  let rec visit (n : Name) (st : NameSet × Array Name) : NameSet × Array Name := Id.run do
    let (seen, out) := st
    if seen.contains n then return st
    let mut st := (seen.insert n, out)
    if let some ci := env.find? n then
      for d in ci.type.getUsedConstants do
        if set.contains d then st := visit d st
    return (st.1, st.2.push n)
  return (ns.foldl (fun st n => visit n st) ({}, #[])).2

/-- What closing the runs inside needs: for each run, its closed family as a function of the
parameters (the type, a family over its packed index, or the block's family) and its universe. -/
abbrev ClosedFams := Array (Expr × Level)

/-- The closed family of the run `run` over the parameters `params`, once its closed types exist,
and its universe. -/
def closedFam (run : MixRun) (params : Array Expr) : TermElabM (Expr × Level) := do
  let e ← appConst (if run.ix?.isSome then run.closedFam else run.closedNames[0]!) params
  let lvl ← forallTelescopeReducing (← inferType e) fun _ body => do
    let .sort l := body | throwError "internal error: not a family{indentExpr e}"
    return (l.dec.getD l).normalize
  if run.ix?.isSome then return (e, lvl)
  let fam ← forallTelescopeReducing (← inferType e) fun is _ => do
    if is.isEmpty then return e
    let J ← packedType is
    withLocalDeclD `p J fun p => do mkLambdaFVars #[p] (mkAppN e (← projsN is.size p))
  return (fam, lvl)

/-- The pairs of an open type, or family, and its closed counterpart, with the declaration they
come from. -/
def typePairs (decls : Array DeclStx) (run : MixRun) : Array (Name × Name × Syntax) :=
  let ref := decls[run.decls[0]!]!.ref
  let types := (run.names.zip run.closedNames).zipIdx.map fun ((o, c), m) =>
    (o, c, decls[run.decls[m]!]!.ref)
  if run.ix?.isSome then #[(run.fam, run.closedFam, ref)] ++ types else types

/-- The family of the run `j` as an argument of an open type, with the closed families `fams`
of the runs outside `k` and the members of the run `k` at `X`: the open types of the runs between
at these. -/
partial def memArg (runs : Array MixRun) (fams : ClosedFams) (params : Array Expr) (k : Nat)
    (X : Expr) (j : Nat) : TermElabM Expr := do
  if j < k then return fams[j]!.1.beta params
  if j == k then return X
  let run := runs[j]!
  let e ← appConst run.fam (params ++ (← run.need.mapM (memArg runs fams params k X)))
  if run.ix?.isSome then return e
  forallTelescopeReducing (← inferType e) fun is _ => do
    if is.isEmpty then return e
    withLocalDeclD `p (← packedType is) fun p => do mkLambdaFVars #[p] (mkAppN e (← projsN is.size p))

/-- Membership in the closed types of the run `j` (`MemRule`): for every run `k` that nests through
it, whose types are those of one type without indices, and every type of `j`, the instance
`Membership (Tₖ params) (Tⱼ params idx)`, named `Tⱼ.instMembershipTₖ`, whose `x ∈ c` is
`PolyIso.Mem (fun X => Tⱼ.Open params (fams) idx) x c` with the members of `k` at `X`: how the
recursors of `k` state their hypotheses through `j`. -/
def memInstances (ctx : Ctx) (decls : Array DeclStx) (runs : Array MixRun) (fams : ClosedFams)
    (j : Nat) : TermElabM (Array MemRule) := do
  let params := ctx.params
  let run := runs[j]!
  let ns ← getCurrNamespace
  let mut out := #[]
  for k in run.nestedBy do
    let rk := runs[k]!
    if rk.ix?.isSome then continue
    let E := fams[k]!.1.beta params
    unless (← whnf (← inferType E)).isSort do continue
    for m in [0:run.names.size] do
      let CT ← appConst run.closedNames[m]! params
      let rule? ← forallTelescopeReducing (← inferType CT) fun idx _ => do
        let C := mkAppN CT idx
        let fn ← withLocalDeclD `X (mkSort fams[k]!.2.succ) fun X => do
          mkLambdaFVars #[X] (mkAppN (← appConst run.names[m]!
            (params ++ (← run.need.mapM (memArg runs fams params k X)))) idx)
        let isoC ← mkConstWithFreshMVarLevels ``Codata.PolyIso
        let (xs, _, _) ← forallMetaTelescope (← inferType isoC)
        unless ← isDefEq xs[0]! fn do return none
        let some inst ← synthInstance? (mkAppN isoC xs) | return none
        let xs ← xs.mapM instantiateMVars
        let memFn ← withLocalDeclD `c C fun c => withLocalDeclD `x E fun x => do
          mkLambdaFVars #[c, x]
            (← mkAppOptM ``Codata.PolyIso.Mem #[fn, xs[1]!, xs[2]!, inst, E, x, c])
        let value ← mkAppOptM ``Membership.mk #[E, C, memFn]
        let type ← mkAppM ``Membership #[E, C]
        let (type, value) ← withBinderInfo (params ++ idx) .implicit do
          return (← mkForallFVars (params ++ idx) type, ← mkLambdaFVars (params ++ idx) value)
        let short := nameIn ns rk.closedNames[0]!
        let name := run.closedNames[m]! ++ Name.mkSimple ("instMembership" ++ short)
        let us ← ctx.levelParamsOf [] #[type, value]
        addDef name us type value decls[run.decls[m]!]!.ref (reducible := true)
        addInstance name .global (eval_prio default)
        let instApp := mkAppN (.const name (us.map mkLevelParam)) (params ++ idx)
        return some {
          np := params.size, nIdx := idx.size, elemN := rk.closedNames[0]!
          contN := run.closedNames[m]!, fn := ← mkLambdaFVars (params ++ idx) fn
          elem := ← mkLambdaFVars params E
          mem := ← mkLambdaFVars (params ++ idx) (← mkAppOptM ``Membership.mem #[E, C, instApp])
          unfolded := ← mkLambdaFVars (params ++ idx) memFn : MemRule }
      if let some rule := rule? then out := out.push rule
  return out

/-- The hook of the outermost run (`pipeline`), once its types exist: the closed types of the runs
inside, from the outermost of them in, `Tₘ params := Tₘ.Open params (fams)` at the closed families
of the runs each needs, as abbreviations, and membership in them (`memInstances`); the closed
families go to `famsRef`, the fold rules to the context, with which the rest of the outermost run
is stated. `xLevels` are the universes of the extra parameters of each run. -/
def closeTypes (decls : Array DeclStx) (runs : Array MixRun) (xLevels : Array (Array Name))
    (famsRef : IO.Ref ClosedFams) (ctx : Ctx) : TermElabM Ctx := do
  let params := ctx.params
  let mut fams : ClosedFams := #[]
  let mut closed := ctx.closed
  let (f₀, l₀) ← closedFam runs[0]! params
  fams := fams.push (← mkLambdaFVars params f₀, l₀)
  for j in [1:runs.size] do
    let run := runs[j]!
    let args := run.need.map (fams[·]!.1)
    let xVals := run.need.map (fams[·]!.2)
    for (o, c, ref) in typePairs decls run do
      let r ← restate o c params.size args xLevels[j]! xVals closed ref (reducible := true)
      closed := { closed with rules := closed.rules.insert o r }
    let (f, l) ← closedFam run params
    fams := fams.push (← mkLambdaFVars params f, l)
  for j in [1:runs.size] do
    closed := { closed with mems := closed.mems ++ (← memInstances ctx decls runs fams j) }
  famsRef.set fams
  return { ctx with closed }

/-- The public interface of the open run `run` restated at the closed types (`restate`), but for
its types, closed already (`closeTypes`): its constructors are reducible, so that the `simp`
lemmas of the open types, those of step 5 among them, apply to the closed ones. -/
def restateRun (decls : Array DeclStx) (run : MixRun) (np : Nat) (xLevels : Array Name)
    (fams : ClosedFams) (rules : Closed) : TermElabM Closed := do
  let pairs := typePairs decls run
  let ctors := (run.decls.zip run.names).flatMap fun (d, n) =>
    decls[d]!.ctors.map fun c => n ++ c.name.getId
  let mut cands : Array (Name × Name × Name × Syntax) := #[]
  for (n, _) in (← getEnv).constants.map₂.toList do
    let some (o, c, ref) := pairs.find? (·.1.isPrefixOf n) | continue
    if ← isPublic o n then cands := cands.push (n, o, c, ref)
  cands := cands.qsort (·.1.lt ·.1)
  let args := run.need.map (fams[·]!.1)
  let xVals := run.need.map (fams[·]!.2)
  let mut rules := rules
  for n in ← typeOrder (cands.map (·.1)) do
    let some (_, o, c, ref) := cands.find? (·.1 == n) | continue
    let n' := n.replacePrefix o c
    if (← getEnv).contains n' then continue
    let r ← restate n n' np args xLevels xVals rules ref (reducible := ctors.contains n)
    rules := { rules with rules := rules.rules.insert n r }
    -- The display of the block functor's constructor as the layer's (`Gen/Pack.lean`).
    if let some (A, xi) := layerCtorExt.find? (← getEnv) n then
      if let some (o, c, _) := pairs.find? (·.1.isPrefixOf A) then
        modifyEnv (layerCtorExt.insert · n' (A.replacePrefix o c, xi - args.size))
  return rules

/-- For each membership instance of a closed type (`MemRule`), the `simp` lemmas `Tⱼ.mem_c` on the
type's constructors: `x ∈ Tⱼ.c args ↔ …`, the right-hand side the normal form of the default `simp`
set of the membership through the open types (with the lemmas `Tⱼ.Open.Colean.Poly.mem_c` of step
5), written with the closed memberships. A constructor whose membership `simp` does not rewrite gets
none. -/
def memLemmas (decls : Array DeclStx) (runs : Array MixRun) (closed : Closed) : TermElabM Unit := do
  let ns ← getCurrNamespace
  let simpCtx ← Simp.mkContext (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let simprocs := #[← Simp.getSimprocs]
  for r in closed.mems do
    let some (d, C) := (runs.flatMap fun run => run.decls.zip run.closedNames).find? (·.2 == r.contN)
      | continue
    for ctor in decls[d]!.ctors do
      let cN := C ++ ctor.name.getId
      let ci ← getConstInfo cN
      let us := ci.levelParams.map mkLevelParam
      forallBoundedTelescope ci.type r.np fun ps cty => do
      forallTelescope cty fun ys rty => do
      let idx := rty.getAppArgs.extract r.np rty.getAppNumArgs
      let mem := r.mem.beta (ps ++ idx)
      withLocalDeclD `x (r.elem.beta ps) fun x => do
      let capp := mkAppN (.const cN us) (ps ++ ys)
      let unfolded := (r.unfolded.beta (ps ++ idx)).beta #[capp, x]
      let (simped, _) ← Meta.simp unfolded simpCtx simprocs
      if simped.expr == unfolded then return
      let pf ← match simped.proof? with
        | some pf => mkAppM ``Iff.of_eq #[pf]
        | none => mkAppM ``Iff.refl #[unfolded]
      let xs := ps ++ ys.push x
      let (type, value) ← withBinderInfo ps .implicit do
        return (← mkForallFVars xs (mkIff (mkApp2 mem capp x) (foldClosed closed simped.expr)),
          ← mkLambdaFVars xs pf)
      let base := C ++ Name.mkSimple ("mem_" ++ ctor.name.getId.toString)
      let n := if (← getEnv).contains base then
          base.appendAfter ("_" ++ nameIn ns r.elemN)
        else base
      let lps := ci.levelParams.filter (collectLevelParams {} type).params.contains
      addThm n lps type value decls[d]!.ref
      addSimp n

/-- `elabMixed` once the modifiers are elaborated, `vars` the section variables. -/
def elabMixedCore (decls : Array DeclStx) (ref : Syntax) (vars : Array Expr) : TermElabM Unit := do
  let mut runs := mixRuns decls
  checkMixNames decls runs ref[0]
  let k := runs.size
  let (bvars, mentions) ← mixedVars decls ref vars
  -- What each run needs, innermost first, and what nests through it.
  let runOf (d : Nat) : Nat := (runs.findIdx? (·.decls.contains d)).getD 0
  let mut needs : Array (Array Nat) := Array.replicate k #[]
  let mut reach : Array (Array Nat) := Array.replicate k #[]
  for i in [0:k] do
    let r := k - 1 - i
    let clo := mixReach needs r ((runs[r]!.decls.flatMap (mentions[·]!)).map runOf)
    reach := reach.set! r clo
    needs := needs.set! r (clo.filter (· < r))
  runs := runs.mapIdx fun j run =>
    { run with need := needs[j]!, nestedBy := (Array.range j).filter (reach[·]!.contains j) }
  declareMixIx decls runs ref bvars
  let mix (r : Nat) : Mix := { all := decls, runs, r, vars := bvars }
  let runDecls (r : Nat) : Array DeclStx := runs[r]!.decls.map (decls[·]!)
  -- The runs inside, from the innermost out, open.
  let mut xLevels : Array (Array Name) := Array.replicate k #[]
  for i in [0:k - 1] do
    let j := k - 1 - i
    let xl ← withCtx (runDecls j) ref vars (mix? := some (mix j)) fun ctx => do
      discard <| pipeline ctx
      return (ctx.mix?.map (·.xLevels)).getD #[]
    xLevels := xLevels.set! j xl
  -- The outermost run, with the closed types of the runs inside as soon as its types exist.
  let famsRef ← IO.mkRef (#[] : ClosedFams)
  let (np, closed) ← withCtx (runDecls 0) ref vars (mix? := some (mix 0)) fun ctx => do
    step (checkMixSorts ctx decls runs xLevels)
    let ctx ← pipeline ctx (afterTypes := closeTypes decls runs xLevels famsRef)
    return (ctx.params.size, ctx.closed)
  -- The rest of the runs inside, at the closed types.
  let fams ← famsRef.get
  let mut closed := closed
  for j in [1:k] do
    closed ← step (restateRun decls runs[j]! np xLevels[j]! fams closed)
  step (memLemmas decls runs closed)
  -- The internals of the closed types, and the open types, `protected`.
  for run in runs.extract 1 runs.size do
    let ctors := (run.decls.zip run.closedNames).flatMap fun (d, n) =>
      decls[d]!.ctors.map fun c => n ++ c.name.getId
    protectGenerated (run.closedNames.push run.closedFam) (run.closedNames ++ ctors)

/-- Elaborate a `mixed_mutual` block `decls` with both kinds, `ref` the command: see the header.
-/
def elabMixed (decls : Array DeclStx) (ref : Syntax) : CommandElabM Unit :=
  runTermElabM fun vars => do
  let decls ← allOrNothing do
    let decls ← prepareDecls decls
    Term.withLevelNames decls[0]!.levelNames (elabMixedCore decls ref vars)
    finishDecls decls
    return decls
  applyDeclAttrs decls

end Codata.Gen
