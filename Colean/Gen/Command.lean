import Colean.Gen.Front
import Colean.Gen.Derive

/-!
# Generators on `Expr`: the pipeline

`codata` and `data`, single declarations, `mutual` blocks, and the runs of a `mixed_mutual`
block (`Gen/Mixed.lean`): the declarations are analysed
(`Gen/Front.lean`) and the steps of `architecture.md` run on their context in the order of their
dependencies, all inside one `TermElabM` run (`runTermElabM`, for the section variables): the
functor (step 1), for `codata` the lifting `T.F.Rel` with its lemmas (step 4, needed by the
model), the signature, the isomorphism and the contract (step 2), in a block the types `Tₘ`, the
framework (step 3), in a block the layer, the destructor and the constructor per type, and for
`codata` the lemmas of the lifting per type (step 4), the constructors and `casesOn` (step 4), in
a block Lambek's lemma and the rules of the destructor and the constructor per type, equality by
the destructor, for `data` the recursor (step 2b, stated with the constructors) and the
computation rules, and in a block the recursors and the folds per type (`data`), or corecursion
and coinduction per type and coinduction up to equality (`codata`). Before them, the declared
sorts with a universe are checked against the types' (`checkSorts`). Each declaration is checked by the kernel as it is
added, so a failure stops the command there, and the state is restored: a failed command
declares nothing. Each step has its own heartbeat budget. Then, separately, the derived instances (step 5,
`Gen/Derive.lean`), whose failure is only a warning. Last, the internals are made `protected`
(`protectGenerated`, `Gen/Decl.lean`), as `inductive` protects its own.

Around the pipeline, as `inductive` does around its declarations: before it, the modifiers
(`prepareDecls`, `Gen/Front.lean`); after it, the doc comments, `protected` on constructors and
the info trees of the names the user wrote (`finishDecls`), and last, outside the all-or-nothing
run, the attributes of the types and constructors (`applyDeclAttrs`).
-/

open Lean Elab Command

namespace Codata.Gen

/-- Run a step of the pipeline with its own heartbeat budget, as a separate command has. -/
def step (x : TermElabM α) : TermElabM α := withCurrHeartbeats x

open Meta in
/-- Check the declared sorts with a universe (`Ctx.written`) against the types', before anything
is declared: `lvls` gives by declaration of the block the `L` of its type's `Type L`, none where
it is not known. A declared sort does not change the universe, which is the encoding's. -/
def Ctx.checkSorts (ctx : Ctx) (lvls : Array (Option Level)) : TermElabM Unit := do
  -- A universe the constructors fix and the model does not have is `genSignature`'s error.
  if let some l := ctx.fixedLvl? then
    unless ← isLevelDefEq (← ctx.modelLevel) l do return
  for w in ctx.written do
    let some L := lvls[w.decl]?.join | continue
    if L.hasMVar || (← isLevelDefEq w.lvl L.succ) then continue
    let actual ← forallTelescopeReducing w.sort fun is _ => mkForallFVars is (mkSort L.succ)
    -- On one line: the sorts are short, and inline in the message.
    let flat (e : Expr) : MetaM String := return (← ppExpr e).pretty (width := 1000)
    let (written, actual) := (← flat w.sort, ← flat actual)
    let why := if w.lvl.normalize == .zero then m!"these commands define types, not propositions"
      else if ctx.isBlock then m!"these commands put the types of a block in the universe of its \
        encoding, the largest of those of the block's indices and of the constructors' data"
      else m!"these commands put a type in the universe of its encoding, the largest of those of \
        its indices and of its constructors' data"
    throwErrorAt w.stx "`{w.T}` is declared with sort `{written}` but defined with sort \
      `{actual}`: {why}; write `{actual}`, or `Type _` to leave the universe to the command"

/-- The pipeline on the context of a declaration, steps 1 to 4 and then step 5. `afterTypes` runs
once the types exist and may extend the context: the outermost run of a `mixed_mutual` block
declares there the closed types of the runs inside, with which the rest is stated. In an open run
of a mixed block the names the user wrote are left to the closed types (`MutualCmd.lean`).
Returns the context as extended. -/
def pipeline (ctx : Ctx) (afterTypes : Ctx → TermElabM Ctx := pure) : TermElabM Ctx := do
  -- The declared sorts, first; those of a mixed block are `elabMixed`'s.
  if ctx.mix?.isNone && !ctx.written.isEmpty then
    let L ← ctx.modelLevel
    step (ctx.checkSorts (.replicate ctx.types.size (some L)))
  step ctx.genFunctor
  if ctx.co then
    step ctx.genRelType
    step ctx.genRelMap
    step ctx.genRelLemmas
  step ctx.genSignature
  step ctx.genIso
  if ctx.co then step ctx.genRelOfC
  step ctx.genModel
  step ctx.genTypes
  let ctx ← step (afterTypes ctx)
  step ctx.genFramework
  step ctx.genLayers
  step ctx.genLayerRels
  step ctx.genCtors
  step ctx.genTypeLambek
  step ctx.genDtorLemmas
  step ctx.genCases
  if ctx.co then
    step ctx.genTypeCorecs
    step ctx.genCoinduct
  else
    step ctx.genRec
    step ctx.genRecLemmas
    step ctx.genTypeRecs
    step ctx.genTypeFolds
  -- A separate step, after the type is complete: it cannot fail the declaration, unless it is
  -- an open run of a mixed block that an outer run nests through.
  ctx.deriveInstances
  -- Last, the internals made `protected` (`protectedGen`).
  let tys := ctx.types.map (·.name)
  protectGenerated (tys.push ctx.name) (tys ++ ctx.ctors.map ctx.tCtor)
  return ctx

/-- Run `x`; on failure, restore the state and rethrow: a failed command declares nothing. The
messages logged so far stay, as do the infos on the user's syntax. -/
def allOrNothing (x : TermElabM α) : TermElabM α := do
  let s ← saveState
  tryCatchRuntimeEx x fun e => do
    let msgs ← Core.getMessageLog
    s.restore
    Core.setMessageLog msgs
    throw e

/-- Once everything is declared, as `inductive` does after its declarations
(`elabInductiveViewsPostprocessing`): the doc comments of the types and the constructors,
`protected` on the constructors, and the names the user wrote, the types and the constructors, in
the info tree, as the declarations they name (after the doc comments, which hovers show). -/
def finishDecls (decls : Array DeclStx) : TermElabM Unit := do
  for d in decls do
    if let some doc := d.modifiers.docString? then
      withRef d.declId <| addDocString d.declName d.binderStx doc
    for c in d.ctors, cm in d.ctorMods do
      let n := d.declName ++ c.name.getId
      if cm.isProtected then modifyEnv (addProtected · n)
      if let some doc := cm.docString? then
        withRef c.name <| addDocString n c.binderStx doc
  withSaveInfoContext do
    for d in decls do
      Term.addTermInfo' d.T (← mkConstWithLevelParams d.declName) (isBinder := true)
    for d in decls do
      for c in d.ctors do
        Term.addTermInfo' c.name (← mkConstWithLevelParams (d.declName ++ c.name.getId))
          (isBinder := true)

/-- The attributes of the types and of the constructors, applied to them once everything is
declared, as `attribute [attrs] T` after the declaration would: a failure is an error of the
attribute, and the declarations stay, as with `inductive`. -/
def applyDeclAttrs (decls : Array DeclStx) : TermElabM Unit := do
  for d in decls do
    withRef d.declId <| Term.applyAttributes d.declName d.modifiers.attrs
    for c in d.ctors, cm in d.ctorMods do
      withRef c.name <| Term.applyAttributes (d.declName ++ c.name.getId) cm.attrs

/-- Elaborate the declarations `decls`, one or a `mutual` block of the same kind, with the
generators of `Gen/`. `ref` is the command. First the modifiers (`prepareDecls`), then the
declarations, at the universe names of the block (`T.{u}`). A failure declares nothing: the state
is restored, then the error is rethrown. The attributes come last (`applyDeclAttrs`). -/
def elabDecls (decls : Array DeclStx) (ref : Syntax) : CommandElabM Unit :=
  runTermElabM fun vars => do
    let decls ← allOrNothing do
      let decls ← prepareDecls decls
      Term.withLevelNames decls[0]!.levelNames do
        discard <| withCtx decls ref vars fun ctx => pipeline ctx
      finishDecls decls
      return decls
    applyDeclAttrs decls

/-- Elaborate a `codata` or `data` declaration. -/
def elabDecl (stx : Syntax) : CommandElabM Unit := do
  let some d := DeclStx.read? stx | throwUnsupportedSyntax
  elabDecls #[d] stx

end Codata.Gen
