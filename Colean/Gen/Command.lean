import Colean.Gen.Front
import Colean.Gen.Derive

/-!
# Generators on `Expr`: the pipeline

`codata` and `data`, single declarations and `mutual` blocks: the declarations are analysed
(`Gen/Front.lean`) and the steps of `architecture.md` run on their context in the order of their
dependencies, all inside one `TermElabM` run (`runTermElabM`, for the section variables): the
functor (step 1), for `codata` the lifting `T.F.Rel` (step 4, needed by the model), the
signature, the isomorphism and the contract (step 2), in a block the types `Tₘ`, the framework
(step 3), the constructors and `casesOn` (step 4), for `data` the recursor (step 2b, stated with
the constructors) and the computation rules, and in a block the aliases. Each declaration is
checked by the kernel as it is added, so a failure stops the command there, and the state is
restored: a failed command declares nothing. Each step has its own heartbeat budget. Then,
separately, the derived instances (step 5, `Gen/Derive.lean`), whose failure is only a warning.
-/

open Lean Elab Command

namespace Codata.Gen

/-- Run a step of the pipeline with its own heartbeat budget, as a separate command has. -/
def step (x : TermElabM α) : TermElabM α := withCurrHeartbeats x

/-- Elaborate the declarations `decls`, one or a `mutual` block of the same kind, with the
generators of `Gen/`. `ref` is the command. A failure declares nothing: the state is restored,
then the error is rethrown. -/
def elabDecls (decls : Array DeclStx) (ref : Syntax) : CommandElabM Unit :=
  runTermElabM fun vars => do
  let s ← saveState
  tryCatchRuntimeEx (withCtx decls ref vars fun ctx => do
    step ctx.genFunctor
    if ctx.co then
      step ctx.genRelType
      step ctx.genRelMap
    step ctx.genSignature
    step ctx.genIso
    if ctx.co then step ctx.genRelOfC
    step ctx.genModel
    step ctx.genTypes
    step ctx.genFramework
    step ctx.genCtors
    step ctx.genCases
    if ctx.co then step ctx.genAliases
    else
      step ctx.genRec
      step ctx.genRecLemmas
      step ctx.genDataAliases
    ctx.addDeclInfo
    -- A separate step, after the type is complete: it cannot fail the declaration.
    ctx.deriveInstances)
    fun e => do
      -- The messages logged so far stay, as do the infos on the user's syntax.
      let msgs ← Core.getMessageLog
      s.restore
      Core.setMessageLog msgs
      throw e

/-- Elaborate a `codata` or `data` declaration. -/
def elabDecl (stx : Syntax) : CommandElabM Unit := do
  let some d := DeclStx.read? stx | throwUnsupportedSyntax
  elabDecls #[d] stx

end Codata.Gen
