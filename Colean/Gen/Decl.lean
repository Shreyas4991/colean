import Lean
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.Constructions.CtorElim

/-!
# Generators on `Expr`: adding declarations

*Spec.* The helpers through which the generators of `Gen/` add their declarations, without
syntax: inductive types with the auxiliary constructions Lean's `inductive` adds
(`addInductive`), definitions, all noncomputable (`addDef`), theorems with a proof term
(`addThm`) or with a proof found by a tactic on a goal metavariable (`prove`, `proveHere`,
`runTac`, `simpOnly`), and attributes (`addSimp`, `addAttrs`); `mkCasesOnApp`, definition by
cases on an inductive type; `withUnfolding`, the definitional unfolding of Lean before 4.34 for
the proofs that need it; and the generated declarations that are `protected`, listed here only
(`protectedGen`, applied by `protectGenerated` once a command has declared everything). Their
inputs are closed terms: the generators build types and values over the free variables of the
analysis (`Gen/Ctx.lean`) and close them with `mkForallFVars`/`mkLambdaFVars`; the universe
parameters come from `levelParamsOf`. A generated declaration has the declaration range of the
user's declaration, unless its name repeats a component (`addRanges`).

Lean's elaborators do more than these helpers on purpose: definitions are not compiled
(everything generated is noncomputable), and there are no matchers (definitions by cases use
`casesOn`, their computation rules are stated as theorems). The generated declarations get
declaration ranges but no info trees, which only the names the user wrote get, the types and the
constructors (`Ctx.addDeclInfo`, `Gen/Surface.lean`).
-/

open Lean Meta Elab Term

namespace Codata.Gen

/-! ### Universes -/

/-- `n` names `u_1`, `u_2`, … not among `avoid`: the universes a declaration adds to the user's,
named as Lean names the universes it introduces. -/
def freshLevelNames (n : Nat) (avoid : List Name) : List Name := Id.run do
  let mut out := #[]
  let mut i := 1
  while out.size < n do
    let u := Name.mkSimple s!"u_{i}"
    unless avoid.contains u do out := out.push u
    i := i + 1
  return out.toList

/-- The universe parameters of a declaration made of the terms `es`, in the order Lean gives
them: the user's universes `user` in their order, then the added ones `fresh` in theirs, each
only if it occurs. Any other universe parameter is an internal error. -/
def levelParamsOf (user fresh : List Name) (es : Array Expr) : MetaM (List Name) := do
  let s := es.foldl (fun s e => collectLevelParams s e) {}
  for u in s.params do
    unless user.contains u || fresh.contains u do
      throwError "internal error: unexpected universe parameter `{u}` in a generated declaration"
  return user.filter s.params.contains ++ fresh.filter s.params.contains

/-- Apply `f` to every universe level in `e`. -/
def mapLevels (f : Level → Level) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => some (.const n (us.map f))
    | .sort u => some (.sort (f u))
    | _ => none

/-- `e` with the universe parameter `u` replaced by `l`; the levels that mentioned `u` are
normalized (`max u_1 0` is `u_1`). -/
def substLevel (u : Name) (l : Level) (e : Expr) : Expr :=
  if !e.hasLevelParam then e else
  mapLevels (fun v =>
    let v' := v.instantiateParams [u] [l]
    if v' == v then v else v'.normalize) e

/-- The universe `v` of a type `A : Type v`. -/
def typeLevel (A : Expr) : MetaM Level := do
  let l := (← instantiateLevelMVars (← getLevel A)).normalize
  match l.dec with
  | some v => return v
  | none => throwError "expected a type in `Type _`, got{indentExpr A}\nin `Sort {l}`"

/-- The constant `n` at the universes given by name, `[(`u, l₁), (`v, l₂)]`: robust to the order
of its universe parameters. -/
def constAt (n : Name) (lvls : List (Name × Level)) : MetaM Expr := do
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun p => match lvls.lookup p with
    | some l => pure l
    | none => throwError "internal error: no universe given for `{p}` of `{n}`"
  return .const n us

/-- The universe `r` of an inductive type in `Type r` whose constructor arguments live in the
sorts `Sort lᵢ`: the least `r` with `lᵢ ≤ r + 1`, as Lean's `inductive` infers `Type _`
(`inferResultingUniverse`, for the offset `1`). -/
def resultLevel (ls : Array Level) : Level :=
  let rec go (l : Level) (off : Int) (acc : Array (Level × Int)) : Array (Level × Int) :=
    match l with
    | .max a b | .imax a b => go b off (go a off acc)
    | .succ a => go a (off - 1) acc
    | .zero => if off < 0 then acc.push (.zero, off) else acc
    | l => acc.push (l, off)
  let cs := ls.foldl (fun acc l => go l.normalize 1 acc) #[]
  (cs.foldl (fun r (l, k) => mkLevelMax' r (Level.addOffset l (-k).toNat)) .zero).normalize

/-! ### Binders -/

/-- Rename the leading `∀` binders of `e`: the `i`-th (from 0) gets `f i n`, `n` its name. -/
def renameForalls (f : Nat → Name → Name) (e : Expr) (i : Nat := 0) : Expr :=
  match e with
  | .forallE n d b bi => .forallE (f i n) d (renameForalls f b (i + 1)) bi
  | _ => e

/-- Run `k` on fresh copies of the local variables `xs`, named `names`, with binder info `bi`:
the type of a copy refers to the earlier copies. -/
def withCopies (xs : Array Expr) (names : Array Name) (bi : BinderInfo)
    (k : Array Expr → TermElabM α) : TermElabM α := do
  let rec go (i : Nat) (ys : Array Expr) : TermElabM α := do
    if h : i < xs.size then
      let ty := (← inferType xs[i]).replaceFVars (xs.extract 0 i) ys
      withLocalDecl names[i]! bi ty fun y => go (i + 1) (ys.push y)
    else k ys
  go 0 #[]

/-- Run `k` with the binder infos of the local variables `xs` set to `bi`, except for instance
binders, which stay: how one variable is bound explicitly in a type and implicitly in a lemma. -/
def withBinderInfo (xs : Array Expr) (bi : BinderInfo) (k : TermElabM α) : TermElabM α := do
  let bs ← xs.filterMapM fun x => do
    if (← x.fvarId!.getBinderInfo).isInstImplicit then return none
    return some (x.fvarId!, bi)
  withNewBinderInfos bs k

/-! ### Declarations -/

/-- Add a declaration, checked by the kernel before returning: with `Elab.async`, `addDecl`
checks definitions and theorems in a separate task, so a rejection would only be logged and the
constant would stay (as an axiom) for the next steps to trip over. -/
def addDeclSync (decl : Declaration) : CoreM Unit :=
  withOptions (Elab.async.set · false) <| addDecl decl

private def checkClosed (name : Name) (es : Array Expr) : MetaM Unit := do
  for e in es do
    let e ← instantiateMVars e
    if e.hasFVar || e.hasMVar then
      throwError "internal error: the generated declaration `{name}` is not closed:{indentExpr e}"

/-- Does a component of `n` occur twice in it? -/
def hasDupComponent (n : Name) : Bool :=
  let cs := n.components
  cs.any fun c => cs.count c > 1

/-- The declaration ranges of a generated declaration: those of the user's declaration `ref`.
A generated name with a repeated component (`T.F.T`, for a constructor `T` of `T`) gets none:
Mathlib's `dupNamespace` linter, which looks for the declarations with a range in a command,
would report it on the user's declaration, for a name the user did not choose. -/
private def addRanges (name : Name) (ref : Syntax) : TermElabM Unit := do
  if ref.getPos?.isSome && !hasDupComponent name then addDeclarationRangesFromSyntax name ref

/-- The declaration ranges of a declaration the user named, a type or a constructor, whatever
its name: those of its syntax `ref`, with the name as written `selection` as the selection range,
as `inductive` gives them. -/
def addRangesUser (name : Name) (ref : Syntax) (selection : Syntax := .missing) :
    TermElabM Unit := do
  if ref.getPos?.isSome then addDeclarationRangesFromSyntax name ref selection

/-- The subterms of `e` satisfying `p`, outermost first (not looking inside them). -/
partial def appsWhere (p : Expr → Bool) (e : Expr) : Array Expr :=
  if p e then #[e] else match e with
    | .app f a => appsWhere p f ++ appsWhere p a
    | .lam _ d b _ | .forallE _ d b _ => appsWhere p d ++ appsWhere p b
    | .letE _ t v b _ => appsWhere p t ++ appsWhere p v ++ appsWhere p b
    | .mdata _ b | .proj _ _ b => appsWhere p b
    | _ => #[]

/-- The first index from `i` on that is not fixed in `masks`, or whose type differs in the
types `toCheck` (the other types and the constructors, instantiated up to `i`). -/
private partial def fixedPrefix (masks : List (Array Bool)) (i : Nat) (type : Expr)
    (toCheck : List Expr) : MetaM Nat := do
  unless masks.all (fun m => i < m.size && m[i]!) && type.isForall do return i
  let d := type.bindingDomain!
  unless ← toCheck.allM fun t => pure t.isForall <&&> isDefEq t.bindingDomain! d do return i
  withLocalDeclD `a d fun a =>
    fixedPrefix masks (i + 1) (type.bindingBody!.instantiate1 a)
      (toCheck.map (·.bindingBody!.instantiate1 a))

/-- How many indices after the `numParams` parameters of the inductive types `types` are *fixed*
and become parameters, as Lean's `inductive` promotes them (`fixedIndicesToParams` in
`MutualInductive.lean`, private, ported here): a prefix of the indices that every constructor
takes as its own arguments at the same positions and passes unchanged to every recursive
occurrence. The types themselves do not change, only the number of parameters, which shapes the
recursor, `casesOn` and `noConfusion`. The types are not reduced: the inductive types are not
declared yet, and generated types are written out. -/
def fixedIndices (numParams : Nat) (types : List InductiveType) : MetaM Nat := do
  if !(← getOptions).getBool `inductive.autoPromoteIndices true then return 0
  let isInd (e : Expr) : Bool := types.any (e.getAppFn.isConstOf ·.name)
  let masks ← types.mapM fun t => do
    let arity ← forallTelescope t.type fun xs _ => pure xs.size
    let mut mask := Array.replicate arity false
    for i in [numParams:arity] do mask := mask.set! i true
    for c in t.ctors do
      mask ← forallTelescope c.type fun xs body => do
        let args := body.getAppArgs
        let mut mask := mask
        for i in [numParams:arity] do
          unless i < xs.size && i < args.size && xs[i]! == args[i]! do mask := mask.set! i false
        for x in xs.extract numParams xs.size do
          for e in appsWhere isInd (← instantiateMVars (← inferType x)) do
            let eArgs := e.getAppArgs
            for i in [numParams:arity] do
              unless i < eArgs.size && i < args.size && eArgs[i]! == args[i]! do
                mask := mask.set! i false
        return mask
    return mask
  forallBoundedTelescope types.head!.type numParams fun params type => do
    let others ← types.tail.mapM fun t => instantiateForall t.type params
    let ctors ← types.flatMapM fun t => t.ctors.mapM fun c => instantiateForall c.type params
    return (← fixedPrefix masks numParams type (others ++ ctors)) - numParams

/-- Add the inductive types `types` (mutual if several) with `numParams` parameters, then the
auxiliary constructions of Lean's `inductive` (`MutualInductive.lean`, whose `mkAuxConstructions`
is private): `recOn`, `casesOn`, `ctorIdx`, the constructor eliminators, `noConfusion`, `below`,
`brecOn`, `sizeOf` with its lemmas, and the injectivity theorems. As in `inductive`, fixed indices
become parameters (`fixedIndices`). Nested inductives (with auxiliary recursors) are not
generated and not supported. -/
def addInductive (levelParams : List Name) (numParams : Nat) (types : List InductiveType)
    (ref : Syntax := .missing) : TermElabM Unit := do
  let types ← types.mapM fun t => do
    return { t with
      type := ← instantiateMVars t.type
      ctors := ← t.ctors.mapM fun c => do return { c with type := ← instantiateMVars c.type } }
  for t in types do
    checkClosed t.name (#[t.type] ++ (t.ctors.map (·.type)).toArray)
  let numParams := numParams + (← fixedIndices numParams types)
  addDeclSync (.inductDecl levelParams numParams types false)
  let names := types.map (·.name)
  -- As in `inductive`: the constructions below compile against the type.
  compileDecls names.toArray
  for n in names do
    mkRecOn n
    mkCasesOn n
    mkCtorIdx n
    mkCtorElim n
    Lean.mkNoConfusion n
    mkBelow n
  for n in names do
    mkBRecOn n
  if let n :: _ := names then mkSizeOfInstances n
  for n in names do
    mkInjectiveTheorems n
  for t in types do
    addRanges t.name ref
    enableRealizationsForConst t.name
    for c in t.ctors do
      addRanges c.name ref
      enableRealizationsForConst c.name

/-- `I.casesOn` on `a : I args`, where `args` are all the arguments of `I`, parameters then
indices, however many of them `I` takes as parameters (`fixedIndices`): the motive is
`motive idx t` at universe `lvl`, and the minor premise of the constructor `c` is `minor c xs`, on
its arguments `xs` after the parameters. -/
def mkCasesOnApp (I : Name) (us : List Level) (args : Array Expr) (a : Expr) (lvl : Level)
    (motive : Array Expr → Expr → TermElabM Expr) (minor : Name → Array Expr → TermElabM Expr) :
    TermElabM Expr := do
  let info ← getConstInfoInduct I
  let ps := args.extract 0 info.numParams
  let idx := args.extract info.numParams args.size
  let ty ← instantiateForall (← instantiateTypeLevelParams info.toConstantVal us) ps
  let motive ← forallTelescope ty fun is _ =>
    withLocalDeclD `t (mkAppN (.const I us) (ps ++ is)) fun t => do
      mkLambdaFVars (is.push t) (← motive is t)
  let minors ← info.ctors.toArray.mapM fun c => do
    let cty ← instantiateForall (← instantiateTypeLevelParams (← getConstVal c) us) ps
    forallTelescope cty fun xs _ => do mkLambdaFVars xs (← minor c xs)
  return mkAppN (.const (mkCasesOnName I) (lvl :: us)) (ps ++ #[motive] ++ idx ++ #[a] ++ minors)

/-- Add a definition, noncomputable; `reducible` for an `abbrev`. -/
def addDef (name : Name) (levelParams : List Name) (type value : Expr) (ref : Syntax := .missing)
    (reducible := false) : TermElabM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  checkClosed name #[type, value]
  let height := getMaxHeight (← getEnv) value + 1
  let hints := if reducible then .abbrev else .regular height
  addDeclSync <| .defnDecl { name, levelParams, type, value, hints, safety := .safe }
  modifyEnv (addNoncomputable · name)
  if reducible then setReducibleAttribute name
  addRanges name ref
  enableRealizationsForConst name

/-- Add a theorem with the proof `value`. -/
def addThm (name : Name) (levelParams : List Name) (type value : Expr) (ref : Syntax := .missing) :
    TermElabM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  checkClosed name #[type, value]
  addDeclSync <| .thmDecl { name, levelParams, type, value }
  addRanges name ref
  enableRealizationsForConst name

/-! ### Protection -/

/-- The generated declarations `T.s` that are `protected`, by `s`, relative to their type `T`
(a block `Blk`, an open type `T.Open` of a mixed block): after `open T` they are not `s`, only
`T.s` (and `t.s` by dot notation). As Lean's `inductive` protects its auxiliary constructions
(`recOn`, `noConfusion`, `below`, `brecOn`, `ctorIdx`, …, which the inductive types generated here
get from it), the other generated declarations that are not user API: `ctor`, `bisim`, the
functor `F`, `contract`; and the internals: the signature (`Shape`, `B`, `Ix`, `ShapeP`, `idx`, `sig`), the
isomorphism and its laws (`toC`, `ofC`, `ofC_toC`, `toC_ofC`, `ofC_map`, `rel_ofC`), the model's
recursor and its rule (`recPos`, `recAux`, `recPos_ctor`), the model's `fold_ctor`, the cases
before the cast (`casesOnAux`, `casesOn_ctor`), and the open type `T.Open` of a mixed block.
Everything under `T.Poly` (step 5) is protected too (`isProtectedGen`). Not protected, as with
`inductive`: the types, the constructors `T.cᵢ`, the eliminators `rec` and `casesOn` (as Lean
leaves them) and our `fold`, `corec`, `dtor`, and the user-facing lemmas (`T.cᵢ_inj`,
`T.cᵢ_ne_cⱼ`, `T.rec_cᵢ`, `T.fold_cᵢ`, `T.casesOn_cᵢ`, `T.dtor_cᵢ`, `T.ctor_cᵢ`, `dtor_corec`,
`corec_eq`, `corec_unique`, `fold_eq`, `fold_unique`, `ctor_dtor`, `dtor_ctor`, `ctor_injective`,
and those of `T.F`). -/
def protectedGen : List String :=
  ["ctor", "bisim", "F", "contract",
    "Shape", "B", "Ix", "ShapeP", "idx", "sig",
    "toC", "ofC", "ofC_toC", "toC_ofC", "ofC_map", "rel_ofC",
    "recPos", "recAux", "recPos_ctor", "fold_ctor", "casesOnAux", "casesOn_ctor",
    "Open"]

/-- Is `n` a generated declaration of the type (block, open type) `owner` to protect: `owner.s`
with `s` in `protectedGen` (or `s'`, the name `owner.s` takes when `s` is the type's own name,
`Ctx.gen`), or under `owner.Poly`? -/
def isProtectedGen (owner n : Name) : Bool :=
  if !owner.isPrefixOf n || owner == n then false else
  match (n.replacePrefix owner .anonymous).components.map (·.toString (escape := false)) with
  | [s] =>
    let last := match owner with | .str _ l => l | _ => ""
    protectedGen.contains s || (s == last ++ "'" && protectedGen.contains last)
  | "Poly" :: _ :: _ => true
  | _ => false

/-- Protect the generated declarations of the types (blocks, open types) `owners` that
`isProtectedGen` names, but for the names the user wrote, `user` (the types, the constructors).
Run once a command has declared everything, so that protection changes no generated statement. -/
def protectGenerated (owners user : Array Name) : CoreM Unit := do
  let env ← getEnv
  let mut ns : Array Name := #[]
  for o in owners do
    for s in protectedGen do
      ns := ns.push (.str o s)
      if let .str _ l := o then
        if l == s then ns := ns.push (.str o (s ++ "'"))
  ns := env.constants.foldStage2 (fun ns n _ =>
    if owners.any fun o => (o ++ `Poly).isPrefixOf n then ns.push n else ns) ns
  for n in ns do
    if env.contains n && !user.contains n && owners.any (isProtectedGen · n) then
      modifyEnv (addProtected · n)

/-! ### Proofs by tactic -/

/-- Run `k` with the definitional unfolding of Lean before 4.34: implicit arguments and the
types of assigned metavariables are compared at the default transparency, unfolding definitions.
For the generated proofs that need it only: a term of the signature is often the expected one
only after unfolding (`sig.idx b` is an index once `b` is a constructor). -/
def withUnfolding [MonadWithOptions m] (k : m α) : m α :=
  withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency false
    |>.setBool `backward.isDefEq.respectTransparency.types false) k

/-- A proof of `type` in the current local context, found by running `tac` on a goal metavariable:
for a proof inside a term, or a statement over the local variables of a generator. The tactic
must close the goal. -/
def proveHere (type : Expr) (tac : MVarId → TermElabM Unit) : TermElabM Expr := do
  let g ← mkFreshExprSyntheticOpaqueMVar type
  tac g.mvarId!
  Term.synthesizeSyntheticMVarsNoPostponing
  let pf ← instantiateMVars g
  if pf.hasExprMVar then
    throwError "internal error: the generated proof of{indentExpr type}\nis incomplete"
  return pf

/-- A proof of the closed statement `type`, as `proveHere` in an empty local context (so that
the tactic sees only the statement's hypotheses). -/
def prove (type : Expr) (tac : MVarId → TermElabM Unit) : TermElabM Expr :=
  withLCtx {} {} (proveHere type tac)

/-- Close the goal `g` by the tactic script `tac`. -/
def runTac (g : MVarId) (tac : TSyntax `tactic) : TermElabM Unit := do
  let gs ← Tactic.run g (Tactic.evalTactic tac)
  unless gs.isEmpty do
    throwError "internal error: unsolved goals{goalsToMessageData gs}"

/-- The simp set of `simp only [lemmas]`: theorems are rewrite rules, definitions are unfolded.
-/
def simpOnlyCtx (lemmas : Array Name) (failIfUnchanged := true) : MetaM Simp.Context := do
  let thms ← (lemmas ++ Tactic.simpOnlyBuiltins).foldlM (init := ({} : SimpTheorems)) fun s n => do
    if (← getConstInfo n).isTheorem then s.addConst n else s.addDeclToUnfold n
  Simp.mkContext (config := { failIfUnchanged }) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)

/-- `simp only [lemmas]` on the goal `g`: the remaining goal, if any. Without `failIfUnchanged`, a
goal on which the lemmas make no progress is returned as it is. -/
def simpOnlyStep (g : MVarId) (lemmas : Array Name) (failIfUnchanged := true) :
    MetaM (Option MVarId) := do
  let (r?, _) ← simpGoal g (← simpOnlyCtx lemmas failIfUnchanged) #[← Simp.getSimprocs]
  return r?.map (·.2)

/-- Close the goal `g` as `simp only [lemmas]` does (with its built-in lemmas and the default
simprocs), from `MetaM`. -/
def simpOnly (g : MVarId) (lemmas : Array Name) : MetaM Unit := do
  if let some g' ← simpOnlyStep g lemmas then
    throwError "internal error: `simp only` did not close the goal{indentD (MessageData.ofGoal g')}"

/-! ### Attributes -/

/-- Make `name` a simp lemma, as `@[simp]` does. -/
def addSimp (name : Name) : MetaM Unit :=
  addSimpTheorem simpExtension name (post := true) (inv := false) .global (eval_prio default)

/-- Apply attributes given as syntax (`@[…]` contents), for those with no simpler API. -/
def addAttrs (name : Name) (attrs : Array (TSyntax ``Parser.Term.attrInstance)) :
    TermElabM Unit := do
  Term.applyAttributes name (← elabAttrs attrs)

end Codata.Gen
