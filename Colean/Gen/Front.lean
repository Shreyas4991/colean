import Colean.Gen.Ctx
import Colean.Syntax

/-!
# Generators on `Expr`: the front end

*Spec.* Input: the syntax of a `codata`/`data` declaration, or of the declarations of a
`mutual` block (`DeclStx`). Output: their context `Ctx` (`Gen/Ctx.lean`), passed to a
continuation inside the local context its free variables live in (`withCtx`). Nothing is
declared here, except the index `Blk.Ix` of a block.

The declarations are elaborated as Lean's `inductive` elaborates them
(`Lean.Elab.MutualInductive`):

1. the headers, the parameters (with auto-bound implicits) and the declared sorts, whose binders
   are the indices; in a block, the parameters must agree (names and types), and so must the
   universes where they are written;
2. the types as local variables `Tₘ : ∀ params idx, Type ?r` (`withAuxDecl`), one universe for
   all, against which each constructor is elaborated to one telescope ending in `Tₘ params idx`:
   binders left of the colon and arrows right of it are the same thing; unnamed arguments are
   named `a₁, a₂, …` by position. The universe `?r` is then the placeholder `uT`
   (`Gen/Ctx.lean`), unless the constructors fixed it;
3. the index binders and the arguments of every constructor are opened as local variables, and
   each argument is classified on its elaborated type (`ArgKind`): an occurrence is an application
   of a type being defined to the parameters and indices; arguments under a telescope and nested
   ones are recognised after `whnfOcc`, the occurrence structure of a nested argument by
   `Gen/Occ.lean`.

A block is one family over `Blk.Ix params`, an inductive type with a constructor per type, whose
arguments are that type's indices: the family's one index binder is `m : Blk.Ix params`, an
occurrence `Tₘ params idx` is at `Blk.Ix.Tₘ idx`, and a constructor name shared by several types
is qualified (`T_c`) in the block-level inductives.

Besides type checking, the analysis checks what the construction needs: the result type of a
constructor is the type applied to its parameters (and indices), recursive arguments are
explicit, no argument type and no index of the result depends on a recursive argument, and the
types being defined do not occur in the domain of a function.

The universe of the declared sort is not used: the type's universe is the model's. The section
variables the declarations use become their first parameters, as with `inductive`; they keep
their binder infos in the generated types.
-/

open Lean Meta Elab Term

namespace Codata.Gen

/-- A `codata` or `data` declaration as written. -/
structure DeclStx where
  co : Bool
  T : Ident
  ps : Array Syntax
  sort? : Option Syntax
  ctors : Array (TSyntax ``codataCtor)
  ref : Syntax
  deriving Inhabited

/-- Read a `codata` or `data` declaration. -/
def DeclStx.read? (stx : Syntax) : Option DeclStx :=
  match stx with
  | `(codata $T:ident $ps:bracketedBinder* $[: $s]? $cs:codataCtor*) =>
    some { co := true, T, ps := ps.map (·.raw), sort? := s.map (·.raw), ctors := cs, ref := stx }
  | `(data $T:ident $ps:bracketedBinder* $[: $s]? $cs:codataCtor*) =>
    some { co := false, T, ps := ps.map (·.raw), sort? := s.map (·.raw), ctors := cs, ref := stx }
  | _ => none

/-- Elaborate binders one by one, so that each variable knows the binder it comes from. -/
private partial def elabBindersRefs (bs : Array Syntax)
    (k : Array Expr → Array Syntax → TermElabM α) (i : Nat := 0) (xs : Array Expr := #[])
    (refs : Array Syntax := #[]) : TermElabM α := do
  if h : i < bs.size then
    Term.elabBinders #[bs[i]] fun ys =>
      elabBindersRefs bs k (i + 1) (xs ++ ys) (refs ++ ys.map fun _ => bs[i])
  else k xs refs

/-- A header, closed: `∀ params, sort`, and the number of parameters. The names `shorts` of the
types being defined are not auto-bound. -/
private def elabHeader (shorts : Array Name) (ps : Array Syntax) (sort? : Option Syntax) :
    TermElabM (Expr × Nat) :=
  Term.withAutoBoundImplicitForbiddenPred (shorts.contains ·) <|
  Term.withAutoBoundImplicit <| Term.elabBinders ps fun params => do
    let sort ← match sort? with
      | some s => Term.elabType s
      | none => pure (mkSort Level.one)
    Term.synthesizeSyntheticMVarsNoPostponing
    let params ← Term.addAutoBoundImplicits params none
    unless params.all (·.isFVar) do throwError "could not infer the types of the parameters"
    let sort ← instantiateMVars sort
    unless ← isTypeFormerType sort do
      throwErrorAt (sort?.getD .missing)
        "the declared sort must be a sort or a family of sorts, `(i : I) → Type u`"
    return (← mkForallFVars params sort, params.size)

/-- Do two headers have the same first `n` binders, by name (up to the hygiene of anonymous
binders, `[Inhabited α]`) and type? -/
private partial def sameParams (a b : Expr) (n : Nat) : MetaM Bool := do
  if n == 0 then return true
  let .forallE na da ba _ := a | return false
  let .forallE nb db bb _ := b | return false
  unless na.eraseMacroScopes == nb.eraseMacroScopes && (← isDefEq da db) do return false
  withLocalDeclD na da fun x => sameParams (ba.instantiate1 x) (bb.instantiate1 x) (n - 1)

/-- The universe of the sort at the end of a declared sort `(i : I) → Type u`. -/
private def sortLevel (sort : Expr) : MetaM Level :=
  forallTelescopeReducing sort fun _ body => do
    match ← whnf body with
    | .sort l => return l
    | _ => throwError "the declared sort must be a sort or a family of sorts, `(i : I) → Type u`"

/-- `name` made unique among `used` by primes. -/
private partial def unique (used : Array Name) (name : Name) : Name :=
  if used.contains name then unique used (name.appendAfter "'") else name

/-- Name the unnamed binders of a telescope: the `i`-th (from 0) `base` with subscript `i + 1`,
made distinct from the named ones. -/
private def nameBinders (base : String) (e : Expr) : Expr := Id.run do
  let mut named := #[]
  let mut t := e
  while t.isForall do
    if !t.bindingName!.hasMacroScopes then named := named.push t.bindingName!
    t := t.bindingBody!
  return renameForalls (fun i n => if n.hasMacroScopes then
    unique named (Name.mkSimple (base ++ Nat.toSubscriptString (i + 1))) else n) e

/-- A constructor, elaborated against the local variable `Tv` of its type: its name, its type
`∀ args, T params idx` (closed over the arguments only), the syntax of each binder argument, and
the syntax of the arrow arguments (the result type). -/
private def elabCtor (Tv : Expr) (params : Array Expr) (nIdx : Nat) (c : TSyntax ``codataCtor) :
    TermElabM (Name × Expr × Array Syntax × Syntax) := do
  let `(codataCtor| | $name:ident $bs:bracketedBinder* $[: $resTy?]?) := c
    | throwUnsupportedSyntax
  withRef c <| Term.withAutoBoundImplicit <| elabBindersRefs bs fun xs refs => do
    let res ← match resTy? with
      | some r => Term.elabType r
      | none =>
        if nIdx > 0 then throwErrorAt c "the constructor needs a result type"
        pure (mkAppN Tv params)
    Term.synthesizeSyntheticMVarsNoPostponing
    let xs' ← Term.addAutoBoundImplicits xs none
    unless xs'.all (·.isFVar) do throwError "could not infer the types of the arguments"
    let refs := Array.replicate (xs'.size - xs.size) c.raw ++ refs
    let ty ← instantiateMVars (← mkForallFVars xs' res)
    if ty.hasExprMVar then throwError "could not infer the types of the arguments{indentExpr ty}"
    return (name.getId, nameBinders "a" ty, refs, (resTy?.map (·.raw)).getD c)

/-- Open the telescopes `tys`, one after the other, keeping their variables. -/
private def openTelescopes (tys : Array Expr) (k : Array (Array Expr × Expr) → TermElabM α) :
    TermElabM α :=
  let rec go (i : Nat) (acc : Array (Array Expr × Expr)) : TermElabM α := do
    if h : i < tys.size then forallTelescope tys[i] fun xs body => go (i + 1) (acc.push (xs, body))
    else k acc
  go 0 #[]

/-- Classify a constructor argument by its type. -/
private def classify (b : Block) (fam? : Option FamIdx) (ty : Expr) : TermElabM ArgKind := do
  unless b.mentions ty do return .data
  let e ← whnfOcc ty
  if let some idx := b.holeOf? e then return .plain idx
  if b.isTypeApp e then throwError badOcc
  let arity? ← withReducible <| forallTelescopeReducing ty fun ys body => do
    if ys.isEmpty || (b.holeOf? (← whnfOcc body)).isNone then return none
    for y in ys do
      if b.mentions (← inferType y) then throwError badDomain
    return some ys.size
  if let some n := arity? then return .fn n
  let occ ← instantiateMVars (← occOf (b.holes fam?) ty)
  let oty ← whnfR (← inferType occ)
  let args := oty.getAppArgs
  if fam?.isSome then
    unless oty.isAppOfArity ``Codata.IOcc 5 do
      throwError "internal error: unexpected occurrence structure{indentExpr oty}"
    return .nest { occ, sh := args[1]!, pos := args[2]!, pidx? := some args[3]! }
  unless oty.isAppOfArity ``Codata.Occ 3 do
    throwError "internal error: unexpected occurrence structure{indentExpr oty}"
  return .nest { occ, sh := args[0]!, pos := args[1]!, pidx? := none }

/-- A constructor's analysis with its metavariables instantiated (the universe of the types). -/
private def instantiateCtor (c : Ctor) : MetaM Ctor := do
  let inst (e : Expr) : MetaM Expr := instantiateMVars e
  let args ← c.args.mapM fun a => do
    let kind ← match a.kind with
      | .plain idx => pure (.plain (← idx.mapM inst))
      | .nest n => do
        let n' : Nest := {
          occ := ← inst n.occ, sh := ← inst n.sh, pos := ← inst n.pos
          pidx? := ← n.pidx?.mapM inst }
        pure (.nest n')
      | k => pure k
    return { a with type := ← inst a.type, kind }
  return { c with args, idx := ← c.idx.mapM inst, uidx := ← c.uidx.mapM inst }

/-- The packed index type of index binders: `(i₁ : I₁) ×' (i₂ : I₂) ×' …`, `I₁`, or `Unit`. -/
private def packedType (idx : Array Expr) : MetaM Expr := do
  if idx.isEmpty then return mkConst ``Unit
  let mut acc ← inferType idx.back!
  for m' in [0:idx.size - 1] do
    acc ← mkAppM ``PSigma #[← mkLambdaFVars #[idx[idx.size - 2 - m']!] acc]
  return acc

/-- Run `k` on the types being defined as auxiliary local variables, as `inductive` does: the
`m`-th named `shorts[m]` (and `names[m]` in full), of type `tys[m]`. -/
private def withAuxDecls (shorts names : Array Name) (tys : Array Expr)
    (k : Array Expr → TermElabM α) : TermElabM α :=
  let rec go (i : Nat) (acc : Array Expr) : TermElabM α := do
    if h : i < shorts.size then
      withAuxDecl shorts[i] tys[i]! names[i]! fun v => go (i + 1) (acc.push v)
    else k acc
  go 0 #[]

/-- Run `k` on local variables named `names` of types `tys`. -/
private def withLocalDeclsD' (names : Array Name) (tys : Array Expr)
    (k : Array Expr → TermElabM α) : TermElabM α :=
  let rec go (i : Nat) (acc : Array Expr) : TermElabM α := do
    if h : i < names.size then withLocalDeclD names[i] tys[i]! fun v => go (i + 1) (acc.push v)
    else k acc
  go 0 #[]

/-- The index of a block, `Blk.Ix params`: an inductive type with a constructor per type, named
like it, whose arguments are that type's indices. Returns the constructors applied to the
parameters, and the type. -/
private def declareIx (ix : Name) (userLevels : List Name) (params declParams : Array Expr)
    (types : Array (Name × Array Expr)) (ref : Syntax) : TermElabM (Array Expr × Expr) := do
  let lvls ← types.foldlM (init := #[]) fun acc (_, idx) => do
    return acc ++ (← idx.mapM fun i => do getLevel (← inferType i))
  let r := resultLevel lvls
  let ty ← withBinderInfo declParams .default do mkForallFVars params (mkSort r.succ)
  let ctorName (n : Name) : Name := ix ++ Name.mkSimple n.lastComponentAsString
  withLocalDeclD `Ix ty fun Iv => do
    let ctorTys ← types.mapM fun (_, idx) =>
      withBinderInfo params .implicit do mkForallFVars (params ++ idx) (mkAppN Iv params)
    let us ← levelParamsOf userLevels [] (ctorTys.push ty)
    let Ic := Lean.mkConst ix (us.map mkLevelParam)
    addInductive us params.size [{
      name := ix, type := ty
      ctors := (types.zip ctorTys).toList.map fun ((n, _), t) =>
        { name := ctorName n, type := t.replaceFVar Iv Ic } }] ref
    let ctors := types.map fun (n, _) =>
      mkAppN (Lean.mkConst (ctorName n) (us.map mkLevelParam)) params
    return (ctors, mkAppN Ic params)

/-- Analyse the declarations `decls`, one or the types of a `mutual` block, all `codata` (`co`)
or all `data`, and run `k` on their context, inside the local context of the context's free
variables. `ref` is the command. `vars` are the section variables: those the declarations use
become their first parameters, as with `inductive`. A block is one family over its index
`Blk.Ix`, which is declared here. -/
def withCtx (decls : Array DeclStx) (ref : Syntax) (vars : Array Expr) (k : Ctx → TermElabM α) :
    TermElabM α := do
  let co := decls[0]!.co
  let shorts := decls.map (·.T.getId)
  let ns ← getCurrNamespace
  let names := shorts.map (ns ++ ·)
  let isBlock := decls.size ≥ 2
  let name := if isBlock then
      ns ++ Name.mkSimple ("_".intercalate (shorts.map (·.toString)).toList)
    else names[0]!
  -- As in `inductive`: no `_recApp` annotations on the occurrences of the types.
  withRef ref <| Term.withoutErrToSorry <| Term.withoutSavingRecAppSyntax do
  let hdrs ← decls.mapM fun d => withRef d.ref do elabHeader shorts d.ps d.sort?
  let (hdr₀, np) := hdrs[0]!
  -- The types of a block agree on their parameters, and on their universe where it is written.
  for d in decls, (hdr, n) in hdrs do
    unless n == np && (← sameParams hdr₀ hdr np) do
      throwErrorAt d.T
        "the types of a mutual block must have the same parameters as `{decls[0]!.T}`"
  -- The placeholder universe of the types: a name no user can write.
  let uT := Name.mkNum `uT 0
  forallBoundedTelescope hdr₀ np fun params sort₀ => do
  -- The sorts, with their binders named.
  let sorts ← hdrs.mapIdxM fun m (hdr, _) => do
    let sort ← if m == 0 then pure sort₀ else instantiateForall hdr params
    forallTelescopeReducing sort fun is body => do
      if (← instantiateMVars (← mkForallFVars is (mkSort Level.zero))).hasMVar then
        throwErrorAt decls[m]!.ref "could not infer the types of the indices"
      return nameBinders "i" (← mkForallFVars is body)
  let written := (decls.zip sorts).filter (·.1.sort?.isSome)
  if let some (d₀, s₀) := written[0]? then
    let l₀ ← sortLevel s₀
    for (d, s) in written do
      unless ← isLevelDefEq (← sortLevel s) l₀ do
        throwErrorAt d.T "the types of a mutual block must be in the same universe as `{d₀.T}`"
  -- The types' universe, a metavariable during the elaboration of the constructors: the
  -- placeholder if they leave it free.
  let r ← mkFreshLevelMVar
  let Ttys ← sorts.mapM fun sort =>
    forallTelescope sort fun is _ => mkForallFVars (params ++ is) (mkSort r.succ)
  let nIdx ← sorts.mapM fun sort => forallTelescope sort fun is _ => pure is.size
  withAuxDecls shorts names Ttys fun Tvs => do
  let ctors ← decls.mapIdxM fun m d => d.ctors.mapM fun c => do
    let (n, ty, refs, resRef) ← elabCtor Tvs[m]! params nIdx[m]! c
    return (m, n, ty, refs, resRef, c)
  let ctors := ctors.flatten
  -- The user's universes, auto-bound ones included.
  let userLevels := (← Term.getLevelNames).reverse
  -- The types' universe, if the constructors fix it; otherwise still a metavariable, which a leaf
  -- with an instance at one universe may fix during the analysis, and then the placeholder.
  let rLvl ← instantiateLevelMVars r
  let rId? := match rLvl with
    | .mvar id => some id
    | _ => none
  let ctors ← ctors.mapM fun (m, n, ty, refs, resRef, c) => do
    let ty ← instantiateMVars ty
    let others := (collectLevelMVars {} ty).result.filter (some · != rId?)
    if ty.hasExprMVar || !others.isEmpty then
      throwErrorAt resRef "could not determine the universes of the arguments{indentExpr ty}"
    return (m, n, ty, refs, resRef, c)
  -- As in `inductive`: the section variables the declarations use (with those their types use)
  -- are parameters; the others leave the local context.
  let (_, used) ← (do
    for (hdr, _) in hdrs do (← instantiateMVars hdr).collectFVars
    for (_, _, ty, _) in ctors do ty.collectFVars).run {}
  let (lctx, localInsts, vars) ← Meta.removeUnused vars used
  withLCtx lctx localInsts do
  -- The occurrences `T params idx` become `T vars params idx`, for local variables `T` over all
  -- the parameters.
  let Ttys ← Tvs.mapM fun Tv => do mkForallFVars vars (← instantiateMVars (← inferType Tv))
  withLocalDeclsD' shorts Ttys fun Tvs' => do
  let ctors := ctors.map fun (m, n, ty, refs, resRef, c) =>
    (m, n, ty.replaceFVars Tvs (Tvs'.map (mkAppN · vars)), refs, resRef, c)
  let params := vars ++ params
  openTelescopes sorts fun idxs => do
  let idxs := idxs.map (·.1)
  openTelescopes (ctors.map (·.2.2.1)) fun opened => do
  let types := (Array.range decls.size).map fun m =>
    { name := names[m]!, fvar := Tvs'[m]!, idx := idxs[m]!, ref := decls[m]!.ref
      nameRef := decls[m]!.T : TypeInfo }
  let declParams := params.extract vars.size params.size
  -- A block: its index `Blk.Ix`, and the one index binder `m : Blk.Ix params` of the family.
  let (ixCtors, ixType?) ← if isBlock then
      let (cs, I) ← declareIx (name ++ `Ix) userLevels params declParams
        (types.map fun t => (t.name, t.idx)) ref
      pure (cs, some I)
    else pure (#[], none)
  let usedNames ← (params ++ idxs.flatten ++ opened.flatMap (·.1)).mapM (·.fvarId!.getUserName)
  let mName ← plainOr (usedNames ++ ctors.map (·.2.1)) `m
  let withFamIdx (k : Array Expr → TermElabM α) : TermElabM α :=
    match ixType? with
    | some I => withLocalDeclD mName I fun mv => k #[mv]
    | none => k idxs[0]!
  withFamIdx fun idx => do
  let b : Block := { params, types, ixCtors, uT, fixedLvl? := some rLvl }
  let J ← match ixType? with
    | some I => pure I
    | none => packedType idx
  let Jlvl ← typeLevel J
  let ctx0 : Ctx :=
    { b with co, name, ref, userLevels, nVars := vars.size, idx, J, Jlvl, ctors := #[] }
  let fam? := ctx0.famIdx?
  -- Constructor names shared by several types of a block are qualified in the block-level
  -- inductives.
  let clash (n : Name) : Bool :=
    ((Array.range decls.size).filter fun m => ctors.any fun c => c.1 == m && c.2.1 == n).size ≥ 2
  let mut out : Array Ctor := #[]
  for (m, cname, _, refs, resRef, c) in ctors, (xs, body) in opened do
    let badRes : MessageData :=
      m!"the result type must be `{shorts[m]!}` applied to its parameters and indices"
    let some (m', uidx) := b.occ? (← whnfOcc body) | throwErrorAt c badRes
    unless m' == m do throwErrorAt c badRes
    let mut args : Array ArgInfo := #[]
    for x in xs, i in [0:xs.size] do
      let ref := refs[i]?.getD resRef
      let decl ← x.fvarId!.getDecl
      let ty ← instantiateMVars decl.type
      let kind ← withRef ref do
        for a in args do
          unless a.kind.isData do
            if ty.containsFVar a.fvar.fvarId! then
              throwError "the type of an argument may not depend on a recursive argument"
        let kind ← classify b fam? ty
        unless kind.isData || decl.binderInfo.isExplicit do
          throwError "implicit binders must not be recursive"
        pure kind
      args := args.push
        { fvar := x, name := decl.userName, bi := decl.binderInfo, type := ty, kind, ref }
    for a in args do
      unless a.kind.isData do
        if uidx.any (·.containsFVar a.fvar.fvarId!) then
          throwErrorAt c "the indices of the result type may not depend on a recursive argument"
    let fname := if clash cname then
        Name.mkSimple (shorts[m]!.lastComponentAsString ++ "_" ++ cname.toString)
      else cname
    out := out.push
      { name := cname, fname, owner := m, args, idx := b.wrap m uidx, uidx, ref := c
        nameRef := c.raw[1] }
  -- The universe, fixed now or the placeholder; the analysis at it.
  let fixedLvl? ← match ← instantiateLevelMVars r with
    | .mvar id => assignLevelMVar id (.param uT); pure none
    | l => pure (some l)
  let ctors ← out.mapM fun c => instantiateCtor c
  k { ctx0 with ctors, fixedLvl? }

end Codata.Gen
