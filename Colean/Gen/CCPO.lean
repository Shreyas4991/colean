import Colean.Gen.Decl
import Colean.Model.CCPO
import Colean.Model.Occ

/-!
# Generators on `Expr`: an order for `partial_fixpoint` (`with_ccpo`)

*Spec.* Input: a type `T` declared by a single `codata` declaration, with parameters and at most
one index, and the constructor without arguments chosen as the bottom (by name,
`with_ccpo (bot := c)`, or the first one).
Output, from the type's public declarations (`T.contract`, `T.F`, `T.F.Rel`, `T.F.rel_map`,
`T.sig`, `T.toC`, `T.ofC` and their laws) and the theory of `Model/CCPO.lean`:

* `T.instCCPO : Lean.Order.CCPO (T params idx)`, at every index: the order of approximation with
  the bottom constructor at the bottom (`Codata.Contract.ccpo`), which `partial_fixpoint` takes as
  the order of a definition with result type `T params idx`;
* `T.approx_iff : x ⊑ y ↔ x = T.c₀ ∨ T.F.Rel (fun x y => x ⊑ y) x.dtor y.dtor`, the order
  unfolded once (`c₀` the bottom constructor);
* `T.approx_coind`: a relation `R` with `R x y → x ⊑ y ∨ T.F.Rel (R ∪ ⊑) x.dtor y.dtor` is
  contained in the order (coinduction up to the order);
* `T.bot_eq : Lean.Order.bot = T.c₀`, a `simp` lemma;
* for every constructor `c` with a recursive argument plain, under a function, or nested,
  `T.monotone_c : monotone fun x => T.c a₁ (t₁ x) …` for monotone `tᵢ`, tagged
  `@[partial_fixpoint_monotone]`: what `partial_fixpoint` needs to prove a definition monotone
  through the constructors. A nested argument with a plain structure (`List T`, `T × T`, at one
  index of a family too) is ordered through it (`Occ.order`, `nestOrder`), for which
  `Model/CCPO.lean` proves the maps and constructors of the leaves and the pairs of a product
  monotone; the other arguments are fixed.

The bottom of a family is a constructor at every index: its result index is the index variable
and it has no other argument (`| stop {n : Nat} : T n`).

This step is separate from the declaration, as step 5 is: it runs on a declared type when the
attribute `with_ccpo` is applied to it (`CodataCmd.lean`), reads only the environment, and changes
nothing the declaration generated. A failure is an error of the attribute, and restores the state.
The pieces of the order (`K`, the bottom layer `e`, the container `C`, the proof that the bottom
has no positions, the lifting `T.F.Rel` with `T.F.rel_map` and `T.rel_ofC`) are elaborated from
short terms on the generated constants (`mkCIdent`), so that unification adapts the plain type's
contract over `Unit` and a family's alike; the statements are built as `Expr`s; the proofs
instantiate the theory, and the monotonicity lemmas apply the constructor of `T.F.Rel` and close
its premises by the hypotheses, or by reflexivity for a fixed nested argument (`Occ.rel_refl`,
`IOcc.rel_refl`).

Not supported: a type of a `mutual` block or of an inner run of a `mixed_mutual` block (each type
needs its bottom, and the order is over the block's index), several indices (the contract is over
the packed index), and recursion through a nested argument by anything but the maps and the
constructors of a leaf and the pairs of a product: through a composite (`some [f n]` in
`Option (List T)`) or a function into a leaf, whose order would have to be Lean's where Lean has
one.
-/

open Lean Meta Elab Term

namespace Codata.Gen.CCPO

/-- An error of the attribute, at its syntax. -/
def fail (msg : MessageData) : TermElabM α :=
  throwError m!"with_ccpo: {msg}"

/-- Elaborate `stx` against `type`, every metavariable solved. -/
def elabAt (stx : Term) (type : Expr) : TermElabM Expr := do
  let e ← withSynthesize <| elabTermEnsuringType stx type
  let e ← instantiateMVars e
  if e.hasExprMVar then
    throwError "internal error: the generated term{indentExpr e}\nhas unsolved metavariables"
  return e

/-- `f a`, with `a` elaborated from `stx` against the type of the next argument of `f`. -/
def appElab (f : Expr) (stx : Term) : TermElabM Expr := do
  let .forallE _ d _ _ ← whnf (← inferType f)
    | throwError "internal error: no argument left in{indentExpr f}"
  return mkApp f (← elabAt stx d)

/-- How a field of a constructor of `T.F` mentions the variable `X`. -/
inductive Kind where
  | data
  /-- `X idx`, or under a telescope of arrows. -/
  | recur
  | nest

/-- The kind of a field of type `ty`, in the variable `X`. -/
def kindOf (X ty : Expr) : MetaM Kind := do
  unless ty.containsFVar X.fvarId! do return .data
  forallTelescopeReducing ty fun ys body => do
    let doms ← ys.anyM fun y => return (← inferType y).containsFVar X.fvarId!
    if !doms && body.getAppFn == X && !(body.getAppArgs.any (·.containsFVar X.fvarId!)) then
      return .recur
    return .nest

variable (T : Name)

/-- The constructor `T.F.c` at the parameters `ps` and the family `X`, with metavariables for its
other arguments, made to produce `T.F ps X idx`: the values of these arguments, or none when one
is not determined by the index (the constructor has an argument). -/
def atIndex (c : Name) (ps : Array Expr) (X : Expr) (target : Expr) :
    TermElabM (Option (Array Expr × Expr)) := do
  let f ← mkConstWithFreshMVarLevels c
  let (ms, _, ty) ← forallMetaTelescope (← instantiateForall (← inferType f) ps)
  unless ← isDefEq ty target do return none
  unless ← isDefEq ms[0]! X do return none
  let vals ← ms.mapM instantiateMVars
  if vals.any (·.hasExprMVar) then return none
  return some (vals.extract 1 vals.size, mkAppN (mkAppN f ps) vals)

/-- The order of a nested argument whose premise in `T.F.Rel` is `prem`, when its structure is a
plain one (`Occ`: a leaf `Occ.ofIso G`, a product, …), or a plain one at one index of a family
(`IOcc.ofOcc o i`): the order through it, `Occ.order`. -/
def nestOrder (prem : Expr) : MetaM (Option Expr) := do
  let args := prem.getAppArgs
  if prem.isAppOfArity ``Codata.Occ.Rel 11 then
    return some (← mkAppOptM ``Codata.Occ.order #[none, none, none, args[3]!, args[6]!, none])
  if prem.isAppOfArity ``Codata.IOcc.Rel 13 && args[5]!.isAppOfArity ``Codata.IOcc.ofOcc 6 then
    let o := args[5]!.getAppArgs
    let X ← whnfR (mkApp args[8]! o[5]!)
    return some (← mkAppOptM ``Codata.Occ.order #[none, none, none, o[4]!, X.headBeta, none])
  return none

/-- `T.monotone_c` for the constructor `T.F.c`, when it has a recursive argument plain or under a
function, or nested with a plain structure: these arguments monotone functions (a nested one for
the order through its structure, `nestOrder`), the others fixed. -/
def genMonotone (c : Name) (ps : Array Expr) (plain : Bool)
    (Tps I σ T' F' K e C Rel' relOfC : Expr)
    (instAt : Array Expr → Expr) (lvls : List Name) (v : Name) : TermElabM Unit := do
  let short := c.componentsRev.head!
  let user := T ++ short
  let relC := T ++ `F.Rel ++ short
  let f ← mkConstWithFreshMVarLevels c
  -- The fields at a variable `X`, to find the recursive ones.
  let fty ← instantiateForall (← inferType f) ps
  let .forallE _ XTy _ _ := fty | throwError "internal error: `{c}` has no family argument"
  let kinds ← withLocalDeclD `X XTy fun X => do
    forallTelescope (fty.bindingBody!.instantiate1 X) fun as _ =>
      as.mapM fun a => do kindOf X (← inferType a)
  unless kinds.any (!· matches .data) do return
  let X := if plain then Tps else T'
  unless ← isDefEq XTy (← inferType X) do
    throwError "internal error: unexpected family argument of `{c}`"
  let cty := fty.bindingBody!.instantiate1 X
  forallTelescope cty fun as concl => do
  -- A field that depends on a recursive one: no lemma.
  for a in as, k in kinds, i in [0:as.size] do
    unless k matches .data do
      let later := as.extract (i + 1) as.size
      if ← later.anyM fun b => return (← inferType b).containsFVar a.fvarId! then
        return
  let idx := if plain then Lean.mkConst ``Unit.unit else concl.getAppArgs.back!
  let TI := if plain then Tps else mkApp Tps idx
  let inst := instAt (if plain then #[] else #[idx])
  let R ← withLocalDeclD `j I fun j => do
    mkLambdaFVars #[j] (← mkAppOptM ``Codata.Contract.Approx #[I, T', F', K, e, j])
  let relGoal (a b : Expr) : MetaM Expr := return (Rel'.beta #[R, idx, a, b]).headBeta
  -- The premises of `T.F.Rel.c` at the fields, one per recursive argument: a nested argument is
  -- monotone when its premise is `Occ.Rel o o R`, for the order `Occ.order o`.
  let orders ← do
    let a := mkAppN (mkAppN f ps) (#[X] ++ as)
    let g ← mkFreshExprSyntheticOpaqueMVar (← relGoal a a)
    let gs ← g.mvarId!.apply (← mkConstWithFreshMVarLevels relC)
    let mut out : Array (Option Expr) := #[]
    let mut j := 0
    for a in as, k in kinds do
      match k with
      | .data => out := out.push none
      | .recur =>
        out := out.push (some (← synthInstance
          (← mkAppM ``Lean.Order.PartialOrder #[← inferType a])))
        j := j + 1
      | .nest =>
        let prem ← instantiateMVars (← gs[j]!.getType)
        j := j + 1
        out := out.push (← nestOrder prem)
    pure out
  unless orders.any (·.isSome) do return
  withLocalDecl `γ .implicit (mkSort (.param v)) fun γ => do
  withLocalDecl `inst .instImplicit (← mkAppM ``Lean.Order.PartialOrder #[γ]) fun instγ => do
  -- The monotone fields as functions of `x : γ`, with their monotonicity.
  let monos := (as.zip orders).filterMap fun (a, o) => o.map (a, ·)
  let rec withFns (i : Nat) (fs hs : Array Expr) (k : Array Expr → Array Expr → TermElabM Unit) :
      TermElabM Unit := do
    if h : i < monos.size then
      let (a, order) := monos[i]
      let n ← a.fvarId!.getUserName
      let A ← inferType a
      withLocalDecl n .implicit (← mkArrow γ A) fun fa => do
      let mono ← mkAppOptM ``Lean.Order.monotone #[γ, instγ, A, order, fa]
      withLocalDeclD (n.appendBefore "h") mono fun ha => withFns (i + 1) (fs.push fa) (hs.push ha) k
    else k fs hs
  withFns 0 #[] #[] fun fs hs => do
  let fixed := (as.zip orders).filterMap fun (a, o) => if o.isSome then none else some a
  let argsAt (x : Expr) : Array Expr := Id.run do
    let mut out := #[]
    let mut j := 0
    for a in as, o in orders do
      if o.isSome then
        out := out.push (mkApp fs[j]! x)
        j := j + 1
      else out := out.push a
    return out
  let mono ← withLocalDeclD `x γ fun x => do
    mkLambdaFVars #[x] (← mkAppOptM user ((ps ++ argsAt x).map some))
  let po ← mkAppOptM ``Lean.Order.CCPO.toPartialOrder #[TI, inst]
  let stmt ← mkAppOptM ``Lean.Order.monotone #[γ, instγ, TI, po, mono]
  -- The proof: the constructor of `T.F.Rel` at `f x` and `f y`, its premises by the hypotheses or
  -- reflexivity, then `approx_ctor`.
  let value ← withLocalDeclD `x γ fun x => withLocalDeclD `y γ fun y => do
    let rxy ← mkAppOptM ``Lean.Order.PartialOrder.rel #[γ, instγ, x, y]
    withLocalDeclD `h rxy fun h => do
    let a := mkAppN (mkAppN f ps) (#[X] ++ argsAt x)
    let b := mkAppN (mkAppN f ps) (#[X] ++ argsAt y)
    let g ← mkFreshExprSyntheticOpaqueMVar (← relGoal a b)
    let gs ← g.mvarId!.apply (← mkConstWithFreshMVarLevels relC)
    let cands := hs.map fun h' => mkAppN h' #[x, y, h]
    for g in gs do
      let ty ← g.getType
      let mut done := false
      for p in cands do
        if ← isDefEq ty (← inferType p) then
          g.assign p
          done := true
          break
      unless done do
        runTac g (← `(tactic| first
          | exact Codata.Occ.rel_refl _ (Codata.Contract.approx_refl _ _) _
          | exact Codata.IOcc.rel_refl _ (fun _ => Codata.Contract.approx_refl _ _) _))
    let rel ← mkAppOptM ``Codata.Contract.Container.rel_of
      #[σ, T', F', K, C, Rel', relOfC, R, idx, a, b, ← instantiateMVars g]
    let pf ← mkAppOptM ``Codata.Contract.approx_ctor #[I, T', F', K, e, idx, a, b, rel]
    mkLambdaFVars #[x, y, h] pf
  let xs := ps ++ #[γ, instγ] ++ fixed ++ fs ++ hs
  let type ← mkForallFVars xs stmt
  let value ← mkLambdaFVars xs value
  let name := T ++ (`monotone).appendAfter ("_" ++ short.toString)
  addThm name (lvls ++ [v]) type value
  addAttrs name #[← `(Parser.Term.attrInstance| partial_fixpoint_monotone)]

/-- The generator of `with_ccpo` on the type `T`, with the bottom constructor `bot?` (named by
`(bot := c)`, short or qualified), or the first constructor without arguments. -/
def genCCPO (bot? : Option Name) : TermElabM Unit := do
  let env ← getEnv
  let some kci := env.find? (T ++ `contract)
    | fail m!"`{.ofConstName T}` is not a type declared by a single `codata` declaration (the \
        types of `mutual` and `mixed_mutual` blocks are not supported)"
  let us := kci.levelParams.map mkLevelParam
  forallTelescope (← instantiateTypeLevelParams kci.toConstantVal us) fun ps body => do
  withBinderInfo ps .implicit do
  unless body.isAppOfArity ``Codata.Contract 3 do
    fail m!"`{.ofConstName T}` is a `data` type: the order is for `codata` types"
  let #[I, T', F'] := body.getAppArgs | unreachable!
  let K := mkAppN (.const (T ++ `contract) us) ps
  -- `T ps`, and whether there is an index.
  let plain := I.isConstOf ``Unit
  let Tps := if plain then T'.bindingBody! else T'
  unless Tps.getAppFn.isConstOf T do
    fail m!"`{.ofConstName T}` has several indices, which are not supported yet"
  let lvls := kci.levelParams
  let ixName ← if plain then pure `i else
    forallTelescope (← inferType Tps) fun is _ => is[0]!.fvarId!.getUserName
  let FN := T ++ `F
  let some (.inductInfo finfo) := env.find? FN
    | fail m!"`{.ofConstName T}` is a type of an inner run of a `mixed_mutual` block, which is not \
        supported"
  if env.contains (T ++ `instCCPO) then
    fail m!"the order of `{.ofConstName T}` is already declared"
  -- The bottom constructor, at every index, and its arguments there.
  let bot ← withLocalDeclD `i I fun i => do
    let X := if plain then Tps else T'
    let target ← Core.betaReduce (← whnf (mkApp2 F' T' i))
    let tryCtor (c : Name) : TermElabM (Option (Name × Array Expr × Expr)) := do
      let some (vals, e) ← atIndex c ps X target | return none
      return some (c, ← vals.mapM (mkLambdaFVars #[i] ·), ← mkLambdaFVars #[i] e)
    match bot? with
    | some b =>
      -- `nil`, or written qualified, `T.nil`.
      let b := (b.replacePrefix T .anonymous).replacePrefix (T.componentsRev.head!) .anonymous
      let c := FN ++ b
      unless finfo.ctors.contains c do
        fail m!"`{b}` is not a constructor of `{.ofConstName T}`"
      let some r ← tryCtor c
        | fail m!"the bottom `{.ofConstName (T ++ b)}` must be a constructor without arguments\
            {if plain then m!"" else m!", at every index"}"
      return r
    | none =>
      for c in finfo.ctors do
        if let some r ← tryCtor c then return r
      fail m!"`{.ofConstName T}` has no constructor without arguments\
        {if plain then m!"" else m!" at every index"}, which the order takes as its bottom"
  let (botF, botVals, e) := bot
  let botName := T ++ botF.componentsRev.head!
  -- The signature, the container and the emptiness of the bottom's positions.
  let σ ← mkAppOptM (T ++ `sig) (ps.map some)
  let id (n : Name) : Term := mkCIdent (T ++ n)
  let CTy ← mkAppOptM ``Codata.Contract.Container #[σ, T', F', K]
  let (toC, ofC, ofC_toC, toC_ofC, ofC_map) :=
    (id `toC, id `ofC, id `ofC_toC, id `toC_ofC, id `ofC_map)
  let C ← elabAt (← `(⟨$toC, $ofC, $ofC_toC, $toC_ofC, fun f _ z => $ofC_map f z⟩)) CTy
  let ccpo0 ← mkAppOptM ``Codata.Contract.ccpo #[σ, T', F', K, e, C]
  let hbot ← elabAt (← `(fun _ b => by cases b)) (← whnf (← inferType ccpo0)).bindingDomain!
  let ccpoFn := mkApp ccpo0 hbot
  let pieces := #[σ, T', F', K, e, C, hbot]
  -- The index binders of the statements, and the index of the theory.
  let withIdx {α} (k : Array Expr → Expr → Expr → TermElabM α) : TermElabM α := do
    if plain then k #[] (Lean.mkConst ``Unit.unit) Tps
    else withLocalDecl ixName .implicit I fun i => k #[i] i (mkApp Tps i)
  let instName := T ++ `instCCPO
  let instAt (is : Array Expr) : Expr := mkAppN (.const instName us) (ps ++ is)
  let relAt (A inst x y : Expr) : MetaM Expr := do
    let po ← mkAppOptM ``Lean.Order.CCPO.toPartialOrder #[A, inst]
    mkAppOptM ``Lean.Order.PartialOrder.rel #[A, po, x, y]
  -- The instance.
  withIdx fun is idx TI => do
    let type ← mkForallFVars (ps ++ is) (← mkAppM ``Lean.Order.CCPO #[TI])
    let value ← mkLambdaFVars (ps ++ is) (mkApp ccpoFn idx)
    addDef instName lvls type value (reducible := true)
    addInstance instName .global (eval_prio default)
  -- The lifting by `T.F.Rel`, with the two facts relating it to the canonical one.
  let thmIff ← mkAppOptM ``Codata.Contract.ccpo_rel_iff_of (pieces.map some)
  let thmIff ← appElab thmIff (← if plain then
      `(fun R _ a b => $(id `F.Rel) (R ()) a b) else `(fun R _ a b => $(id `F.Rel) R a b))
  let Rel' ← instantiateMVars (thmIff.appArg!)
  let thmIff ← appElab thmIff (← if plain then
      `(fun _ _ z => $(id `F.rel_map) _ _ _ z fun p => p.2)
    else `(fun _ _ z => $(id `F.rel_map) _ _ _ z fun _ p => p.2))
  let relOfC ← elabAt (← `(fun R _ z z' h => $(id `rel_ofC) R z z' h))
    (← whnf (← inferType thmIff)).bindingDomain!
  let thmIff := mkApp thmIff relOfC
  -- `T.approx_iff`
  withIdx fun is idx TI => do
    withLocalDecl `x .implicit TI fun x => withLocalDecl `y .implicit TI fun y => do
    let inst := instAt is
    let R ← if plain then
        withLocalDeclD `x TI fun a => withLocalDeclD `y TI fun b => do
          mkLambdaFVars #[a, b] (← relAt TI inst a b)
      else withLocalDeclD `j I fun j => do
        let TJ := mkApp Tps j
        withLocalDeclD `x TJ fun a => withLocalDeclD `y TJ fun b => do
          mkLambdaFVars #[j, a, b] (← relAt TJ (instAt #[j]) a b)
    let botV ← mkAppOptM botName ((ps ++ botVals.map (·.beta #[idx])).map some)
    let rhs := mkOr (← mkEq x botV)
      (← mkAppM (T ++ `F.Rel) #[R, ← mkAppM (T ++ `dtor) #[x], ← mkAppM (T ++ `dtor) #[y]])
    let type ← mkForallFVars (ps ++ is ++ #[x, y]) (mkIff (← relAt TI inst x y) rhs)
    let value ← mkLambdaFVars (ps ++ is ++ #[x, y]) (mkAppN thmIff #[idx, x, y])
    addThm (T ++ `approx_iff) lvls type value
  -- `T.approx_coind`
  withIdx fun is idx TI => do
    let inst := instAt is
    -- The relations `fun j x y => R j x y ∨ x ⊑ y` and the hypothesis, at an index `j`.
    let atJ (k : Array Expr → Expr → Expr → TermElabM Expr) : TermElabM Expr :=
      if plain then k #[] TI inst else
        withLocalDeclD `j I fun j => do mkForallFVars #[j] (← k #[j] (mkApp Tps j) (instAt #[j]))
    let RTy ← atJ fun _ A _ => do mkArrow A (← mkArrow A (mkSort .zero))
    withLocalDeclD `R RTy fun R => do
    let Rup ← if plain then
        withLocalDeclD `x TI fun a => withLocalDeclD `y TI fun b => do
          mkLambdaFVars #[a, b] (mkOr (mkApp2 R a b) (← relAt TI inst a b))
      else withLocalDeclD `j I fun j => do
        let TJ := mkApp Tps j
        withLocalDeclD `x TJ fun a => withLocalDeclD `y TJ fun b => do
          mkLambdaFVars #[j, a, b] (mkOr (mkAppN R #[j, a, b]) (← relAt TJ (instAt #[j]) a b))
    let HTy ← atJ fun js A instJ => do
      withLocalDeclD `x A fun a => withLocalDeclD `y A fun b => do
        let step := mkOr (← relAt A instJ a b)
          (← mkAppM (T ++ `F.Rel) #[Rup, ← mkAppM (T ++ `dtor) #[a], ← mkAppM (T ++ `dtor) #[b]])
        mkForallFVars #[a, b] (← mkArrow (mkAppN R (js ++ #[a, b])) step)
    withLocalDeclD `H HTy fun H => do
    withLocalDecl `x .implicit TI fun x => withLocalDecl `y .implicit TI fun y => do
    withLocalDeclD `h (mkAppN R (is ++ #[x, y])) fun h => do
    let (R', H') := if plain then (Lean.mkLambda `j .default I R, Lean.mkLambda `j .default I H)
      else (R, H)
    let pf ← mkAppOptM ``Codata.Contract.ccpo_coind_of
      ((pieces ++ #[Rel', relOfC, R', H', idx, x, y, h]).map some)
    let xs := ps ++ #[R, H] ++ is ++ #[x, y, h]
    addThm (T ++ `approx_coind) lvls (← mkForallFVars xs (← relAt TI inst x y))
      (← mkLambdaFVars xs pf)
  -- `T.bot_eq`
  withIdx fun is idx TI => do
    let botV ← mkAppOptM botName ((ps ++ botVals.map (·.beta #[idx])).map some)
    let lhs ← mkAppOptM ``Lean.Order.bot #[TI, instAt is]
    let type ← mkForallFVars (ps ++ is) (← mkEq lhs botV)
    let value ← mkLambdaFVars (ps ++ is)
      (← mkAppOptM ``Codata.Contract.bot_eq ((pieces.push idx).map some))
    addThm (T ++ `bot_eq) lvls type value
    addSimp (T ++ `bot_eq)
  -- The monotonicity lemmas of the constructors.
  let v := (freshLevelNames 1 lvls).head!
  for c in finfo.ctors do
    genMonotone T c ps plain Tps I σ T' F' K e C Rel' relOfC instAt lvls v

end Codata.Gen.CCPO
