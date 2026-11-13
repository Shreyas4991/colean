import Colean.Gen.Derive.Simp

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

The step is in parts, each on the ones before: the holes and the structures of the fields
(`Derive/Holes.lean`), the presentation (`Derive/Pres.lean`), the layer and its laws
(`Derive/Layer.lean`), the fixpoint and the instances (`Derive/Fix.lean`), the `simp` lemmas
(`Derive/Simp.lean`); this file runs them (`genPoly`, `deriveInstances`).

Scope: in a block, a nested argument with positions at several types of the block inside a named
type constructor (`List (Ping × Pong)`) gets its instances, but not its `simp` lemmas, which
state the members by the type of each, and the step warns. A hole in the same field as `T` has a
structure in two variables unless it is in another argument of a leaf than `T` (`E α (T α)` inside
a list), or under a functor on families: the hole is constant there. A hole that is a family (an
`IPolyIso` instance) is not supported: `Model/Poly.lean` has the fixpoint for a parameter that is
a type.
-/

open Lean Meta Elab Term

namespace Codata.Gen

namespace Ctx

variable (ctx : Ctx)

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
  let short (n : Name) : MessageData := m!"`{(privateToUserName n).replacePrefix ns .anonymous}`"
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
