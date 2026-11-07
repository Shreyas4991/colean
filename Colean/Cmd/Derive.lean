import Colean.Cmd.Surface
import Colean.Model.Poly

/-!
# Deriving `PolyIso` for a declared type

*Spec.* Input: a type that is already completely declared: the analysis of its declaration and
its public declarations (`T`, `T.F`, `T.dtor`, `T.corec`, `T.fold`, `T.contract`, …). Output: the
instances `PolyIso` and `PolyMap` for `fun X => T (H₁ X) … (Hₙ X)`, for `H₁`, …, `Hₙ` themselves
instances, so that later declarations can nest through `T`.

This step is separate from the declaration of the type. It runs after it, nothing in the
declaration depends on it, and it cannot affect it: on failure every declaration of this step is
rolled back and a warning is logged, and the type is simply not available for nesting.

The parameters of `T` that may vary, the *holes*, are those of sort `Type u` used only in
fields whose type has an occurrence structure in them, and that no later type depends on.
A hole in a field makes that field a parameter position; the other parameters stay constant.
With the holes fixed, the layer `T.F (H X) Y` is presented as `Lay P B X Y` (`T.Poly.toL`,
`T.Poly.ofL`) and the generic theorems of `Model/Poly.lean` do the rest, from the contract.

Scope: a single type without indices. Mutual blocks and indexed families are skipped.
-/

open Lean Elab Command Lean.Parser.Term

namespace Codata

open Ctx

/-- A parameter that may vary, and the names of its premises. -/
private structure Hole where
  a : Ident
  ty : Term
  /-- Its sort in the second instantiation, for `PolyMap`. -/
  ty' : Term
  H : Ident
  H' : Ident
  S : Ident
  R : Ident

/-- A field at a parameter position: its name and the structure of its type in the hole. -/
private abbrev HoleField := Ident × OccInfo

private def isTypeSort (ty : Term) : Bool := ty.raw.isOfKind ``Parser.Term.type

/-- The universe name of `Type u`, when it is a plain name. -/
private def typeLevelName? (ty : Term) : Option Name :=
  let stx := ty.raw
  if stx.isOfKind ``Parser.Term.type && stx.getNumArgs == 2 && stx[1].getNumArgs == 1 &&
      stx[1][0].isIdent then some stx[1][0].getId else none

/-- `Type u'` for `Type u`. -/
private def withLevel (ty : Term) (u : Ident) : Term :=
  let stx := ty.raw
  ⟨Syntax.node .none ``Parser.Term.type #[stx[0], Syntax.node .none nullKind #[u.raw]]⟩

/-- The parameters, one per name. -/
private def paramList (ctx : Ctx) : CommandElabM (Array (Ident × Term)) := do
  let mut out := #[]
  for b in ctx.pExp do
    let (ids, ty, _) ← readBinder ⟨b.raw⟩
    out := out ++ ids.map (·, ty)
  return out

/-- Does the tree mention one of the names, outside its holes? -/
private partial def treeMentions (names : Array Name) : OccTree → Bool
  | .const t => mentionsAny t.raw names
  | .hole _ => false
  | .prod l r | .sum l r => treeMentions names l || treeMentions names r
  | .pi _ A _ body | .sigma _ A body => mentionsAny A.raw names || treeMentions names body
  | .leaf G _ arg => mentionsAny G.raw names || treeMentions names arg
  | .ileaf G _ _ arg => mentionsAny G.raw names || treeMentions names arg

private def holeOf (a : Name) (t : Term) : Option (Array Term) :=
  if t.raw.isIdent && t.raw.getId.eraseMacroScopes == a then some #[] else none

/-- The parameters that may vary. -/
private partial def findHoles (ctx : Ctx) (cands : Array (Ident × Term)) :
    CommandElabM (Array (Ident × Term)) := do
  let names := cands.map (·.1.getId)
  let mut bad : Array Name := #[]
  for c in ctx.ctors do
    let mut scope := ctx.pExp
    for (g, k) in c.groups.zipIdx do
      match g.kind with
      | .data =>
        let ms := names.filter fun n => mentionsAny g.ty.raw #[n]
        if ms.size ≥ 2 then
          bad := bad ++ ms
        else if let some a := ms[0]? then
          let treeOk ← try
              discard <| occTreeOf (holeOf a) #[a] scope g.ty
              pure true
            catch _ => pure false
          let later := (c.groups.extract (k + 1) c.groups.size).any fun g' =>
            mentionsAny g'.ty.raw (g.ids.map (·.getId))
          if !treeOk || later then bad := bad.push a
        scope := scope.push (← mkBinder g.implicit g.ids g.ty)
      | .pos _ => pure ()
      | .fn tele _ =>
        bad := bad ++ names.filter fun n => tele.any fun (_, d) => mentionsAny d.raw #[n]
      | .occ info =>
        bad := bad ++ names.filter fun n => treeMentions #[n] info.tree
  if bad.isEmpty then return cands
  findHoles ctx (cands.filter fun (a, _) => !bad.contains a.getId)

/-- A tree in the hole, with the premise `H` at the holes. -/
private partial def plugHole (H occ : Term) : OccTree → OccTree
  | .hole idx => .leaf H occ (.hole idx)
  | .prod l r => .prod (plugHole H occ l) (plugHole H occ r)
  | .sum l r => .sum (plugHole H occ l) (plugHole H occ r)
  | .pi a A p body => .pi a A p (plugHole H occ body)
  | .sigma a A body => .sigma a A (plugHole H occ body)
  | .leaf G o arg => .leaf G o (plugHole H occ arg)
  | .ileaf G o p arg => .ileaf G o p (plugHole H occ arg)
  | t => t

private def polyName (ctx : Ctx) (s : String) : Ident :=
  mkIdent (.str (.str ctx.tName "Poly") s)

/-- `@f args`. -/
private def mkAppT' (f : Ident) (args : Array Term) : CommandElabM Term :=
  `(@$f:ident $args*)

/-- Generate the instances for the holes. -/
private def genInstances (ctx : Ctx) (params holesA : Array (Ident × Term)) : CommandElabM Unit := do
  let isHole (n : Name) : Bool := holesA.any (·.1.getId == n)
  let consts := params.filter fun (a, _) => !isHole a.getId
  let constNames := consts.map (·.1.getId)
  let constTys := consts.map (·.2)
  let x := mkIdent `poly_x
  let x' := mkIdent `poly_x'
  elabCommand (← `(universe $x:ident $x':ident))
  -- The holes and their premises. A hole's universe changes in the second instantiation, unless
  -- a constant parameter shares it.
  let mut hs : Array Hole := #[]
  let mut sUnivs : Array (Ident × Ident) := #[]
  for i in [0:holesA.size] do
    let (a, ty) := holesA[i]!
    let s := mkIdent (Name.mkSimple s!"poly_s{i}")
    let p := mkIdent (Name.mkSimple s!"poly_p{i}")
    elabCommand (← `(universe $s:ident $p:ident))
    sUnivs := sUnivs.push (s, p)
    let ty' ← match typeLevelName? ty with
      | some u =>
        if constTys.any fun t => mentionsAny t.raw #[u] then pure ty else
          let u' := mkIdent (Name.mkSimple s!"poly_{u}'")
          unless (← getScope).levelNames.contains u'.getId do
            elabCommand (← `(universe $u':ident))
          pure (withLevel ty u')
      | none => pure ty
    hs := hs.push { a, ty, ty', H := mkIdent (Name.mkSimple s!"poly_H{i}")
                    H' := mkIdent (Name.mkSimple s!"poly_H'{i}")
                    S := mkIdent (Name.mkSimple s!"poly_S{i}")
                    R := mkIdent (Name.mkSimple s!"poly_R{i}") }
  let impC ← consts.mapM fun (c, ty) => `(bracketedBinderF| {$c:ident : $ty})
  let expC ← consts.mapM fun (c, ty) => `(bracketedBinderF| ($c:ident : $ty))
  let mut HB : Array (TSyntax ``bracketedBinderF) := #[]
  let mut HImp : Array (TSyntax ``bracketedBinderF) := #[]
  let mut HImp' : Array (TSyntax ``bracketedBinderF) := #[]
  let mut SRImp : Array (TSyntax ``bracketedBinderF) := #[]
  let mut SRExp : Array (TSyntax ``bracketedBinderF) := #[]
  let mut insts : Array (TSyntax ``bracketedBinderF) := #[]
  let mut insts' : Array (TSyntax ``bracketedBinderF) := #[]
  for (h, i) in hs.zipIdx do
    let (s, p) := sUnivs[i]!
    let (Hn, Hn', Sn, Rn, ty, ty') := (h.H, h.H', h.S, h.R, h.ty, h.ty')
    HB := HB.push (← `(bracketedBinderF| ($Hn:ident : Type $x → $ty)))
    HImp := HImp.push (← `(bracketedBinderF| {$Hn:ident : Type $x → $ty}))
    HImp' := HImp'.push (← `(bracketedBinderF| {$Hn':ident : Type $x' → $ty'}))
    SRImp := SRImp.push (← `(bracketedBinderF| {$Sn:ident : Type $s}))
    SRImp := SRImp.push (← `(bracketedBinderF| {$Rn:ident : $Sn → Type $p}))
    SRExp := SRExp.push (← `(bracketedBinderF| ($Sn:ident : Type $s)))
    SRExp := SRExp.push (← `(bracketedBinderF| ($Rn:ident : $Sn → Type $p)))
    insts := insts.push (← `(bracketedBinderF| [Codata.PolyIso $Hn $Sn $Rn]))
    insts' := insts'.push (← `(bracketedBinderF| [Codata.PolyIso $Hn' $Sn $Rn]))
  let cT : Array Term := consts.map (idT ·.1)
  let srT : Array Term := hs.foldl (fun acc h => acc ++ #[idT h.S, idT h.R]) #[]
  let psT := cT ++ srT
  let HsT : Array Term := hs.map (idT ·.H)
  let HsT' : Array Term := hs.map (idT ·.H')
  let X := mkIdent `poly_X
  let Y := mkIdent `poly_Y
  let pT (X : Ident) (prime : Bool) : CommandElabM (Array Term) :=
    ctx.pids.mapM fun id =>
      match hs.find? (·.a.getId == id.getId) with
      | some h => let Hn := if prime then h.H' else h.H; `($Hn:ident $X:ident)
      | none => pure (idT id)
  let pTX ← pT X false
  -- The fields at parameter positions, with their structures in the premises.
  let scope₀ := expC ++ HImp ++ SRImp ++ insts
  let mut fieldsAll : Array (Array HoleField) := #[]
  let mut holeIds : Array Name := #[]
  for c in ctx.ctors do
    let mut scope := scope₀
    let mut fields : Array HoleField := #[]
    for g in c.groups do
      if g.kind.isData then
        match hs.find? fun h => mentionsAny g.ty.raw #[h.a.getId] with
        | some h =>
          let an := h.a.getId
          let tree ← occTreeOf (holeOf an) #[an] scope g.ty
          let occ ← `(Codata.Occ.ofIso $(h.H))
          let tree := plugHole (idT h.H) occ tree
          let unit ← `(Unit)
          let o ← occTermOf false unit (fun _ => `(())) tree
          let (Sh, Pos, _) ← occShapes scope o false
          let info : OccInfo := { tree, o, Sh, Pos, indexed := false, pidx := Pos }
          fields := fields ++ g.ids.map (·, info)
          holeIds := holeIds ++ g.ids.map (·.getId)
        | none =>
          scope := scope.push (← mkBinder g.implicit g.ids g.ty)
    fieldsAll := fieldsAll.push fields
  let isHoleField (x : Ident) : Bool := holeIds.contains x.getId
  let plainGroups (c : CtorInfo) := c.groups.filter fun g =>
    g.kind.isData && !g.ids.any isHoleField
  let plainIds (c : CtorInfo) : Array Ident := (plainGroups c).foldl (· ++ ·.ids) #[]
  -- Hole fields are per constructor, so a repeated field name stays apart.
  let S₀ := polyName ctx "S"
  let P₀ := polyName ctx "P"
  let B₀ := polyName ctx "B"
  let Sp ← mkAppT S₀ psT
  let Pp ← mkAppT P₀ psT
  let Bp ← mkAppT B₀ psT
  let psB := expC ++ SRExp
  let sCtor (c : CtorInfo) : Ident := mkIdent (S₀.getId ++ c.fname.getId)
  let pCtor (c : CtorInfo) (x : Ident) : Ident := mkIdent (P₀.getId ++ (posCtorName c x).getId)
  let bCtor (c : CtorInfo) (x : Ident) : Ident := mkIdent (B₀.getId ++ (posCtorName c x).getId)
  let fieldShapeBinders (fields : Array HoleField) (implicit : Bool) :
      CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
    fields.mapM fun (x, info) => mkBinder implicit #[nestShapeId x] info.Sh
  -- The shapes.
  let mut sCtors : Array (TSyntax ``Parser.Command.ctor) := #[]
  for (c, m) in ctx.ctors.zipIdx do
    let bs := (← (plainGroups c).mapM fun g => mkBinder g.implicit g.ids g.ty) ++
      (← nestShapeBinders c false) ++ (← fieldShapeBinders fieldsAll[m]! false)
    sCtors := sCtors.push (← `(Parser.Command.ctor| | $(c.fname):ident $[$bs]*))
  elabCommand (← `(inductive $S₀:ident $[$psB]* where $[$sCtors:ctor]*))
  -- The positions.
  let sApp (c : CtorInfo) (fields : Array HoleField) : CommandElabM Term := do
    let ids := (plainIds c).map idT ++ nestShapeIds c ++ fields.map fun (x, _) => idT (nestShapeId x)
    `(@$(sCtor c):ident $psT* $ids*)
  let mut pCtors : Array (TSyntax ``Parser.Command.ctor) := #[]
  let mut bCtors : Array (TSyntax ``Parser.Command.ctor) := #[]
  for (c, m) in ctx.ctors.zipIdx do
    let fields := fieldsAll[m]!
    let dbs := (← (plainGroups c).mapM fun g => mkBinder true g.ids g.ty) ++
      (← nestShapeBinders c true) ++ (← fieldShapeBinders fields true)
    let shape ← sApp c fields
    let resP ← `($Pp $shape)
    let resB ← `($Bp $shape)
    for (x, info) in fields do
      let xs := nestShapeId x
      let Pos := info.Pos
      pCtors := pCtors.push (← `(Parser.Command.ctor|
        | $(posCtorName c x):ident $[$dbs]* (q : $Pos $xs) : $resP))
    for g in c.groups do
      match g.kind with
      | .data => pure ()
      | .pos _ =>
        for y in g.ids do
          bCtors := bCtors.push (← `(Parser.Command.ctor| | $(posCtorName c y):ident $[$dbs]* : $resB))
      | .fn tele _ =>
        let tbs ← teleBinders tele
        for y in g.ids do
          bCtors := bCtors.push (← `(Parser.Command.ctor|
            | $(posCtorName c y):ident $[$dbs]* $[$tbs]* : $resB))
      | .occ info =>
        for y in g.ids do
          let ys := nestShapeId y
          let Pos := info.Pos
          bCtors := bCtors.push (← `(Parser.Command.ctor|
            | $(posCtorName c y):ident $[$dbs]* (q : $Pos $ys) : $resB))
  elabCommand (← `(inductive $P₀:ident $[$psB]* : $Sp → Type _ where $[$pCtors:ctor]*))
  elabCommand (← `(inductive $B₀:ident $[$psB]* : $Sp → Type _ where $[$bCtors:ctor]*))
  -- The layer.
  let toL := polyName ctx "toL"
  let ofL := polyName ctx "ofL"
  let ofL_toL := polyName ctx "ofL_toL"
  let toL_ofL := polyName ctx "toL_ofL"
  let ofL_map := polyName ctx "ofL_map"
  let fixId := polyName ctx "fix"
  let FY ← mkAppT ctx.F (pTX.push (idT Y))
  let lay ← `(Codata.Lay $Pp $Bp $X $Y)
  let premises := impC ++ HB ++ SRImp ++ insts
  let toAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.zipIdx.mapM fun (c, m) => do
    let fields := fieldsAll[m]!
    let nested := c.nested ++ fields
    let zs : Array Ident ← nested.mapM fun (x, _) => freshId s!"z_{x.getId.toString}"
    let vals := (plainIds c).map idT ++ (← zs.mapM fun z => `($z:ident.1))
    let shape ← `(@$(sCtor c):ident $psT* $vals*)
    let mut pAlts : Array (TSyntax ``matchAlt) := #[]
    let mut bAlts : Array (TSyntax ``matchAlt) := #[]
    let zOf (x : Ident) : Ident := zs[(nested.findIdx? (·.1.getId == x.getId)).get!]!
    for (x, _) in fields do
      pAlts := pAlts.push (← `(matchAltExpr| | $(pCtor c x):ident q => $(zOf x):ident.2 q))
    for g in c.groups do
      match g.kind with
      | .data => pure ()
      | .pos _ =>
        for y in g.ids do
          bAlts := bAlts.push (← `(matchAltExpr| | $(bCtor c y):ident => $y:ident))
      | .fn tele _ =>
        let ys := teleIds tele
        for y in g.ids do
          bAlts := bAlts.push (← `(matchAltExpr| | $(bCtor c y):ident $ys* => $y:ident $ys*))
      | .occ .. =>
        for y in g.ids do
          bAlts := bAlts.push (← `(matchAltExpr| | $(bCtor c y):ident q => $(zOf y):ident.2 q))
    let pf ← if pAlts.isEmpty then `(fun p => nomatch p) else `(fun p => match p with $pAlts:matchAlt*)
    let bf ← if bAlts.isEmpty then `(fun b => nomatch b) else `(fun b => match b with $bAlts:matchAlt*)
    let layer ← `(⟨$shape, $pf, $bf⟩)
    let rhs ← if zs.isEmpty then pure layer else do
      let toCs ← nested.mapM fun (x, info) => `(Codata.Occ.toC $(info.o) $x:ident)
      `((fun $[$zs:ident]* => $layer) $toCs*)
    ctx.alt c #[← ctx.fPat c] rhs
  let discrsA := ctx.discrs (← `(a))
  elabCommand (← `(def $toL:ident $[$premises]* {$X:ident : Type $x} {$Y:ident : Type _} (a : $FY) :
      $lay := match $[$discrsA:term],* with $toAlts:matchAlt*))
  let ofAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.zipIdx.mapM fun (c, m) => do
    let fields := fieldsAll[m]!
    let hsP ← psT.mapM fun _ => `(_)
    let ids := (plainIds c).map idT ++ nestShapeIds c ++ fields.map fun (x, _) => idT (nestShapeId x)
    let spat ← `(@$(sCtor c):ident $hsP* $ids*)
    let mut args : Array Term := #[]
    for g in c.groups do
      for y in g.ids do
        match g.kind with
        | .data =>
          match fields.find? (·.1.getId == y.getId) with
          | some (_, info) =>
            let ys := nestShapeId y
            args := args.push (← `(Codata.Occ.ofC $(info.o) ⟨$ys, fun q => v ($(pCtor c y) q)⟩))
          | none => args := args.push (idT y)
        | .pos _ => args := args.push (← `(k $(bCtor c y)))
        | .fn tele _ =>
          let ys := teleIds tele
          args := args.push (← `(fun $[$ys:ident]* => k ($(bCtor c y) $ys*)))
        | .occ info =>
          let ys := nestShapeId y
          args := args.push (← `(Codata.Occ.ofC $(info.o) ⟨$ys, fun q => k ($(bCtor c y) q)⟩))
    let rhs ← `(@$(ctx.fCtor c):ident $pTX* $Y:ident $args*)
    let vp ← if fields.isEmpty then `(_) else `(v)
    let kp ← if c.hasRec then `(k) else `(_)
    ctx.alt c #[← `(⟨$spat, $vp, $kp⟩)] rhs
  let discrsZ := ctx.discrs (← `(z))
  elabCommand (← `(def $ofL:ident $[$premises]* {$X:ident : Type $x} {$Y:ident : Type _} (z : $lay) :
      $FY := match $[$discrsZ:term],* with $ofAlts:matchAlt*))
  -- Calls with every argument explicit: constants, premises, presentations, instances, then the
  -- rest. Nothing is left to inference, since `S` and `R` occur only in the layer.
  let call (f : Ident) (Hs : Array Term) (rest : Array Term) : CommandElabM Term := do
    let instH ← hs.mapM fun _ => `(_)
    let args := cT ++ Hs ++ srT ++ instH ++ rest
    `(@$f:ident $args*)
  let Xt := idT X
  let Yt := idT Y
  let hole ← `(_)
  let lhs₁ ← call ofL HsT #[Xt, Yt, ← call toL HsT #[Xt, Yt, ← `(a)]]
  elabCommand (← `(theorem $ofL_toL:ident $[$premises]* {$X:ident : Type $x} {$Y:ident : Type _}
      (a : $FY) : $lhs₁ = a := by
    cases a
    all_goals first | rfl | simp only [$toL:ident, $ofL:ident, Codata.Occ.ofC_toC']))
  let lhs₂ ← call toL HsT #[Xt, Yt, ← call ofL HsT #[Xt, Yt, ← `(z)]]
  elabCommand (← `(theorem $toL_ofL:ident $[$premises]* {$X:ident : Type $x} {$Y:ident : Type _}
      (z : $lay) : $lhs₂ = z := by
    obtain ⟨s, v, k⟩ := z
    cases s
    all_goals try simp only [$toL:ident, $ofL:ident]
    all_goals repeat rw [Codata.Occ.toC_ofC]
    all_goals refine congrArg (Sigma.mk _) (Prod.ext (funext fun p => ?_) (funext fun b => ?_))
    all_goals first | (cases p <;> rfl) | (cases b <;> rfl)))
  let Y' := mkIdent `poly_Y'
  let lay' ← `(Codata.Lay $Pp $Bp $X $Y)
  let lhs₃ ← call ofL HsT #[Xt, idT Y', ← `(Codata.Lay.map f z)]
  let rhs₃ ← call ofL HsT #[Xt, Yt, ← `(z)]
  elabCommand (← `(theorem $ofL_map:ident $[$premises]* {$X:ident : Type $x}
      {$Y:ident : Type _} {$Y':ident : Type _} (f : $Y → $Y') (z : $lay') :
      $lhs₃ = $(ctx.Fmap) f $rhs₃ := by
    obtain ⟨s, v, k⟩ := z
    cases s
    all_goals first | rfl | simp only [$ofL:ident, $(ctx.Fmap):ident, Codata.Lay.map, Codata.Occ.map_ofC]))
  -- The fixpoint at `X`, from the public declarations of the type.
  let Tx ← mkAppT ctx.T pTX
  let treeOf (B : Term) : CommandElabM Term :=
    if ctx.co then `(Codata.coTree $B) else `(Codata.inTree $B)
  let tree ← treeOf Bp
  let toLa (e : Term) : CommandElabM Term := call toL HsT #[Xt, hole, e]
  let ofLa (e : Term) : CommandElabM Term := call ofL HsT #[Xt, hole, e]
  let dL ← `(fun (a : $Tx) => $(← toLa (← `($(ctx.dtor) a))))
  let K ← mkAppT' ctx.contract pTX
  let fixBody : Term ← if ctx.co then do
      let ofLz ← `(fun z => $(← ofLa (← `(z))))
      let ofLtoL ← call ofL_toL HsT #[Xt, hole, hole]
      let ofLmap ← call ofL_map HsT #[Xt, hole, hole, ← `(f), ← `(z)]
      `(Codata.coFix $dL
          (fun c s => $(ctx.corec) (fun st => $(← ofLa (← `(c st)))) s)
          (fun c a => by rw [$(ctx.dtor_corec):ident, ← $ofL_map:ident, $toL_ofL:ident])
          (Codata.co_bisim $K $dL $ofLz (fun _ => $ofLtoL) (fun f z => $ofLmap)))
    else do
      let toLy ← `(fun y => $(← toLa (← `(y))))
      let ofLz ← `(fun z => $(← ofLa (← `(z))))
      let ofLtoL ← call ofL_toL HsT #[Xt, hole, ← `(a)]
      let ofLmap ← call ofL_map HsT #[Xt, hole, hole, ← `(f), ← `(z)]
      `(Codata.inFix (fun z => $(ctx.ctor) $(← ofLa (← `(z)))) $dL
          (fun z => by rw [$(ctx.dtor_ctor):ident, $toL_ofL:ident])
          (fun a => by rw [$ofL_toL:ident, $(ctx.ctor_dtor):ident])
          (fun a t => $(ctx.fold) (fun y => a $(← toLa (← `(y)))) t)
          (fun a z => by rw [$(ctx.fold_ctor):ident, ← $ofL_map:ident, $toL_ofL:ident])
          (Codata.in_ind $K $toLy $ofLz (fun a => $ofLtoL) (fun f z => $ofLmap)))
  elabCommand (← `(def $fixId:ident $[$premises]* ($X:ident : Type $x) :
      Codata.PolyFix $Pp $tree $X $Tx := $fixBody))
  -- The instances.
  let fam := if ctx.co then ``Signature.Cotype else ``Signature.Intype
  let famId := mkCIdent fam
  let shapesOf (B : Term) : CommandElabM Term := `($famId:ident (Codata.shapeSig $B) ())
  let W ← shapesOf Bp
  let path ← `(Codata.Path $Pp $tree)
  let fixAt (Hs : Array Term) : CommandElabM Term := call fixId Hs #[hole]
  let fixH ← fixAt HsT
  let fixH' ← fixAt HsT'
  let isoId := polyName ctx "instPolyIso"
  let mapId := polyName ctx "instPolyMap"
  let isoB := impC ++ HImp ++ SRImp ++ insts
  elabCommand (← `(instance $isoId:ident $[$isoB]* :
      Codata.PolyIso (fun ($X:ident : Type $x) => $Tx) $W $path :=
    ⟨Codata.PolyFix.equiv $fixH⟩))
  let pTX' ← pT X true
  let Tx' ← mkAppT ctx.T pTX'
  let mapB := impC ++ HImp ++ HImp' ++ SRImp ++ insts ++ insts'
  elabCommand (← `(instance $mapId:ident $[$mapB]* :
      Codata.PolyMap (fun ($X:ident : Type $x) => $Tx) (fun ($X:ident : Type $x') => $Tx') :=
    ⟨fun f a => Codata.PolyFix.map $fixH $fixH' f a,
      fun f a => Codata.PolyFix.equiv_map $fixH $fixH' f a⟩))
  -- `fun X => T A X` is `T A`: the instances at the identity in the last parameter, the other
  -- holes constant.
  let some last := ctx.pids.back? | return
  let some hLast := hs.back? | return
  unless hLast.a.getId == last.getId do return
  let others := hs.pop
  let aB ← others.mapM fun h => do
    let (a, ty) := (h.a, h.ty)
    `(bracketedBinderF| ($a:ident : $ty))
  let etaArgs : Array Term := ctx.pids.pop.map idT
  let etaApp ← mkAppT ctx.T etaArgs
  let Hid ← `(fun X => X)
  let etaHs ← hs.mapM fun h => if h.a.getId == last.getId then pure Hid else `(fun _ => $(h.a):ident)
  let etaSR : Array Term ← hs.foldlM (init := #[]) fun acc h => do
    if h.a.getId == last.getId then
      return acc ++ #[← `(Unit), ← `(fun _ => Unit)]
    return acc ++ #[idT h.a, ← `(fun _ => Empty)]
  let etaPs := cT ++ etaSR
  let Bε ← mkAppT B₀ etaPs
  let Pε ← mkAppT P₀ etaPs
  let treeε ← treeOf Bε
  let Wε ← shapesOf Bε
  let pathε ← `(Codata.Path $Pε $treeε)
  let etaB := impC ++ aB
  let instH ← hs.mapM fun _ => `(_)
  let isoArgs := cT ++ etaHs ++ etaSR ++ instH
  elabCommand (← `(instance $(polyName ctx "instPolyIsoEta"):ident $[$etaB]* :
      Codata.PolyIso $etaApp $Wε $pathε := @$isoId:ident $isoArgs*))
  -- Across universes only when the last parameter does not share its universe.
  let tied := match typeLevelName? hLast.ty with
    | some u => others.any fun h => mentionsAny h.ty.raw #[u]
    | none => true
  let lastTy := hLast.ty
  let lastTy' := if tied then hLast.ty else hLast.ty'
  let mapArgs := cT ++ etaHs ++ etaHs ++ etaSR ++ instH ++ instH
  elabCommand (← `(instance $(polyName ctx "instPolyMapEta"):ident $[$etaB]* :
      Codata.PolyMap ($etaApp : $lastTy → Type _) ($etaApp : $lastTy' → Type _) :=
    @$mapId:ident $mapArgs*))

/-- Generate the instances of a declared type, if it has holes. Failure is a warning: the
declarations of this step are rolled back, and the type stays as it is. -/
def deriveInstances (ctx : Ctx) : CommandElabM Unit := do
  if ctx.k != 0 || ctx.isMutual then return
  let params ← paramList ctx
  let cands := params.filter fun (a, ty) =>
    isTypeSort ty && !params.any fun (b, tb) => b.getId != a.getId && mentionsAny tb.raw #[a.getId]
  let saved ← get
  let fail (msg : MessageData) : CommandElabM Unit := do
    set saved
    logWarning m!"`{ctx.T}` cannot be nested through: no `Codata.PolyIso` instance was \
      generated. The type itself is not affected.\n{msg}"
  try
    let holesA ← findHoles ctx cands
    if holesA.isEmpty then return
    modify fun s => { s with messages := {} }
    elabCommand (← `(noncomputable section))
    elabCommand (← `(set_option Elab.async false))
    elabCommand (← `(set_option linter.dupNamespace false))
    elabCommand (← `(set_option backward.isDefEq.respectTransparency false))
    elabCommand (← `(set_option backward.isDefEq.respectTransparency.types false))
    genInstances ctx params holesA
    elabCommand (← `(end))
    let msgs := (← get).messages
    if msgs.hasErrors then
      let first := msgs.toList.find? (·.severity == .error)
      fail (first.map (·.data) |>.getD "")
    else
      modify fun s => { s with messages := saved.messages ++ msgs }
  catch e => fail e.toMessageData

end Codata
