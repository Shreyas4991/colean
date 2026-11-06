import Colean.Cmd.Analysis

/-!
# The command, step 2: the model

*Spec.* Input: the context and `T.F` (step 1). Output: a model of the contract for `F`:

* the signature `T.Shape`, `T.B`, `T.idx`, `T.Ix`, `T.sig`, the fixed data format of
  `Model/Cotype.lean`;
* the isomorphism `T.toC`/`T.ofC` between `F X` and the signature's layers, with its laws
  `ofC_toC`, `toC_ofC`, `ofC_map` (and `rel_ofC` for codata). These are the second of the two
  places where the command proves by tactic;
* the type `T` as `Cotype`/`Intype` of the signature, its `dtor`/`corec`/`dtor_corec`/`bisim`
  (or `ctor`/`fold`/`fold_ctor`), instantiated from the generic transport theorems through the
  isomorphism, and `T.contract`, the model packaged for the framework.

`T.corec` and `T.fold` are taken from the model rather than from `T.contract` because the
contract fixes one universe for the state; this is the one reason the framework step reads the
model (see `architecture.md`).
-/

open Lean Elab Command Lean.Parser.Term

namespace Codata

open Ctx

/-! ### The signature: shapes, positions and their indices -/

def genSignature (ctx : Ctx) : CommandElabM Unit := do
  let pExp := ctx.pExp
  let pImp := ctx.pImp
  let shapeCtors ← ctx.ctors.mapM fun c => do
    let bs := (← (c.groups.filter (·.kind.isData)).mapM fun g => mkBinder g.implicit g.ids g.ty)
      ++ (← nestShapeBinders c false)
    if ctx.idxed then
      let res ← appT ctx.Shapep c.idx
      `(Parser.Command.ctor| | $(c.fname):ident $[$bs]* : $res)
    else
      `(Parser.Command.ctor| | $(c.fname):ident $[$bs]*)
  let ixBExp ← ctx.ixBExp
  let ib ← ctx.ixB
  if ctx.idxed then
    elabCommand (← `(inductive $(ctx.Shape):ident $[$pExp]* : ∀ $[$ixBExp]*, Type _ where
      $[$shapeCtors:ctor]*))
  else
    elabCommand (← `(inductive $(ctx.Shape):ident $[$pExp]* where $[$shapeCtors:ctor]*))
  -- The positions, one constructor per recursive argument; and (indexed) their indices.
  let mut bCtors : Array (TSyntax ``Parser.Command.ctor) := #[]
  let mut idxAlts : Array (TSyntax ``matchAlt) := #[]
  for c in ctx.ctors do
    let dbs ← dataBindersImplicit c
    let res ← appT ctx.Bp (c.idx ++ #[← ctx.shapeApp c])
    for g in c.groups do
      match g.kind with
      | .data => pure ()
      | .pos idx =>
        for x in g.ids do
          bCtors := bCtors.push
            (← `(Parser.Command.ctor| | $(posCtorName c x):ident $[$dbs]* : $res))
          if ctx.idxed then
            let packed ← ctx.pack (idx.map (ctx.substBare c))
            idxAlts := idxAlts.push (← ctx.alt c #[← `(_), ← ctx.bPat c x #[]] packed)
      | .fn tele idx =>
        let tbs ← teleBinders tele
        let ys := (teleIds tele).map idT
        for x in g.ids do
          bCtors := bCtors.push (← `(Parser.Command.ctor|
            | $(posCtorName c x):ident $[$dbs]* $[$tbs]* : $res))
          if ctx.idxed then
            let packed ← ctx.pack (idx.map (ctx.substBare c))
            idxAlts := idxAlts.push (← ctx.alt c #[← `(_), ← ctx.bPat c x ys] packed)
      | .occ info =>
        for x in g.ids do
          let xs := nestShapeId x
          let Pos := info.Pos
          bCtors := bCtors.push (← `(Parser.Command.ctor|
            | $(posCtorName c x):ident $[$dbs]* (q : $Pos $xs) : $res))
          if ctx.idxed then
            let packed ← ctx.occIdxAt c info (idT xs) (← `(q))
            idxAlts := idxAlts.push (← ctx.alt c #[← `(_), ← ctx.bPat c x #[← `(q)]] packed)
  if !ctx.idxed then
    -- A plain type is a family over `Unit`.
    elabCommand (← `(inductive $(ctx.B):ident $[$pExp]* : $(ctx.Shapep) → Type _ where
      $[$bCtors:ctor]*))
    elabCommand (← `(abbrev $(ctx.sig):ident $[$pExp]* : Codata.Signature where
      I := Unit
      Shape := fun _ => $(ctx.Shapep)
      B := fun _ s => $(ctx.Bp) s
      idx := fun _ => ()))
    return
  let ShapeI ← ctx.atI ctx.Shapep
  elabCommand (← `(inductive $(ctx.B):ident $[$pExp]* : ∀ $[$ixBExp]*, $ShapeI → Type _ where
    $[$bCtors:ctor]*))
  if ctx.packed then
    elabCommand (← `(abbrev $(ctx.Ix):ident $[$pExp]* : Type _ := $(← mkIxTerm ctx.idx)))
  let BIs ← appT ctx.Bp (ctx.iArgs ++ #[← `(s)])
  -- The shape is a discriminant too (with the pattern `_`), so that it is refined.
  let discrsB := ctx.discrs (← `(s)) |>.push (← `(b))
  let idxBody ← if idxAlts.isEmpty then `(nomatch b)
    else `(match $[$discrsB:term],* with $idxAlts:matchAlt*)
  elabCommand (← `(def $(ctx.idxId):ident $[$pImp]* $[$ib]* {s : $ShapeI} (b : $BIs) :
      $(ctx.Ixp) := $idxBody))
  if ctx.packed then
    let iPat ← ctx.pack ctx.iArgs
    -- The shapes on the packed index.
    elabCommand (← `(def $(ctx.ShapeP):ident $[$pExp]* (p : $(ctx.Ixp)) : Type _ :=
      match p with | $iPat:term => $ShapeI))
    elabCommand (← `(abbrev $(ctx.sig):ident $[$pExp]* : Codata.Signature where
      I := $(ctx.Ixp)
      Shape := $(ctx.ShapePp)
      B := fun p s => match p, s with | $iPat:term, s => $BIs
      idx := fun {p} {s} b => match p, s, b with | $iPat:term, s, b => $(ctx.idxId) b))
  else
    elabCommand (← `(abbrev $(ctx.sig):ident $[$pExp]* : Codata.Signature where
      I := $(ctx.Ixp)
      Shape := $(ctx.Shapep)
      B := $(ctx.Bp)
      idx := fun b => $(ctx.idxId) b))

/-! ### The isomorphism `F X ≃ σ.Obj X` and its three laws

With indices, the family `X` is on the packed index (that is what the generic theorems expect),
while the index binders stay curried, so that constructor patterns can bind all their arguments.
-/

def genIso (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let ib ← ctx.ixB
  let X ← `(X)
  let famB : Array (TSyntax ``bracketedBinderF) := #[← `(bracketedBinderF| {X Y : $(ctx.Ixp) → Type _})]
  let famBX : Array (TSyntax ``bracketedBinderF) := #[← `(bracketedBinderF| {X : $(ctx.Ixp) → Type _})]
  let curX ← ctx.curryFam X
  let FXi ← ctx.atI (← `($(ctx.Fp) $curX))
  let pI ← ctx.pack ctx.iArgs
  let ObjX ← `($(ctx.sigId `Obj) $(ctx.sigp) X $pI)
  let ObjY ← `($(ctx.sigId `Obj) $(ctx.sigp) Y $pI)
  let toCAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.mapM fun c => do
    let lhs ← ctx.fPat c
    -- The layers `Occ.toC o x` of the nested arguments are bound by a lambda, so that the
    -- inner `match` is parametric in them and `toC_ofC` can rewrite them.
    let zs : Array Ident ← c.nested.mapM fun (x, _) => freshId s!"z_{x.getId.toString}"
    let shape ← ctx.shapeValWith c (← zs.mapM fun z => `($z:ident.1))
    let mut alts : Array (TSyntax ``matchAlt) := #[]
    let mut k := 0
    for g in c.groups do
      match g.kind with
      | .data => pure ()
      | .pos _ =>
        for x in g.ids do
          alts := alts.push (← `(matchAltExpr| | $(ctx.bCtor c x):ident => $x:ident))
      | .fn tele _ =>
        let ys := teleIds tele
        for x in g.ids do
          alts := alts.push (← `(matchAltExpr| | $(ctx.bCtor c x):ident $ys* => $x:ident $ys*))
      | .occ .. =>
        for x in g.ids do
          let z := zs[k]!
          k := k + 1
          alts := alts.push (← `(matchAltExpr| | $(ctx.bCtor c x):ident q => $z:ident.2 q))
    let child ← if alts.isEmpty then `(fun b => nomatch b)
      else `(fun b => match b with $alts:matchAlt*)
    let layer ← `(⟨$shape, $child⟩)
    let rhs ← if zs.isEmpty then pure layer else do
      let toCs ← c.nested.mapM fun (x, info) =>
        `($(occId info.indexed `toC) $(ctx.occOf c info true) $x:ident)
      `((fun $[$zs:ident]* => $layer) $toCs*)
    ctx.alt c #[lhs] rhs
  let discrsA := ctx.discrs (← `(a))
  elabCommand (← `(def $(ctx.toC):ident $[$pImp]* $[$famBX]* $[$ib]* (a : $FXi) : $ObjX :=
    match $[$discrsA:term],* with $toCAlts:matchAlt*))
  let ofCAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.mapM fun c => do
    let shape ← ctx.shapePat c
    let mut args : Array Term := #[]
    for g in c.groups do
      for x in g.ids do
        match g.kind with
        | .data => args := args.push (idT ((ctx.bareIdx c x.getId).getD x))
        | .pos _ => args := args.push (← `(ch $(ctx.bCtor c x)))
        | .fn tele _ =>
          let ys := teleIds tele
          args := args.push (← `(fun $[$ys:ident]* => ch ($(ctx.bCtor c x) $ys*)))
        | .occ info =>
          let xs := nestShapeId x
          args := args.push (← `($(occId info.indexed `ofC) $(ctx.occOf c info true)
            ⟨$xs, fun q => ch ($(ctx.bCtor c x) q)⟩))
    let rhs ← ctx.fApp c (← `(_)) args
    let pat ← if c.hasRec then `(⟨$shape, ch⟩) else `(⟨$shape, _⟩)
    ctx.alt c #[pat] rhs
  let discrsZ := ctx.discrs (← `(z))
  elabCommand (← `(def $(ctx.ofC):ident $[$pImp]* $[$famBX]* $[$ib]* (z : $ObjX) : $FXi :=
    match $[$discrsZ:term],* with $ofCAlts:matchAlt*))
  -- With nested arguments the layers go through the container's isomorphism, and its laws
  -- finish what `rfl` no longer can.
  let nested := ctx.hasOcc
  let seq (tacs : Array (TSyntax `tactic)) : CommandElabM (TSyntax ``Parser.Tactic.tacticSeq) :=
    `(tacticSeq| $[$tacs:tactic]*)
  let ofC_toC_pf ← seq (#[← `(tactic| cases a)] ++ (← if nested then
      pure #[← `(tactic| all_goals first | rfl | simp only [$(ctx.toC):ident, $(ctx.ofC):ident, Codata.Occ.ofC_toC', Codata.IOcc.ofC_toC'])]
    else pure #[← `(tactic| all_goals rfl)]))
  elabCommand (← `(theorem $(ctx.ofC_toC):ident $[$pImp]* $[$famBX]* $[$ib]* (a : $FXi) :
      $(ctx.ofC) ($(ctx.toC) a) = a := by $ofC_toC_pf))
  let toC_ofC_pf ← seq (#[← `(tactic| obtain ⟨s, ch⟩ := z), ← `(tactic| cases s)] ++
    (← if nested then
      -- The container's shape is in a dependent position (the type of the children), which
      -- `simp` cannot rewrite; `rw` can, one nested argument at a time.
      pure #[← `(tactic| all_goals try simp only [$(ctx.toC):ident, $(ctx.ofC):ident]),
        ← `(tactic| all_goals repeat rw [Codata.Occ.toC_ofC]),
        ← `(tactic| all_goals repeat rw [Codata.IOcc.toC_ofC])]
    else pure #[]) ++
    #[← `(tactic| all_goals refine congrArg (Codata.Signature.Obj.mk _) (funext fun b => ?_)),
      ← `(tactic| all_goals cases b), ← `(tactic| all_goals rfl)])
  elabCommand (← `(theorem $(ctx.toC_ofC):ident $[$pImp]* $[$famBX]* $[$ib]* (z : $ObjX) :
      $(ctx.toC) ($(ctx.ofC) z) = z := by $toC_ofC_pf))
  -- `f : ∀ q, X q → Y q` on the packed index, curried for `F.map`.
  let fTyP ← `(∀ q, X q → Y q)
  let fCur ← ctx.curryN (← `(f)) #[⟨(← `(x)).raw⟩]
  let ofC_map_pf ← seq (#[← `(tactic| obtain ⟨s, ch⟩ := z), ← `(tactic| cases s)] ++
    (← if nested then
      pure #[← `(tactic| all_goals first | rfl | simp only [$(ctx.ofC):ident, $(ctx.Fmap):ident, Codata.Signature.Obj.map, Codata.Occ.map_ofC, Codata.IOcc.map_ofC])]
    else pure #[]) ++
    #[← `(tactic| all_goals rfl)])
  elabCommand (← `(theorem $(ctx.ofC_map):ident $[$pImp]* $[$famB]* (f : $fTyP) $[$ib]*
      (z : $ObjX) : $(ctx.ofC) ($(ctx.sigId `Obj.map) f z) = $(ctx.Fmap) $fCur ($(ctx.ofC) z) := by
    $ofC_map_pf))
  if ctx.co then
    let relTyP ← `(∀ q, X q → Y q → Prop)
    let RCur ← ctx.curryN (← `(R)) #[]
    -- After `cases h`, one goal per constructor remains, in order. With nested arguments the
    -- hypothesis on a nested pair is turned into the equality of the shapes, substituted, and
    -- the relation on the contents.
    let common : Array (TSyntax `tactic) := #[← `(tactic| obtain ⟨s, ch⟩ := z),
      ← `(tactic| obtain ⟨s', ch'⟩ := z'), ← `(tactic| cases s), ← `(tactic| all_goals cases s'),
      ← `(tactic| all_goals try simp only [$(ctx.ofC):ident] at h), ← `(tactic| all_goals cases h)]
    let tail : Array (TSyntax `tactic) := #[← `(tactic| refine ⟨_, _, _, rfl, rfl, fun b => ?_⟩),
      ← `(tactic| cases b), ← `(tactic| all_goals solve_by_elim)]
    let rel_ofC_pf ← if nested then do
        let bullets ← ctx.ctors.mapM fun c => do
          let recs := c.groups.foldl (init := #[]) fun acc g =>
            if g.kind.isData then acc else acc ++ g.ids.map fun x => (x, g.kind)
          let mut steps : Array (TSyntax `tactic) := #[]
          if !recs.isEmpty then
            let hs ← recs.mapM fun (x, _) => freshId s!"h_{x.getId.toString}"
            steps := steps.push (← `(tactic| rename_i $[$hs:ident]*))
            for (h, (_, kind)) in hs.zip recs do
              if kind.isOcc then
                -- `rfl` must be the keyword pattern, not a hygienic name.
                let rflPat := mkIdent `rfl
                let relOfC := occId kind.isFam `rel_ofC
                steps := steps.push
                  (← `(tactic| obtain ⟨$rflPat:ident, $h:ident⟩ := $relOfC _ _ $h))
          let all := steps ++ tail
          `(tactic| · $[$all:tactic]*)
        seq (common ++ bullets)
      else
        seq (common ++ #[← `(tactic| all_goals refine ⟨_, _, _, rfl, rfl, fun b => ?_⟩),
          ← `(tactic| all_goals cases b), ← `(tactic| all_goals solve_by_elim)])
    elabCommand (← `(theorem $(ctx.rel_ofC):ident $[$pImp]* $[$famB]* (R : $relTyP) $[$ib]*
        (z : $ObjX) (z' : $ObjY) (h : $(ctx.Rel) $RCur ($(ctx.ofC) z) ($(ctx.ofC) z')) :
        $(ctx.sigId `Obj.Rel) R z z' := by $rel_ofC_pf))

/-! ### The contract -/

/-- The conversion lambdas that instantiate the generic theorems at a curried family. -/
structure Conv where
  /-- `fun p => S p.1 p.2` -/
  Sp : Term
  /-- `fun p => F S p.1 p.2` -/
  FSp : Term
  /-- `fun p => F T p.1 p.2` -/
  FTp : Term
  /-- `fun p => T p.1 p.2` -/
  Tpk : Term
  /-- `fun {p} a => @toC params Sp p.1 p.2 a` -/
  toC : Term
  /-- `fun {p} z => @ofC params Sp p.1 p.2 z` -/
  ofCS : Term
  /-- `fun {p} z => @ofC params T p.1 p.2 z` -/
  ofC : Term
  /-- `fun {p} a => @ofC_toC params Sp p.1 p.2 a` -/
  ofC_toC : Term
  /-- `fun f {p} z => @ofC_map params Sp T f p.1 p.2 z` -/
  ofC_map : Term
  /-- `fun R {p} z z' h => @rel_ofC params T T R p.1 p.2 z z' h` -/
  rel_ofC : Term
  /-- `fun {p} a => @toC params T p.1 p.2 a` -/
  toCT : Term
  /-- `fun {p} a => @ofC_toC params T p.1 p.2 a` -/
  ofC_toCT : Term
  /-- `fun {p} z => @toC_ofC params T p.1 p.2 z` -/
  toC_ofC : Term
  /-- `fun f {p} z => @ofC_map params T Sp f p.1 p.2 z` -/
  ofC_mapTS : Term
  /-- `fun f {_} a => F.map (curry f) a` -/
  map : Term
  /-- `fun R {_} a b => F.Rel (curry R) a b` -/
  Rel : Term
  /-- `fun p s => c p.1 p.2 s` -/
  c : Term
  /-- `(⟨i₁, i₂⟩ : Ixp)` -/
  pI : Term

def mkConv (ctx : Ctx) : CommandElabM Conv := do
  let S := ctx.Sid
  let pArgs ← ctx.projs (← `(p))
  let Sp ← ctx.packFam (idT S)
  let FSp ← if ctx.packed then `(fun (p : $(ctx.Ixp)) => $(← appT (← `($(ctx.Fp) $S)) pArgs))
    else `($(ctx.Fp) $S)
  let FTp ← if ctx.packed then `(fun (p : $(ctx.Ixp)) => $(← appT (← `($(ctx.Fp) $(ctx.Tp))) pArgs))
    else `($(ctx.Fp) $(ctx.Tp))
  let Tpk ← ctx.packFam ctx.Tp
  let Cot ← ctx.famT
  let pTerms := ctx.pTerms
  let x : Ident := ⟨(← `(x)).raw⟩
  return {
    Sp, FSp, FTp, Tpk
    toC := ← `(fun {p} a => @$(ctx.toC) $pTerms* $Sp $pArgs* a)
    ofCS := ← `(fun {p} z => @$(ctx.ofC) $pTerms* $Sp $pArgs* z)
    ofC := ← `(fun {p} z => @$(ctx.ofC) $pTerms* $Cot $pArgs* z)
    ofC_toC := ← `(fun {p} a => @$(ctx.ofC_toC) $pTerms* $Sp $pArgs* a)
    ofC_map := ← `(fun f {p} z => @$(ctx.ofC_map) $pTerms* $Sp $Cot f $pArgs* z)
    rel_ofC := ← `(fun R {p} z z' h => @$(ctx.rel_ofC) $pTerms* $Cot $Cot R $pArgs* z z' h)
    toCT := ← `(fun {p} a => @$(ctx.toC) $pTerms* $Cot $pArgs* a)
    ofC_toCT := ← `(fun {p} a => @$(ctx.ofC_toC) $pTerms* $Cot $pArgs* a)
    toC_ofC := ← `(fun {p} z => @$(ctx.toC_ofC) $pTerms* $Cot $pArgs* z)
    ofC_mapTS := ← `(fun f {p} z => @$(ctx.ofC_map) $pTerms* $Cot $Sp f $pArgs* z)
    map := ← `(fun f {_} a => $(ctx.Fmap) $(← ctx.curryN (← `(f)) #[x]) a)
    Rel := ← `(fun R {_} a b => $(ctx.Rel) $(← ctx.curryN (← `(R)) #[]) a b)
    c := ← ctx.uncurryN (← `(c)) #[⟨(← `(s)).raw⟩]
    pI := ← ctx.packI }

def genContract (ctx : Ctx) : CommandElabM Unit := do
  let pExp := ctx.pExp
  let pImp := ctx.pImp
  let xTy ← ctx.famTy
  let ib ← ctx.ixB
  let ixBExp ← ctx.ixBExp
  let iIds := ctx.iIds
  let iArgs := ctx.iArgs
  let S := ctx.Sid
  let Ti ← ctx.atI ctx.Tp
  let FTi ← ctx.atI (← `($(ctx.Fp) $(ctx.Tp)))
  let Si ← ctx.atI (idT S)
  let cTy ← ctx.famFn (idT S) (← `($(ctx.Fp) $S))
  if ctx.k == 0 then
    elabCommand (← `(def $(ctx.T):ident $[$pExp]* : Type _ := $(ctx.sigId `Cotype) $(ctx.sigp) ()))
  else if ctx.packed then
    elabCommand (← `(def $(ctx.T):ident $[$pExp]* : ∀ $[$ixBExp]*, Type _ :=
      fun $[$iIds:ident]* => $(ctx.sigId `Cotype) $(ctx.sigp) $(← ctx.pack iArgs)))
  else
    elabCommand (← `(def $(ctx.T):ident $[$pExp]* : ∀ $[$ixBExp]*, Type _ :=
      $(ctx.sigId `Cotype) $(ctx.sigp)))
  let cv ← mkConv ctx
  let pTerms := ctx.pTerms
  let Cot ← `($(ctx.sigId `Cotype) $(ctx.sigp))
  elabCommand (← `(def $(ctx.dtor):ident $[$pImp]* $[$ib]* (t : $Ti) : $FTi :=
    @$(ctx.ofC) $pTerms* $Cot $iArgs* ($(ctx.sigId `dtorC) t)))
  let pArgs ← ctx.projs (← `(p))
  let coalg ← `(fun (p : $(ctx.Ixp)) s =>
    @$(ctx.toC) $pTerms* $(cv.Sp) $pArgs* $(← appT (← `(c)) (pArgs ++ #[← `(s)])))
  elabCommand (← `(def $(ctx.corec):ident $[$pImp]* {$S : $xTy} (c : $cTy) $[$ib]* (s : $Si) :
      $Ti := $(ctx.sigId `corecC) (σ := $(ctx.sigp)) (S := $(cv.Sp)) (i := $(cv.pI)) $coalg s))
  let corecFn ← if ctx.k == 0 then `($(ctx.corec) c)
    else `(fun $[$(← ctx.holes)]* s => $(ctx.corec) c s)
  let cs ← appT (← `(c)) (iArgs ++ #[← `(s)])
  elabCommand (← `(theorem $(ctx.dtor_corec):ident $[$pImp]* {$S : $xTy} (c : $cTy) $[$ib]*
      (s : $Si) : $(ctx.dtor) ($(ctx.corec) c s) = $(ctx.Fmap) $corecFn $cs :=
    $(ctx.sigId `dtor_corec_of) (σ := $(ctx.sigp)) (S := $(cv.Sp)) (FS := $(cv.FSp))
      (FT := $(cv.FTp)) (i := $(cv.pI)) $(cv.toC) $(cv.ofCS) $(cv.ofC) $(cv.map) $(cv.ofC_toC)
      $(cv.ofC_map) $(cv.c) s))
  let RTy ← ctx.famRel ctx.Tp ctx.Tp
  let Rixy ← appT (← `(R)) (iArgs ++ #[← `(x), ← `(y)])
  let HTy ← `(∀ $[$ixBExp]* x y, $Rixy → $(ctx.Rel) R ($(ctx.dtor) x) ($(ctx.dtor) y))
  let Rp ← ctx.packFam (← `(R))
  let Hp ← ctx.uncurryN (← `(H)) #[⟨(← `(x)).raw⟩, ⟨(← `(y)).raw⟩, ⟨(← `(h)).raw⟩]
  elabCommand (← `(theorem $(ctx.bisim):ident $[$pImp]* (R : $RTy) (H : $HTy) $[$ib]*
      {x y : $Ti} (h : $Rixy) : x = y :=
    $(ctx.sigId `bisim_of) (σ := $(ctx.sigp)) (FT := $(cv.FTp)) (i := $(cv.pI)) $(cv.ofC)
      $(cv.Rel) $(cv.rel_ofC) $Rp $Hp h))

/-- `T.contract : Codata.Contract T F`, the model packaged as the contract. -/
def genContractDef (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let cv ← mkConv ctx
  let jIds := ctx.jIds
  let x : Ident := ⟨(← `(x)).raw⟩
  let sId : Ident := ⟨(← `(s)).raw⟩
  -- The contract, at the packed index; each field converts a curried piece.
  let Fpk ← if ctx.packed then
      `(fun (X : $(ctx.Ixp) → Type _) (p : $(ctx.Ixp)) =>
        $(← appT (← `($(ctx.Fp) $(← ctx.curryFam (← `(X))))) (← ctx.projs (← `(p)))))
    else pure ctx.Fp
  let cur (f : Term) (extra : Array Ident) := ctx.curryN f extra
  let Hcur ← `(fun $[$jIds:ident]* x y h =>
    $(← appT (← `(H)) (#[← ctx.pack ctx.jArgs] ++ #[← `(x), ← `(y), ← `(h)])))
  -- The contract's `bisim` is for the canonical lifting; the generated one is for the
  -- inductive `F.Rel`, which contains it by `F.rel_map`.
  let mapP ← `(fun {_ _} f {_} a => $(ctx.Fmap) $(← cur (← `(f)) #[x]) a)
  let RelP ← `(fun {_ _} R {_} a b => $(ctx.Rel) $(← cur (← `(R)) #[]) a b)
  let relMapP ← `(fun {_ _ _} R f g {_} a h => $(ctx.Frel_map) $(← cur (← `(R)) #[])
    $(← cur (← `(f)) #[]) $(← cur (← `(g)) #[]) a $(← cur (← `(h)) #[x]))
  let bisimP ← `(fun R H {_ _ _} h => $(ctx.bisim) $(← cur (← `(R)) #[]) $Hcur h)
  elabCommand (← `(def $(ctx.contract):ident $[$pImp]* :
      $(ctx.topId `Contract) (I := $(ctx.Ixp)) $(cv.Tpk) $Fpk where
    map := $mapP
    map_id := fun {_ _} a => $(ctx.Fmap_id) a
    map_comp := fun {_ _ _} g f {_} a => $(ctx.Fmap_comp) $(← cur (← `(g)) #[]) $(← cur (← `(f)) #[]) a
    dtor := fun {_} t => $(ctx.dtor) t
    corec := fun {_} c {_} s => $(ctx.corec) $(← cur (← `(c)) #[sId]) s
    dtor_corec := fun {_} c {_} s => $(ctx.dtor_corec) $(← cur (← `(c)) #[sId]) s
    bisim := $(ctx.topId `bisim_canonical_of) (I := $(ctx.Ixp)) (T := $(cv.Tpk)) (F := $Fpk)
      $mapP $RelP $relMapP (fun {_} t => $(ctx.dtor) t) $bisimP))

/-! ### The contract: the type, its constructor and its fold -/

def genDataContract (ctx : Ctx) : CommandElabM Unit := do
  let pExp := ctx.pExp
  let pImp := ctx.pImp
  let pTerms := ctx.pTerms
  let xTy ← ctx.famTy
  let ib ← ctx.ixB
  let ixBExp ← ctx.ixBExp
  let iIds := ctx.iIds
  let iArgs := ctx.iArgs
  let S := ctx.Sid
  let Ti ← ctx.atI ctx.Tp
  let FTi ← ctx.atI (← `($(ctx.Fp) $(ctx.Tp)))
  let Si ← ctx.atI (idT S)
  let aTy ← ctx.famFn (← `($(ctx.Fp) $S)) (idT S)
  let Int ← ctx.famT
  if ctx.k == 0 then
    elabCommand (← `(def $(ctx.T):ident $[$pExp]* : Type _ := $Int ()))
  else if ctx.packed then
    elabCommand (← `(def $(ctx.T):ident $[$pExp]* : ∀ $[$ixBExp]*, Type _ :=
      fun $[$iIds:ident]* => $Int $(← ctx.pack iArgs)))
  else
    elabCommand (← `(def $(ctx.T):ident $[$pExp]* : ∀ $[$ixBExp]*, Type _ := $Int))
  let cv ← mkConv ctx
  elabCommand (← `(def $(ctx.ctor):ident $[$pImp]* $[$ib]* (y : $FTi) : $Ti :=
    $(ctx.sigId `ctorI) (@$(ctx.toC) $pTerms* $Int $iArgs* y)))
  let pArgs ← ctx.projs (← `(p))
  let alg ← `(fun (p : $(ctx.Ixp)) z =>
    $(← appT (← `(a)) (pArgs ++ #[← `(@$(ctx.ofC) $pTerms* $(cv.Sp) $pArgs* z)])))
  elabCommand (← `(def $(ctx.fold):ident $[$pImp]* {$S : $xTy} (a : $aTy) $[$ib]* (t : $Ti) :
      $Si := $(ctx.sigId `foldI) (σ := $(ctx.sigp)) (S := $(cv.Sp)) (i := $(cv.pI)) $alg t))
  let foldFn ← if ctx.k == 0 then `($(ctx.fold) a)
    else `(fun $[$(← ctx.holes)]* t => $(ctx.fold) a t)
  let ay ← appT (← `(a)) (iArgs ++ #[← `($(ctx.Fmap) $foldFn y)])
  let z : Ident := ⟨(← `(z)).raw⟩
  elabCommand (← `(theorem $(ctx.fold_ctor):ident $[$pImp]* {$S : $xTy} (a : $aTy) $[$ib]*
      (y : $FTi) : $(ctx.fold) a ($(ctx.ctor) y) = $ay :=
    $(ctx.sigId `fold_ctor_of) (σ := $(ctx.sigp)) (S := $(cv.Sp)) (FS := $(cv.FSp))
      (FT := $(cv.FTp)) (i := $(cv.pI)) $(cv.toCT) $(cv.ofC) $(cv.ofCS) $(cv.map) $(cv.ofC_toCT)
      $(cv.ofC_mapTS) $(← ctx.uncurryN (← `(a)) #[z]) y))

/-- `T.contract : Data.Contract T F`, the model packaged as the contract. -/
def genDataContractDef (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let pTerms := ctx.pTerms
  let cv ← mkConv ctx
  let pArgs ← ctx.projs (← `(p))
  let x : Ident := ⟨(← `(x)).raw⟩
  let z : Ident := ⟨(← `(z)).raw⟩
  -- The contract, at the packed index; each field converts a curried piece.
  let Fpk ← if ctx.packed then
      `(fun (X : $(ctx.Ixp) → Type _) (p : $(ctx.Ixp)) =>
        $(← appT (← `($(ctx.Fp) $(← ctx.curryFam (← `(X))))) pArgs))
    else pure ctx.Fp
  let cur (f : Term) (extra : Array Ident) := ctx.curryN f extra
  let mapP ← `(fun {_ _} f {_} a => $(ctx.Fmap) $(← cur (← `(f)) #[x]) a)
  let ofCP ← `(fun {X} {p} z => @$(ctx.ofC) $pTerms* X $pArgs* z)
  let ofCmapP ← `(fun {X Y} f {p} z => @$(ctx.ofC_map) $pTerms* X Y f $pArgs* z)
  elabCommand (← `(def $(ctx.contract):ident $[$pImp]* :
      Data.Contract (I := $(ctx.Ixp)) $(cv.Tpk) $Fpk where
    map := $mapP
    map_id := fun {_ _} a => $(ctx.Fmap_id) a
    map_comp := fun {_ _ _} g f {_} a => $(ctx.Fmap_comp) $(← cur (← `(g)) #[]) $(← cur (← `(f)) #[]) a
    ctor := fun {_} y => $(ctx.ctor) y
    fold := fun {_} a {_} t => $(ctx.fold) $(← cur (← `(a)) #[z]) t
    fold_ctor := fun {_} a {_} y => $(ctx.fold_ctor) $(← cur (← `(a)) #[z]) y
    induction := $(ctx.sigId `induction_of) (σ := $(ctx.sigp)) (F := $Fpk) $mapP $(cv.toCT) $ofCP
      $(cv.toC_ofC) $(cv.ofC_toCT) $ofCmapP))
end Codata
