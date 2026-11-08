import Colean.Gen.Surface
import Colean.Model.Poly

/-!
# Generators on `Expr`, step 5: deriving `PolyIso` for a declared type

*Spec.* Input: a type that is already completely declared, a single type, a family or the types
of a block, with its context: the analysis of its declaration and its public declarations (`T`,
`T.F`, `T.dtor`, `T.corec`, `T.fold`, `T.contract`, …). Output: the instances `PolyIso` and
`PolyMap` for `fun X => T (H₁ X) … (Hₙ X) idx` at every index `idx`, for `H₁`, …, `Hₙ` themselves
instances, so that later declarations can nest through `T`.

This step is separate from the declaration of the type. It runs after it, nothing in the
declaration depends on it, and it cannot affect it: on failure every declaration of this step is
rolled back and a warning is logged, and the type is simply not available for nesting.

The parameters of `T` that may vary, the *holes*, are those of sort `Type u` that no other
parameter's type and no index's type depends on and that are used, outside the occurrences of
`T` and their indices, only in fields whose type has an occurrence structure in them
(`Gen/Occ.lean`, with the parameter as the hole) and that no later argument and no result index
depends on. Such a field is at a *parameter position*; its structure in the premise `Hᵢ` is that
structure with `Occ.ofIso Hᵢ` at the holes (`Holes.atHole?`). With the holes fixed, the layer
`T.F (H X) Y` is presented as `Lay P B X Y` (`T.Poly.S`, `T.Poly.P`, `T.Poly.B`, `T.Poly.toL`,
`T.Poly.ofL` and their laws), and the generic theorems of `Model/Poly.lean` do the rest from the
contract (`T.Poly.fix`, the instances `T.Poly.instPolyIso`, `T.Poly.instPolyMap`, and when the
last parameter is the last hole, `T.Poly.instPolyIsoEta` and `T.Poly.instPolyMapEta` for
`T a₁ … aₙ₋₁` itself).

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
shape, and the laws by cases and rewriting with the laws of `Model/Occ.lean`; the proof arguments
of `coFix` and `inFix` (`icoFix`, `iinFix`) are `rw` scripts on goal metavariables, everything
else instantiates a theorem of `Model/Poly.lean`.

Scope: in a block, the index of a position of a nested argument must be a type of the block at
variables, as through a named type constructor at one type (`L Odd`) or under binders; through a
product or a sum (`Ping × Pong`, `Ping × Nat`) it is the presentation's index only after cases on
the position, and the step fails.
-/

open Lean Meta Elab Term

namespace Codata.Gen

/-- The holes of the structure of a field in the parameter `a : Type lvl`: its occurrences, with
the structure `atHole?` put at them. -/
def paramHoles (a : Expr) (lvl : Level) (atHole? : Option (Expr × Level) := none) : Holes where
  holeOf? e := if e == a then some #[] else none
  isTypeApp e := e.getAppFn == a
  mentions e := e.containsFVar a.fvarId!
  lvl
  fam? := none
  atHole?

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

namespace Ctx

variable (ctx : Ctx)

/-- `T.Poly.s`. -/
def polyName (s : String) : Name := .str (.str ctx.name "Poly") s

/-! ### The holes -/

/-- Remove the candidates that may not vary, until none is removed. -/
partial def refineHoles (cands : Array Expr) : TermElabM (Array Expr) := do
  let mut bad : Array Expr := #[]
  for c in ctx.ctors do
    -- In an index of the result, a parameter is fixed by the constructor.
    bad := bad ++ cands.filter fun h => c.uidx.any (·.containsFVar h.fvarId!)
    for a in c.args, i in [0:c.args.size] do
      if a.kind.isData then
        let ms := cands.filter (a.type.containsFVar ·.fvarId!)
        if ms.size ≥ 2 then
          bad := bad ++ ms
        else if let some h := ms[0]? then
          let ok ← try
              discard <| occOf (paramHoles h (← typeLevel h)) a.type
              pure true
            catch _ => pure false
          let later := (c.args.extract (i + 1) c.args.size).any
              (·.type.containsFVar a.fvar.fvarId!) ||
            c.uidx.any (·.containsFVar a.fvar.fvarId!)
          if !ok || later then bad := bad.push h
      else
        -- Outside the occurrences of the type, and in their indices.
        let ty := ctx.replaceOccU a.type (fun _ idx => mkAppN (Lean.mkConst ``Unit) idx) ctx.lvl
        bad := bad ++ cands.filter (ty.containsFVar ·.fvarId!)
  if bad.isEmpty then return cands
  refineHoles (cands.filter (!bad.contains ·))

/-- The parameters that may vary. -/
def polyHoles : TermElabM (Array Expr) := do
  let mut cands := #[]
  for p in ctx.params do
    let isType := match ← instantiateMVars (← inferType p) with
      | .sort (.succ _) => true
      | _ => false
    let used ← ctx.params.anyM fun q => do
      return q != p && (← instantiateMVars (← inferType q)).containsFVar p.fvarId!
    -- An index's type may not mention it: the index is fixed per instance.
    let inIdx ← ctx.types.anyM fun t => t.idx.anyM fun i => do
      return (← instantiateMVars (← inferType i)).containsFVar p.fvarId!
    if isType && !used && !inIdx then cands := cands.push p
  ctx.refineHoles cands

/-! ### The context of the instances -/

/-- A field at a parameter position: its position among the constructor's arguments, and its
structure in the premise, with its shapes and positions. -/
structure HoleField where
  k : Nat
  occ : Expr
  sh : Expr
  pos : Expr
  deriving Inhabited

/-- The local variables of the generated declarations: the holes and the other parameters (of
the analysis), the premises `Hᵢ : Type x → Aᵢ` (and `H'ᵢ`, at other universes, for `PolyMap`),
their presentations `Sᵢ`, `Rᵢ` and instances, the fields at parameter positions of each
constructor, and the universes. -/
structure Poly where
  holes : Array Expr
  consts : Array Expr
  Hs : Array Expr
  Hs' : Array Expr
  Ss : Array Expr
  Rs : Array Expr
  insts : Array Expr
  insts' : Array Expr
  fields : Array (Array HoleField)
  /-- The universes of this step: `x`, `x'`, `y`, `y'`, the primed universe of the last
  parameter (`instPolyMapEta`), then `sᵢ`, `pᵢ` per hole, then the primed universes. -/
  fresh : List Name
  /-- The user's universes of the holes and their primed versions, for `H'`. -/
  primes : List (Name × Level)
  /-- With indices, the index of the presentation: the packed index `J` over the constants, or in
  a block `Blk.Poly.Ix consts`, the block's index without the holes. -/
  I : Expr := Lean.mkConst ``Unit
  /-- An index of the analysis as an index of the presentation: in a block, `Blk.Ix.Tₘ params`
  becomes `Blk.Poly.Ix.Tₘ consts`. -/
  toPolyIdx : Expr → Expr := id
  deriving Inhabited

namespace Poly

variable (P : Poly)

def lvl (i : Nat) : Level := .param P.fresh[i]!
def lx : Level := P.lvl 0
def lx' : Level := P.lvl 1
def ly : Level := P.lvl 2
def ly' : Level := P.lvl 3

/-- `S₁ R₁ S₂ R₂ …`. -/
def SR : Array Expr := (P.Ss.zip P.Rs).flatMap fun (s, r) => #[s, r]

/-- The parameters of `T.Poly.S`, `P`, `B`. -/
def psB : Array Expr := P.consts ++ P.SR

/-- The premises of `toL`, `ofL`, `fix`, …: `{consts} (H…) {S R…} [insts]`. -/
def premises : Array Expr := P.consts ++ P.Hs ++ P.SR ++ P.insts

/-- `e` at the primed universes of the holes. -/
def prime (e : Expr) : Expr :=
  e.instantiateLevelParams (P.primes.map (·.1)) (P.primes.map (·.2))

/-- `e` with the holes at the premises `Hs` applied to `X`. -/
def subX (Hs : Array Expr) (X e : Expr) : Expr := e.replaceFVars P.holes (Hs.map (mkApp · X))

end Poly

/-- The parameters at the premises applied to `X`: `consts`, `Hᵢ X` for the holes. -/
def polyParams (P : Poly) (Hs : Array Expr) (X : Expr) : Array Expr :=
  ctx.params.map fun p => match P.holes.findIdx? (· == p) with
    | some i => mkApp Hs[i]! X
    | none => p

/-- The constant `n` at its universes `σ` (by name; the others as they are). -/
def polyConst (n : Name) (σ : List (Name × Level) := []) : MetaM Expr := do
  let ci ← getConstInfo n
  return .const n (ci.levelParams.map fun p => (σ.lookup p).getD (.param p))

/-! ### Indices

With indices, the presentation is a family over the index `P.I`: the packed index `J` of a family,
or for a block `Blk.Poly.Ix consts`, the block's index `Blk.Ix params` without the parameters that
vary, which it takes although its constructors do not use them. The family of the type at the
premises lives over its own index `I'` (`J`, or `Blk.Ix (H X)`), read along `ι : P.I → I'`, the
identity or `Blk.Poly.ixIn`. -/

/-- The index of the presentation of the family-level index arguments `idx`. -/
def polyIdx (P : Poly) (idx : Array Expr) : MetaM Expr := return P.toPolyIdx (← ctx.pack idx)

/-- `ι j`, the index `j` of the presentation as an index of the family at the premises `Hs` and
`X`: `j`, or in a block `Blk.Poly.ixIn params j`. -/
def polyIota (P : Poly) (Hs : Array Expr) (X j : Expr) : MetaM Expr := do
  if !ctx.isBlock then return j
  return mkApp (mkAppN (← polyConst (ctx.polyName "ixIn")) (ctx.polyParams P Hs X)) j

/-- The universe `v` of a family `Y : … → Type v`. -/
def famLevel (Y : Expr) : MetaM Level := do
  forallTelescopeReducing (← inferType Y) fun _ body => do
    let .sort l ← whnf body | throwError "internal error: not a family{indentExpr Y}"
    let some v := l.dec | throwError "internal error: not a family of types{indentExpr Y}"
    return v

/-- In a block, `Blk.Poly.Ix consts`, the block's index without the holes, with a constructor per
type whose arguments are that type's indices, and `Blk.Poly.ixIn params` into `Blk.Ix params`;
returns `P` with the index of the presentation and the translation of the block's index. -/
def genPolyIx (P : Poly) : TermElabM Poly := do
  let name := ctx.polyName "Ix"
  let lvls ← ctx.types.foldlM (init := #[]) fun acc t => do
    return acc ++ (← t.idx.mapM fun i => do getLevel (← inferType i))
  let r := resultLevel lvls
  let pre := P.consts.filter (!ctx.declParams.contains ·)
  let ty ← withBinderInfo (P.consts.filter (!pre.contains ·)) .default do
    mkForallFVars P.consts (mkSort r.succ)
  let ctorName (m : Nat) : Name :=
    name ++ Name.mkSimple ctx.types[m]!.name.lastComponentAsString
  let us ← withLocalDeclD `Ix ty fun Iv => do
    let ctorTys ← ctx.types.mapM fun t =>
      withBinderInfo P.consts .implicit do mkForallFVars (P.consts ++ t.idx) (mkAppN Iv P.consts)
    let us ← ctx.levelParamsOf [] (ctorTys.push ty)
    let Ic := Lean.mkConst name (us.map mkLevelParam)
    addInductive us P.consts.size [{
      name, type := ty
      ctors := (Array.range ctx.types.size).toList.map fun m =>
        { name := ctorName m, type := ctorTys[m]!.replaceFVar Iv Ic } }] ctx.ref
    pure us
  let I := mkAppN (Lean.mkConst name (us.map mkLevelParam)) P.consts
  let ctors := (Array.range ctx.types.size).map fun m =>
    mkAppN (Lean.mkConst (ctorName m) (us.map mkLevelParam)) P.consts
  -- `ixIn`, by cases.
  withLocalDeclD `i I fun i => do
    let value ← mkCasesOnApp name (us.map mkLevelParam) P.consts i (← getLevel ctx.J)
      (fun _ _ => pure ctx.J) fun cname xs => do
        let some m := (Array.range ctx.types.size).find? (ctorName · == cname)
          | throwError "internal error: unexpected constructor {cname}"
        return mkAppN ctx.ixCtors[m]! xs
    let xs := ctx.params.push i
    let (type, value) ← withBinderInfo ctx.params .implicit do
      return (← mkForallFVars xs ctx.J, ← mkLambdaFVars xs value)
    addDef (ctx.polyName "ixIn") (← ctx.levelParamsOf [] #[type, value]) type value ctx.ref
  let toPolyIdx (e : Expr) : Expr := e.replace fun t =>
    match ctx.ixCtors.findIdx? (· == t) with
    | some m => some ctors[m]!
    | none => if t == ctx.J then some I else none
  return { P with I, toPolyIdx }

/-! ### The presentation: `S`, `P`, `B` -/

/-- The data arguments of the `m`-th constructor that are not at parameter positions. -/
def polyPlain (P : Poly) (m : Nat) : Array ArgInfo :=
  (ctx.ctors[m]!.args.zipIdx.filter fun (a, k) =>
    a.kind.isData && !P.fields[m]!.any (·.k == k)).map (·.1)

/-- Run `k` on the shape binders of the `m`-th constructor: those of its nested arguments, then
of its fields at parameter positions. -/
def withPolyShapes (P : Poly) (m : Nat) (bi : BinderInfo) (k : Array Expr → TermElabM α) :
    TermElabM α :=
  let c := ctx.ctors[m]!
  ctx.withShapeBinders c bi fun nshs =>
    withLocalsN P.fields[m]!.size (fun j => do
      let f := P.fields[m]![j]!
      return (c.args[f.k]!.name.appendAfter "_s", bi, f.sh)) fun fshs => k (nshs ++ fshs)

/-- `T.Poly.S.c psB plain shapes`. -/
def polySCtor (P : Poly) (m : Nat) (args : Array Expr) : MetaM Expr := do
  return mkAppN (← polyConst (ctx.polyName "S" ++ ctx.ctors[m]!.fname)) (P.psB ++ args)

/-- `T.Poly.S psB`, `T.Poly.P psB s`, `T.Poly.B psB s`. -/
def polyS (P : Poly) : MetaM Expr := return mkAppN (← polyConst (ctx.polyName "S")) P.psB
def polyP (P : Poly) : MetaM Expr := return mkAppN (← polyConst (ctx.polyName "P")) P.psB
def polyB (P : Poly) : MetaM Expr := return mkAppN (← polyConst (ctx.polyName "B")) P.psB

/-- The name of the constructor of `P` (`B`) for the argument `a` of `c`. -/
def polyPos (s : String) (c : Ctor) (a : ArgInfo) : Name :=
  ctx.polyName s ++ Name.mkSimple (c.fname.toString ++ "_" ++ a.name.toString)

/-- Declare the inductive `name` with the parameters `psB` (explicit, but for the section
variables) and the constructors `mkCtors I` over a local variable `I` for it: a type `S`
(`idx := false`) or a family over `S`; with indices, `S` is a family over the index `P.I`, and so
are the families over it. Its universe is inferred from the constructors. -/
def polyInductive (P : Poly) (name : Name) (idx : Bool)
    (mkCtors : Expr → TermElabM (Array (Name × Expr))) : TermElabM Unit := do
  let psB := P.psB
  let declare (lvl : Level) : TermElabM Expr := do
    let pre := P.consts.filter (!ctx.declParams.contains ·)
    withBinderInfo (psB.filter (!pre.contains ·)) .default do
    let withI (k : Array Expr → TermElabM Expr) : TermElabM Expr :=
      if ctx.idxed then withLocalDeclD `i P.I fun i => k #[i] else k #[]
    withI fun is => do
      if idx then
        withLocalDeclD `s (mkAppN (← ctx.polyS P) is) fun s =>
          mkForallFVars (psB ++ is |>.push s) (mkSort lvl)
      else mkForallFVars (psB ++ is) (mkSort lvl)
  withLocalDeclD `I (← declare Level.one) fun Iv => do
  let cs ← mkCtors Iv
  let lvls ← cs.foldlM (init := #[]) fun acc (_, t) => forallTelescope t fun xs _ => do
    return acc ++ (← (xs.extract psB.size xs.size).mapM fun x => do getLevel (← inferType x))
  let ty ← declare (resultLevel lvls).succ
  let us ← ctx.levelParamsOf P.fresh (cs.map (·.2) |>.push ty)
  let Ic := Lean.mkConst name (us.map mkLevelParam)
  addInductive us psB.size [{
    name, type := ty
    ctors := cs.toList.map fun (n, t) => { name := n, type := t.replaceFVar Iv Ic } }] ctx.ref

/-- `T.Poly.S`, `T.Poly.P` (a position per field at a parameter position, with a position of its
structure), `T.Poly.B` (a position per recursive argument, as in `T.B`). -/
def genPolyShapes (P : Poly) : TermElabM Unit := do
  let ms := Array.range ctx.ctors.size
  -- With indices, the index of the presentation of the result of the `m`-th constructor.
  let cIdx (m : Nat) : MetaM (Array Expr) := do
    if ctx.idxed then return #[← ctx.polyIdx P ctx.ctors[m]!.idx] else return #[]
  -- `S`: the data, the shapes of the nested arguments and of the fields.
  ctx.polyInductive P (ctx.polyName "S") false fun Sv => ms.mapM fun m =>
    ctx.withPolyShapes P m .default fun shs => do
      let plain := (ctx.polyPlain P m).map (·.fvar)
      let t ← withBinderInfo P.psB .implicit do
        mkForallFVars (P.psB ++ plain ++ shs) (mkAppN Sv (P.psB ++ (← cIdx m)))
      return (ctx.polyName "S" ++ ctx.ctors[m]!.fname, t)
  -- A constructor of `P` or `B` for the `m`-th constructor: data and shapes implicit, `extra`.
  let posCtor (Iv : Expr) (m : Nat) (extra : Array Expr → (Array Expr → TermElabM Expr) →
      TermElabM Expr) : TermElabM Expr :=
    ctx.withPolyShapes P m .implicit fun shs => extra shs fun ys => do
      let plain := (ctx.polyPlain P m).map (·.fvar)
      withBinderInfo (P.psB ++ plain) .implicit do
        mkForallFVars (P.psB ++ plain ++ shs ++ ys)
          (mkApp (mkAppN Iv (P.psB ++ (← cIdx m))) (← ctx.polySCtor P m (plain ++ shs)))
  ctx.polyInductive P (ctx.polyName "P") true fun Iv => ms.flatMapM fun m => do
    let c := ctx.ctors[m]!
    let nn := c.nests.size
    (Array.range P.fields[m]!.size).mapM fun j => do
      let f := P.fields[m]![j]!
      let t ← posCtor Iv m fun shs k =>
        withLocalDeclD `q (mkApp f.pos shs[nn + j]!).headBeta fun q => k #[q]
      return (ctx.polyPos "P" c c.args[f.k]!, t)
  ctx.polyInductive P (ctx.polyName "B") true fun Iv => ms.flatMapM fun m => do
    let c := ctx.ctors[m]!
    c.recArgs.mapM fun a => do
      let t ← posCtor Iv m fun shs k => withPosArgs c a (shs.extract 0 c.nests.size) k
      return (ctx.polyPos "B" c a, t)

/-- The index of the child at a position, from the arguments `bargs` of its constructor in
`T.Poly.B` (the plain data, the shapes, the extra arguments), as `posIdx` for `T.B`. A field at a
parameter position occurs in no index (`refineHoles`). -/
def polyPosIdx (P : Poly) (m : Nat) (a : ArgInfo) (bargs : Array Expr) : MetaM Expr := do
  let c := ctx.ctors[m]!
  let plain := ctx.polyPlain P m
  let np := plain.size
  let nsh := c.nests.size + P.fields[m]!.size
  let σ (e : Expr) := e.replaceFVars (plain.map (·.fvar)) (bargs.extract 0 np)
  let extra := bargs.extract (np + nsh) bargs.size
  match a.kind with
  | .plain idx => ctx.polyIdx P (idx.map σ)
  | .fn _ =>
    let mut ty := σ a.type
    for y in extra do
      ty ← whnfR ty
      ty := ty.bindingBody!.instantiate1 y
    let some idx := ctx.holeOf? (← whnfOcc ty)
      | throwError "internal error: no occurrence at the end of{indentExpr ty}"
    ctx.polyIdx P idx
  | .nest n =>
    let some j := c.nests.findIdx? (·.1.fvar == a.fvar) | unreachable!
    let some pidx := n.pidx? | throwError "internal error: a nested argument without indices"
    return P.toPolyIdx (mkApp2 (σ pidx) bargs[np + j]! extra[0]!).headBeta
  | .data => throwError "internal error: a data argument has no position"

/-- With indices, `T.Poly.idx`, the index of the child at a position, by cases. -/
def genPolyIdx (P : Poly) : TermElabM Unit := do
  let B ← ctx.polyB P
  withLocalDecl `i .implicit P.I fun i => do
  withLocalDecl `s .implicit (mkApp (← ctx.polyS P) i) fun s => do
  withLocalDeclD `b (mkApp2 B i s) fun b => do
  let args := P.psB ++ #[i, s]
  let Bn := ctx.polyName "B"
  let value ← mkCasesOnApp Bn B.getAppFn.constLevels! args b (← getLevel P.I)
    (fun _ _ => pure P.I) fun cname xs => do
      let some (m, a) := (Array.range ctx.ctors.size).findSome? fun m =>
          let c := ctx.ctors[m]!
          (c.recArgs.find? (ctx.polyPos "B" c · == cname)).map (m, ·)
        | throwError "internal error: unexpected constructor {cname}"
      let c := ctx.ctors[m]!
      let nargs ← ctx.withPolyShapes P m .implicit fun shs =>
        withPosArgs c a (shs.extract 0 c.nests.size) fun ys =>
          pure ((ctx.polyPlain P m).size + shs.size + ys.size)
      ctx.polyPosIdx P m a (← ctorArgsOf Bn P.psB.size args xs nargs)
  let xs := P.psB ++ #[i, s, b]
  let (type, value) ← withBinderInfo P.psB .implicit do
    return (← mkForallFVars xs P.I, ← mkLambdaFVars xs value)
  addDef (ctx.polyName "idx") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref

/-- `T.Poly.sig psB`, the signature of the presentation: the index `P.I`, `S`, `B` and `idx`. -/
def polySig (P : Poly) : MetaM Expr :=
  return mkAppN (← polyConst (ctx.polyName "sig")) P.psB

/-- With indices, `T.Poly.sig`, reducible as `T.sig`. -/
def genPolySig (P : Poly) : TermElabM Unit := do
  let S ← ctx.polyS P
  let B ← ctx.polyB P
  let rS ← withLocalDeclD `i P.I fun i => do typeLevel (mkApp S i)
  let rB ← withLocalDeclD `i P.I fun i => withLocalDeclD `s (mkApp S i) fun s => do
    typeLevel (mkApp2 B i s)
  let idxFn ← lam `i P.I (bi := .implicit) fun i => lam `s (mkApp S i) (bi := .implicit) fun s =>
    lam `b (mkApp2 B i s) fun b => do
      return mkAppN (← polyConst (ctx.polyName "idx")) (P.psB ++ #[i, s, b])
  let value := mkApp4 (.const ``Codata.Signature.mk [← typeLevel P.I, rS, rB]) P.I S B idxFn
  let type ← inferType value
  let pre := P.consts.filter (!ctx.declParams.contains ·)
  let (type, value) ← withBinderInfo (P.psB.filter (!pre.contains ·)) .default do
    return (← mkForallFVars P.psB type, ← mkLambdaFVars P.psB value)
  addDef (ctx.polyName "sig") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref
    (reducible := true)

/-! ### The layer: `toL`, `ofL` and their laws -/

/-- `T.F (H X) Y`, at the universe `w` of `Y`. -/
def polyF (P : Poly) (X Y : Expr) (w : Level) : MetaM Expr := do
  return mkAppN (← ctx.constWith ctx.F [w]) (ctx.polyParams P P.Hs X |>.push Y)

/-- `Lay (T.Poly.P psB) (T.Poly.B psB) X Y`. -/
def polyLay (P : Poly) (X Y : Expr) : MetaM Expr := do
  mkAppOptM ``Codata.Lay #[none, ← ctx.polyP P, ← ctx.polyB P, X, Y]

/-- With indices, the type of the family `Y` that `T.F (H X)` takes: `∀ j₁ j₂, Type w`, or
`Blk.Ix (H X) → Type w`. -/
def polyYTy (P : Poly) (Hs : Array Expr) (X : Expr) (w : Level) : TermElabM Expr := do
  return P.subX Hs X (← ctx.famType w)

/-- The family of the children of a layer, on the index of the presentation, from the family `Y`
that `T.F` takes: `fun j => Y (ι j)`, curried; `Y` itself for one index. -/
def polyLayFam (P : Poly) (Hs : Array Expr) (X Y : Expr) : TermElabM Expr := do
  if !ctx.isBlock && ctx.k == 1 then return Y
  lam `j P.I fun j => do return mkAppN Y (← ctx.projs (← ctx.polyIota P Hs X j))

/-- `ILay (T.Poly.sig psB) (T.Poly.P psB) X (fun j => Y (ι j)) i`. -/
def polyILay (P : Poly) (X Y i : Expr) : TermElabM Expr := do
  mkAppOptM ``Codata.ILay
    #[← ctx.polySig P, ← ctx.polyP P, X, ← ctx.polyLayFam P P.Hs X Y, i]

/-- `T.F (H X) Y (ι i)` at the index `i` of the presentation, at the universe `w` of `Y`. -/
def polyFI (P : Poly) (X Y i : Expr) (w : Level) : TermElabM Expr := do
  return mkAppN (← ctx.polyF P X Y w) (← ctx.projs (← ctx.polyIota P P.Hs X i))

/-- `T.Poly.idx psB i s b`, the index of the child at `b`. -/
def polyIdxAt (P : Poly) (i s b : Expr) : MetaM Expr := do
  return mkAppN (← polyConst (ctx.polyName "idx")) (P.psB ++ #[i, s, b])

/-- `(b : T.Poly.B psB i s) → Y (ι (T.Poly.idx b))`, the children of a layer at `i` and `s`. -/
def polyKidsTy (P : Poly) (X Y i s : Expr) : TermElabM Expr := do
  let layY ← ctx.polyLayFam P P.Hs X Y
  withLocalDeclD `b (mkApp2 (← ctx.polyB P) i s) fun b => do
    mkForallFVars #[b] (mkApp layY (← ctx.polyIdxAt P i s b)).headBeta

/-- `Occ.ofC o ⟨sh, fun q => snd q⟩` for a plain structure, the structure of a field at a
parameter position, also when the type has indices. -/
def mkOfCPlain (o hole sh : Expr) (snd : Expr → TermElabM Expr) : TermElabM Expr :=
  ({ ctx with idx := #[] } : Ctx).mkOfC o hole sh snd

/-- `T.Poly.toL premises X Y a` (`ofL`, …): a declaration of this step over the premises, at
the universes `y` of `Y` (and `y'`) given by `σ`. -/
def polyAt (P : Poly) (s : String) (σ : List (Name × Level)) (args : Array Expr) : MetaM Expr := do
  return mkAppN (← polyConst (ctx.polyName s) σ) (P.premises ++ args)

/-- The substitution of the arguments of `c` by `ys`, and of the holes by `Hᵢ X`. -/
def polySubst (P : Poly) (c : Ctor) (ys : Array Expr) (X : Expr) (e : Expr) : Expr :=
  (e.replaceFVars c.fvars ys).replaceFVars P.holes (P.Hs.map (mkApp · X))

/-- The layer of `F.c ys` (`toL`): `(fun z… => ⟨S.c data z.1…, positions, children⟩) (toC o x)…`.
-/
def polyLayer (P : Poly) (m : Nat) (X Y : Expr) (ys : Array Expr) : TermElabM Expr := do
  let c := ctx.ctors[m]!
  let fs := P.fields[m]!
  let σ := polySubst P c ys X
  let toC (o hole y : Expr) : MetaM Expr :=
    mkAppOptM ``Codata.Occ.toC #[none, none, none, o, hole, y]
  -- With indices, the structure of a nested argument is indexed, at `Y` on the packed index.
  let nestToC (o y : Expr) : TermElabM Expr := do
    if !ctx.idxed then return ← toC o Y y
    mkAppOptM ``Codata.IOcc.toC
      #[none, none, none, none, none, o, P.subX P.Hs X (← ctx.packFam Y), y]
  let toCs := (← c.nests.mapM fun (a, n) => do
      let some k := c.args.findIdx? (·.fvar == a.fvar) | unreachable!
      nestToC (ctx.nestAt n P.ly σ) ys[k]!) ++
    (← fs.mapM fun f => toC (σ f.occ) X ys[f.k]!)
  let names := c.nests.map (·.1.name) ++ fs.map (c.args[·.k]!.name)
  withLocalsN toCs.size (fun j => return (names[j]!.appendBefore "z_", .default,
      ← inferType toCs[j]!)) fun zs => do
  let plain := (c.args.zip ys).filterMap fun (a, y) =>
    if a.kind.isData && !fs.any (c.args[·.k]!.fvar == a.fvar) then some y else none
  let shape ← ctx.polySCtor P m (plain ++ (← zs.mapM fun z => mkAppM ``Sigma.fst #[z]))
  -- With indices, the index of the layer (translated before the substitution, which changes the
  -- parameters of the block's index).
  let i? ← if ctx.idxed then some <$> σ <$> ctx.polyIdx P c.idx else pure none
  let atIdx (fam : Expr) : Expr := match i? with
    | some i => mkApp fam i
    | none => fam
  -- The positions and the children, by cases (in general position with indices).
  let byCases (ty : Expr) (val : Name → CasesSubgoal → TermElabM Expr) : TermElabM Expr := do
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (b, g') ← g.mvarId!.intro1
    for sg in ← if ctx.idxed then casesPos g' b else g'.cases b do
      let some n := sg.ctorName | throwError "internal error: no constructor"
      let v ← val n sg
      sg.mvarId.withContext do
        unless ← isDefEq (← sg.mvarId.getType) (← inferType v) do
          throwError "internal error: ill-typed position{indentExpr v}"
        sg.mvarId.assign v
    instantiateMVars g
  let pf ← byCases (← mkArrow (mkApp (atIdx (← ctx.polyP P)) shape) X) fun n sg => do
    let some j := fs.findIdx? fun f => n == ctx.polyPos "P" c c.args[f.k]!
      | throwError "internal error: unexpected position {n}"
    return mkApp (← mkAppM ``Sigma.snd #[sg.subst.apply zs[c.nests.size + j]!]) sg.fields.back!
  let bTy ← match i? with
    | some i => ctx.polyKidsTy P X Y i shape
    | none => mkArrow (mkApp (← ctx.polyB P) shape) Y
  let bf ← byCases bTy fun n sg => do
    let some k := c.args.findIdx? fun a => !a.kind.isData && n == ctx.polyPos "B" c a
      | throwError "internal error: unexpected position {n}"
    let a := c.args[k]!
    match a.kind with
    | .nest _ =>
      let some j := c.nests.findIdx? (·.1.fvar == a.fvar) | unreachable!
      let v := mkApp (← mkAppM ``Sigma.snd #[sg.subst.apply zs[j]!]) sg.fields.back!
      -- In a block, the child's index must be the block's index of the presentation's.
      if ctx.isBlock then
        let ok ← sg.mvarId.withContext do isDefEq (← sg.mvarId.getType) (← inferType v)
        unless ok do
          throwError "the positions of the nested argument `{a.name}` of `{c.name}` are at a \
            type of the block only after cases on them, as through a product or a sum, which is \
            not supported for the types of a block"
      return v
    | .fn n => return mkAppN (sg.subst.apply ys[k]!) (sg.fields.extract (sg.fields.size - n))
    | _ => return sg.subst.apply ys[k]!
  let lay ← match i? with
    | some i =>
      let layTy ← whnfR (← ctx.polyILay P X Y i)
      mkAppOptM ``Sigma.mk
        #[layTy.appFn!.appArg!, layTy.appArg!, shape, ← mkAppM ``Prod.mk #[pf, bf]]
    | none =>
      let β ← lam `s (← ctx.polyS P) fun s => do
        mkAppM ``Prod
          #[← mkArrow (mkApp (← ctx.polyP P) s) X, ← mkArrow (mkApp (← ctx.polyB P) s) Y]
      mkAppOptM ``Sigma.mk #[← ctx.polyS P, β, shape, ← mkAppM ``Prod.mk #[pf, bf]]
  return mkAppN (← mkLambdaFVars zs lay) toCs

/-- `F.c (H X) Y args` from the shape arguments `sargs` of `S.c` and the contents `v`, `k` of a
layer (`ofL`): a field at a parameter position is `Occ.ofC o ⟨x_s, fun q => v (P.c_x q)⟩`, a
recursive argument `k (B.c_y)`, under its telescope or through its structure. -/
def polyOfLBody (P : Poly) (m : Nat) (X Y v k : Expr) (sargs : Array Expr) :
    TermElabM Expr := do
  let c := ctx.ctors[m]!
  let fs := P.fields[m]!
  let plainArgs := ctx.polyPlain P m
  let np := plainArgs.size
  let shs := sargs.extract np sargs.size
  let σd (e : Expr) : Expr :=
    (e.replaceFVars (plainArgs.map (·.fvar)) (sargs.extract 0 np)).replaceFVars P.holes
      (P.Hs.map (mkApp · X))
  let posApp (s : String) (a : ArgInfo) (extra : Array Expr) : MetaM Expr := do
    return mkAppN (← polyConst (ctx.polyPos s c a)) (P.psB ++ sargs ++ extra)
  -- The occurrences of the nested structures: `Y`, or with indices `Y` on the packed index.
  let hole ← if ctx.idxed then pure (P.subX P.Hs X (← ctx.packFam Y)) else pure Y
  let mut fn := mkAppN (← ctx.constWith (ctx.fCtor c) [P.ly]) (ctx.polyParams P P.Hs X |>.push Y)
  let mut ty ← inferType fn
  let mut di := 0
  for a in c.args, i in [0:c.args.size] do
    ty ← whnf ty
    let val ← match a.kind with
      | .data =>
        if let some j := fs.findIdx? (·.k == i) then
          ctx.mkOfCPlain (σd fs[j]!.occ) X shs[c.nests.size + j]! fun q => do
            return mkApp v (← posApp "P" a #[q])
        else pure sargs[di]!
      | .plain _ => pure (mkApp k (← posApp "B" a #[]))
      | .fn n => withTele n ty.bindingDomain! fun zs _ => do
        mkLambdaFVars zs (mkApp k (← posApp "B" a zs))
      | .nest n =>
        let some j := c.nests.findIdx? (·.1.fvar == a.fvar) | unreachable!
        ctx.mkOfC (substLevel ctx.uT P.ly (σd n.occ)) hole shs[j]! fun q => do
          return mkApp k (← posApp "B" a #[q])
    if a.kind.isData && !fs.any (·.k == i) then di := di + 1
    fn := mkApp fn val
    ty := ty.bindingBody!.instantiate1 val
  return fn

/-- The type `T.F (H X) Y idx…` of `a` once the index of the presentation is split into its
components: the indices reduced, `⟨i₁, i₂⟩.1` to `i₁`, in a block `ι (Blk.Poly.Ix.Tₘ idx)` to
`Blk.Ix.Tₘ idx`, so that cases on `a` see them. -/
def polyWhnfIdx (ty : Expr) : MetaM Expr := do
  let np := ctx.params.size + 1
  let args ← ty.getAppArgs.mapIdxM fun k e => if k < np then pure e else whnf e
  return mkAppN ty.getAppFn args

/-- `toL` in a block, on the goal `g : ILay … i` with `a : Blk.F (H X) Y (ι i)`: by cases on the
index `i`, then on `a`, whose index `ι i` is then `Blk.Ix.Tₘ idx`, which drops the constructors of
the other types and solves the equations of the indices (the `idx` are variables). -/
def polyToLBlock (P : Poly) (X Y : Expr) (g : MVarId) (i : FVarId) : TermElabM Unit := do
  for sg in ← g.cases i do
    sg.mvarId.withContext do
    let some a := (← getLCtx).lastDecl | throwError "internal error: no layer to destructure"
    let g ← sg.mvarId.replaceLocalDeclDefEq a.fvarId (← ctx.polyWhnfIdx (← instantiateMVars a.type))
    for sg in ← g.cases a.fvarId do
      sg.mvarId.withContext do
      let some m := ctx.ctors.findIdx? fun c => sg.ctorName == some (ctx.fCtor c)
        | throwError "internal error: unexpected case {sg.ctorName}"
      let v ← ctx.polyLayer P m X Y sg.fields
      unless ← isDefEq (← sg.mvarId.getType) (← inferType v) do
        throwError "internal error: ill-typed layer{indentExpr v}"
      sg.mvarId.assign v

/-- With indices, `T.Poly.toL` and `T.Poly.ofL` at an index `i` of the presentation, between
`T.F (H X) Y (ι i)` and the layer at `i`. `toL` is by cases on `F` (in a block `polyToLBlock`),
`ofL` by cases on the shape. -/
def genIPolyLayer (P : Poly) : TermElabM Unit := do
  let close (xs : Array Expr) (type value : Expr) : TermElabM (Expr × Expr) :=
    withBinderInfo (P.consts ++ P.SR) .implicit do
      return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  withLocalDecl `X .implicit (mkSort P.lx.succ) fun X => do
  withLocalDecl `Y .implicit (← ctx.polyYTy P P.Hs X P.ly) fun Y => do
  withLocalDecl `i .implicit P.I fun i => do
  let FXY ← ctx.polyFI P X Y i P.ly
  let lay ← ctx.polyILay P X Y i
  -- `toL`
  withLocalDeclD `a FXY fun a => do
    let value ← if ctx.isBlock then do
        let g ← mkFreshExprSyntheticOpaqueMVar lay
        ctx.polyToLBlock P X Y g.mvarId! i.fvarId!
        instantiateMVars g
      else do
        let np := ctx.params.size + 1
        mkCasesOnApp ctx.F (← ctx.levelsWith ctx.F [P.ly]) FXY.getAppArgs a (← getLevel lay)
          (fun is _ => do
            ctx.polyILay P X Y (← ctx.pack (← fullIdx ctx.F np FXY.getAppArgs is)))
          fun cname xs => do
            let some m := ctx.ctors.findIdx? (ctx.fCtor · == cname)
              | throwError "internal error: unexpected constructor {cname}"
            ctx.polyLayer P m X Y
              (← ctorArgsOf ctx.F np FXY.getAppArgs xs ctx.ctors[m]!.args.size)
    let (type, value) ← close (P.premises ++ #[X, Y, i, a]) lay value
    addDef (ctx.polyName "toL") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref
  -- `ofL`
  withLocalDeclD `z lay fun z => do
    let S ← ctx.polyS P
    let Sn := ctx.polyName "S"
    let s ← mkAppM ``Sigma.fst #[z]
    let w ← mkAppM ``Sigma.snd #[z]
    let motive (j s : Expr) : TermElabM Expr := do
      mkArrow (← mkArrow (mkApp2 (← ctx.polyP P) j s) X)
        (← mkArrow (← ctx.polyKidsTy P X Y j s) (← ctx.polyFI P X Y j P.ly))
    let args := P.psB.push i
    let value ← mkCasesOnApp Sn S.getAppFn.constLevels! args s (← getLevel (← motive i s))
      (fun is s => do motive (← fullIdx Sn P.psB.size args is)[0]! s) fun cname xs => do
        let some m := ctx.ctors.findIdx? (Sn ++ ·.fname == cname)
          | throwError "internal error: unexpected constructor {cname}"
        let nsh := ctx.ctors[m]!.nests.size + P.fields[m]!.size
        let sargs ← ctorArgsOf Sn P.psB.size args xs ((ctx.polyPlain P m).size + nsh)
        let shape := mkAppN (← polyConst cname) (P.psB ++ sargs)
        let j := (← whnf (← inferType shape)).appArg!
        lam `v (← mkArrow (mkApp2 (← ctx.polyP P) j shape) X) fun v => do
          lam `k (← ctx.polyKidsTy P X Y j shape) fun k =>
            ctx.polyOfLBody P m X Y v k sargs
    let value := mkApp2 value (← mkAppM ``Prod.fst #[w]) (← mkAppM ``Prod.snd #[w])
    let (type, value) ← close (P.premises ++ #[X, Y, i, z]) FXY value
    addDef (ctx.polyName "ofL") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref

/-- `T.Poly.toL` and `T.Poly.ofL`. -/
def genPolyLayer (P : Poly) : TermElabM Unit := do
  if ctx.idxed then return ← ctx.genIPolyLayer P
  let close (xs : Array Expr) (type value : Expr) : TermElabM (Expr × Expr) :=
    withBinderInfo (P.consts ++ P.SR) .implicit do
      return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  withLocalDecl `X .implicit (mkSort P.lx.succ) fun X => do
  withLocalDecl `Y .implicit (mkSort P.ly.succ) fun Y => do
  let FXY ← ctx.polyF P X Y P.ly
  let lay ← ctx.polyLay P X Y
  -- `toL`, by cases on `F`.
  withLocalDeclD `a FXY fun a => do
    let np := ctx.params.size + 1
    let value ← mkCasesOnApp ctx.F (← ctx.levelsWith ctx.F [P.ly]) FXY.getAppArgs a
      (← getLevel lay) (fun _ _ => pure lay) fun cname xs => do
        let some m := ctx.ctors.findIdx? (ctx.fCtor · == cname)
          | throwError "internal error: unexpected constructor {cname}"
        ctx.polyLayer P m X Y (← ctorArgsOf ctx.F np FXY.getAppArgs xs ctx.ctors[m]!.args.size)
    let (type, value) ← close (P.premises ++ #[X, Y, a]) lay value
    addDef (ctx.polyName "toL") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref
  -- `ofL`, by cases on the shape.
  withLocalDeclD `z lay fun z => do
    let S ← ctx.polyS P
    let s ← mkAppM ``Sigma.fst #[z]
    let w ← mkAppM ``Sigma.snd #[z]
    let motive (s : Expr) : TermElabM Expr := do
      mkArrow (← mkArrow (mkApp (← ctx.polyP P) s) X)
        (← mkArrow (← mkArrow (mkApp (← ctx.polyB P) s) Y) FXY)
    let value ← mkCasesOnApp (ctx.polyName "S") (S.getAppFn.constLevels!) P.psB s
      (← getLevel (← motive s)) (fun _ s => motive s) fun cname xs => do
        let some m := ctx.ctors.findIdx? (ctx.polyName "S" ++ ·.fname == cname)
          | throwError "internal error: unexpected constructor {cname}"
        let shape := mkAppN (mkAppN (.const cname S.getAppFn.constLevels!) P.psB) xs
        lam `v (← mkArrow (mkApp (← ctx.polyP P) shape) X) fun v => do
          lam `k (← mkArrow (mkApp (← ctx.polyB P) shape) Y) fun k =>
            ctx.polyOfLBody P m X Y v k xs
    let value := mkApp2 value (← mkAppM ``Prod.fst #[w]) (← mkAppM ``Prod.snd #[w])
    let (type, value) ← close (P.premises ++ #[X, Y, z]) FXY value
    addDef (ctx.polyName "ofL") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref

/-- Destructure a layer `z = ⟨s, v, k⟩` and run `k` on each case of the shape, with its
constructor. -/
def polyCasesLay (P : Poly) (g : MVarId) (z : Expr) (k : Nat → MVarId → TermElabM Unit)
    (i? : Option Expr := none) : TermElabM Unit := do
  let #[sg] ← g.cases z.fvarId! | throwError "internal error: cases on a layer"
  let #[sg'] ← sg.mvarId.cases sg.fields[1]!.fvarId! | throwError "internal error: cases on a pair"
  let s := sg'.subst.apply sg.fields[0]!
  -- With indices, the shape is at the variable `i`, which the cases instantiate.
  let S ← match i? with
    | some i => pure (mkApp (← ctx.polyS P) (sg'.subst.apply (sg.subst.apply i)))
    | none => ctx.polyS P
  let g ← sg'.mvarId.withContext do sg'.mvarId.replaceLocalDeclDefEq s.fvarId! S
  for sg in ← g.cases s.fvarId! do
    let some m := ctx.ctors.findIdx? fun c => sg.ctorName == some (ctx.polyName "S" ++ c.fname)
      | throwError "internal error: unexpected shape {sg.ctorName}"
    k m sg.mvarId

/-- Split the index `i` of the presentation into its components by cases, for cases on
`a : T.F (H X) Y (ι i)`: nothing for one index, the dependent pairs for several, in a block the
type and its indices. Returns the goals with `a`, its type at the components (`polyWhnfIdx`). -/
def polyCasesIdx (g : MVarId) (i a : FVarId) : MetaM (Array (MVarId × FVarId)) := do
  if !ctx.isBlock && ctx.k == 1 then return #[(g, a)]
  let rec split (g : MVarId) (i : FVarId) : Nat → MetaM (Array MVarId)
    | n + 1 => do
      let sgs ← g.cases i
      if ctx.isBlock || n ≤ 1 then return sgs.map (·.mvarId)
      sgs.flatMapM fun sg => split sg.mvarId sg.fields.back!.fvarId! n
    | 0 => return #[g]
  (← split g i ctx.k).mapM fun g => g.withContext do
    let some a := (← getLCtx).lastDecl | throwError "internal error: no layer to destructure"
    let g ← g.replaceLocalDeclDefEq a.fvarId (← ctx.polyWhnfIdx (← instantiateMVars a.type))
    return (g, a.fvarId)

/-- With indices, `T.Poly.ofL_toL`, `T.Poly.toL_ofL`, `T.Poly.ofL_map` at an index `i` of the
presentation, as without: `cases` on `a` after `polyCasesIdx`, the positions by `casesPos`, and
the indexed structures of the nested arguments. -/
def genIPolyLaws (P : Poly) : TermElabM Unit := do
  let close (xs : Array Expr) (type value : Expr) : TermElabM (Expr × Expr) :=
    withBinderInfo (P.consts ++ P.SR) .implicit do
      return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  let add (s : String) (xs : Array Expr) (stmt pf : Expr) : TermElabM Unit := do
    let (type, value) ← close xs stmt pf
    addThm (ctx.polyName s) (← ctx.levelParamsOf P.fresh #[type]) type value ctx.ref
  let hasLayer (m : Nat) : Bool := ctx.ctors[m]!.hasNest || !P.fields[m]!.isEmpty
  withLocalDecl `X .implicit (mkSort P.lx.succ) fun X => do
  withLocalDecl `Y .implicit (← ctx.polyYTy P P.Hs X P.ly) fun Y => do
  withLocalDecl `i .implicit P.I fun i => do
  let FXY ← ctx.polyFI P X Y i P.ly
  let lay ← ctx.polyILay P X Y i
  let toL (a : Expr) := ctx.polyAt P "toL" [] #[X, Y, i, a]
  let ofL (z : Expr) := ctx.polyAt P "ofL" [] #[X, Y, i, z]
  let hole := P.subX P.Hs X (← ctx.packFam Y)
  -- `ofL_toL`
  withLocalDeclD `a FXY fun a => do
    let pf ← proveHere (← mkEq (← ofL (← toL a)) a) fun g => do
      for (g, a) in ← ctx.polyCasesIdx g i.fvarId! a.fvarId! do
      for sg in ← g.cases a do
        let some m := ctx.ctors.findIdx? fun c => sg.ctorName == some (ctx.fCtor c)
          | throwError "internal error: unexpected case {sg.ctorName}"
        if !hasLayer m then
          sg.mvarId.refl
          continue
        sg.mvarId.withContext do
        let c := ctx.ctors[m]!
        let some (_, _, rhs) := (← instantiateMVars (← sg.mvarId.getType)).eq?
          | throwError "internal error: expected an equation"
        -- The arguments of `F.c`, those `T.F` takes as parameters too.
        let np := ctx.params.size + 1
        let ys := rhs.getAppArgs.extract np rhs.getAppNumArgs
        let σ := polySubst P c ys X
        let ys' ← (c.args.zip ys).zipIdx.mapM fun ((a, y), k) => do
          if let some f := P.fields[m]!.find? (·.k == k) then
            let t ← mkAppOptM ``Codata.Occ.toC #[none, none, none, σ f.occ, X, y]
            return ← ctx.mkOfCPlain (σ f.occ) X (← mkAppM ``Sigma.fst #[t]) fun q => do
              return mkApp (← mkAppM ``Sigma.snd #[t]) q
          match a.kind with
          | .nest n =>
            let o := ctx.nestAt n P.ly σ
            let t ← mkAppOptM ``Codata.IOcc.toC #[none, none, none, none, none, o, hole, y]
            ctx.mkOfC o hole (← mkAppM ``Sigma.fst #[t]) fun q => do
              return mkApp (← mkAppM ``Sigma.snd #[t]) q
          | _ => pure y
        let lhs := mkAppN rhs.getAppFn (rhs.getAppArgs.extract 0 np ++ ys')
        let g ← sg.mvarId.replaceTargetDefEq (← mkEq lhs rhs)
        withUnfolding <| simpOnly g #[``Codata.Occ.ofC_toC', ``Codata.IOcc.ofC_toC']
    add "ofL_toL" (P.premises ++ #[X, Y, i, a]) (← mkEq (← ofL (← toL a)) a) pf
  -- `toL_ofL`
  withLocalDeclD `z lay fun z => do
    let pf ← proveHere (← mkEq (← toL (← ofL z)) z) fun g => (ctx.polyCasesLay P g z · (some i))
      fun m g => g.withContext do
      let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
        | throwError "internal error: expected an equation"
      let mut g ← g.replaceTargetDefEq (← mkEq (← whnf lhs) rhs)
      let thms := (ctx.ctors[m]!.nests.map fun _ => ``Codata.IOcc.toC_ofC) ++
        P.fields[m]!.map fun _ => ``Codata.Occ.toC_ofC
      for thm in thms do
        let r ← g.rewrite (← g.getType) (← mkConstWithFreshMVarLevels thm)
        g ← g.replaceTargetEq r.eNew r.eqProof
      let shape := (← whnf rhs).appFn!.appArg!
      let j := (← whnf (← inferType shape)).appArg!
      let gs ← Tactic.run g do
        Tactic.evalTactic (← `(tactic|
          refine congrArg (Sigma.mk _) (Prod.ext (funext fun p => ?_) (funext fun b => ?_))))
      for (g', fam) in gs.zip [← ctx.polyP P, ← ctx.polyB P] do
        g'.withContext do
        let p := (← getLCtx).lastDecl.get!.toExpr
        let g' ← g'.replaceLocalDeclDefEq p.fvarId! (mkApp2 fam j shape)
        for sg in ← casesPos g' p.fvarId! do sg.mvarId.refl
    add "toL_ofL" (P.premises ++ #[X, Y, i, z]) (← mkEq (← toL (← ofL z)) z) pf
  -- `ofL_map`
  withLocalDecl `Y' .implicit (← ctx.polyYTy P P.Hs X P.ly') fun Y' => do
  withLocalDeclD `f (P.subX P.Hs X (← ctx.famFn Y Y')) fun f => do
  withLocalDeclD `z lay fun z => do
    let fι ← lam `j P.I fun j => do
      return mkAppN f (← ctx.projs (← ctx.polyIota P P.Hs X j))
    let mapped ← mkAppOptM ``Codata.ILay.map #[← ctx.polySig P, ← ctx.polyP P, X,
      ← ctx.polyLayFam P P.Hs X Y, ← ctx.polyLayFam P P.Hs X Y', fι, i, z]
    let lhs ← ctx.polyAt P "ofL" [(P.fresh[2]!, P.ly')] #[X, Y', i, mapped]
    let rhs := mkAppN (← ctx.constWith ctx.Fmap [P.ly, P.ly'])
      (ctx.polyParams P P.Hs X ++ #[Y, Y', f] ++ (← ctx.projs (← ctx.polyIota P P.Hs X i)) ++
        #[← ofL z])
    let stmt ← mkEq lhs rhs
    let pf ← proveHere stmt fun g => (ctx.polyCasesLay P g z · (some i)) fun m g => do
      if !hasLayer m then return ← g.refl
      g.withContext do
      let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
        | throwError "internal error: expected an equation"
      let g ← g.replaceTargetDefEq (← mkEq (← whnf lhs) (← whnf rhs))
      withUnfolding do
        if let some g ← simpOnlyStep g
            #[``Codata.ILay.map, ``Codata.Occ.map_ofC, ``Codata.IOcc.map_ofC] then
          g.refl
    add "ofL_map" (P.premises ++ #[X, Y, Y', f, i, z]) stmt pf

/-- `T.Poly.ofL_toL`, `T.Poly.toL_ofL`, `T.Poly.ofL_map`. -/
def genPolyLaws (P : Poly) : TermElabM Unit := do
  if ctx.idxed then return ← ctx.genIPolyLaws P
  let close (xs : Array Expr) (type value : Expr) : TermElabM (Expr × Expr) :=
    withBinderInfo (P.consts ++ P.SR) .implicit do
      return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  let add (s : String) (xs : Array Expr) (stmt pf : Expr) : TermElabM Unit := do
    let (type, value) ← close xs stmt pf
    addThm (ctx.polyName s) (← ctx.levelParamsOf P.fresh #[type]) type value ctx.ref
  let hasLayer (m : Nat) : Bool := ctx.ctors[m]!.hasNest || !P.fields[m]!.isEmpty
  withLocalDecl `X .implicit (mkSort P.lx.succ) fun X => do
  withLocalDecl `Y .implicit (mkSort P.ly.succ) fun Y => do
  let FXY ← ctx.polyF P X Y P.ly
  let lay ← ctx.polyLay P X Y
  let toL (a : Expr) := ctx.polyAt P "toL" [] #[X, Y, a]
  let ofL (z : Expr) := ctx.polyAt P "ofL" [] #[X, Y, z]
  -- `ofL_toL`: `ofL (toL (F.c ys))` unfolds to `F.c ys'` with `ofC o ⟨(toC o x).1, …⟩` for a
  -- field or a nested argument `x`, which `ofC_toC'` rewrites.
  withLocalDeclD `a FXY fun a => do
    let pf ← proveHere (← mkEq (← ofL (← toL a)) a) fun g => do
      for sg in ← g.cases a.fvarId! do
        let some m := ctx.ctors.findIdx? fun c => sg.ctorName == some (ctx.fCtor c)
          | throwError "internal error: unexpected case {sg.ctorName}"
        if !hasLayer m then
          sg.mvarId.refl
          continue
        sg.mvarId.withContext do
        let c := ctx.ctors[m]!
        let some (_, _, rhs) := (← instantiateMVars (← sg.mvarId.getType)).eq?
          | throwError "internal error: expected an equation"
        let ys := sg.fields
        let σ := polySubst P c ys X
        let roundTrip (o hole y : Expr) : TermElabM Expr := do
          let t ← mkAppOptM ``Codata.Occ.toC #[none, none, none, o, hole, y]
          ctx.mkOfC o hole (← mkAppM ``Sigma.fst #[t]) fun q => do
            return mkApp (← mkAppM ``Sigma.snd #[t]) q
        let ys' ← (c.args.zip ys).zipIdx.mapM fun ((a, y), i) => do
          if let some f := P.fields[m]!.find? (·.k == i) then return ← roundTrip (σ f.occ) X y
          match a.kind with
          | .nest n => roundTrip (ctx.nestAt n P.ly σ) Y y
          | _ => pure y
        let pre := rhs.getAppArgs.extract 0 (rhs.getAppNumArgs - ys.size)
        let lhs := mkAppN rhs.getAppFn (pre ++ ys')
        let g ← sg.mvarId.replaceTargetDefEq (← mkEq lhs rhs)
        withUnfolding <| simpOnly g #[``Codata.Occ.ofC_toC']
    add "ofL_toL" (P.premises ++ #[X, Y, a]) (← mkEq (← ofL (← toL a)) a) pf
  -- `toL_ofL`: the layers `toC o (ofC o z)` rewritten one by one, then the positions by cases.
  withLocalDeclD `z lay fun z => do
    let pf ← proveHere (← mkEq (← toL (← ofL z)) z) fun g => ctx.polyCasesLay P g z fun m g =>
      g.withContext do
      let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
        | throwError "internal error: expected an equation"
      let mut g ← g.replaceTargetDefEq (← mkEq (← whnf lhs) rhs)
      for _ in [0:ctx.ctors[m]!.nests.size + P.fields[m]!.size] do
        let r ← g.rewrite (← g.getType) (← mkConstWithFreshMVarLevels ``Codata.Occ.toC_ofC)
        g ← g.replaceTargetEq r.eNew r.eqProof
      let shape := (← whnf rhs).appFn!.appArg!
      let gs ← Tactic.run g do
        Tactic.evalTactic (← `(tactic|
          refine congrArg (Sigma.mk _) (Prod.ext (funext fun p => ?_) (funext fun b => ?_))))
      for (g', fam) in gs.zip [← ctx.polyP P, ← ctx.polyB P] do
        g'.withContext do
        let p := (← getLCtx).lastDecl.get!.toExpr
        let g' ← g'.replaceLocalDeclDefEq p.fvarId! (mkApp fam shape)
        for sg in ← g'.cases p.fvarId! do sg.mvarId.refl
    add "toL_ofL" (P.premises ++ #[X, Y, z]) (← mkEq (← toL (← ofL z)) z) pf
  -- `ofL_map`
  withLocalDecl `Y' .implicit (mkSort P.ly'.succ) fun Y' => do
  withLocalDeclD `f (← mkArrow Y Y') fun f => do
  withLocalDeclD `z lay fun z => do
    let mapped ← mkAppM ``Codata.Lay.map #[f, z]
    let lhs ← ctx.polyAt P "ofL" [(P.fresh[2]!, P.ly')] #[X, Y', mapped]
    let rhs := mkAppN (← ctx.constWith ctx.Fmap [P.ly, P.ly'])
      (ctx.polyParams P P.Hs X ++ #[Y, Y', f, ← ofL z])
    let stmt ← mkEq lhs rhs
    let pf ← proveHere stmt fun g => ctx.polyCasesLay P g z fun m g => do
      if !hasLayer m then return ← g.refl
      g.withContext do
      let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
        | throwError "internal error: expected an equation"
      let g ← g.replaceTargetDefEq (← mkEq (← whnf lhs) (← whnf rhs))
      withUnfolding do
        if let some g ← simpOnlyStep g #[``Codata.Lay.map, ``Codata.Occ.map_ofC] then g.refl
    add "ofL_map" (P.premises ++ #[X, Y, Y', f, z]) stmt pf

/-! ### The fixpoint and the instances -/

/-- With indices, `T.Poly.fix (X) : IPolyFix P tree X (fun i => T (H X) (ι i))`: `icoFix`
(`iinFix`), whose `corec` (`fold`) on states over the index of the presentation is the type's on
the states `Along ι St` (`Over ι St`) over its own index, and the bisimulation (induction)
principle from the contract along `ι` (`ico_bisim`, `iin_ind`). The proof arguments are `rw` on
goal metavariables, as without indices. -/
def genIPolyFix (P : Poly) : TermElabM Unit := do
  let L ← ctx.tLvl
  let pX (X : Expr) := ctx.polyParams P P.Hs X
  let ident (n : Name) : Ident := mkCIdent n
  -- The layers maps composed by the states (`Along`, `Over`) are the expected ones by unfolding:
  -- `rfl` after the rewriting.
  let rwTac (steps : Array (Bool × Name)) : TermElabM (TSyntax `tactic) := do
    let rules ← steps.mapM fun (rev, n) =>
      if rev then `(Parser.Tactic.rwRule| ← $(ident n):ident)
      else `(Parser.Tactic.rwRule| $(ident n):ident)
    `(tactic| rw [$rules,*] <;> rfl)
  let σE ← ctx.polySig P
  let Pc ← ctx.polyP P
  withLocalDeclD `X (mkSort P.lx.succ) fun X => do
  -- The type at the premises, curried, and as a family over the index of the presentation.
  let T := mkAppN (← ctx.constWith ctx.name []) (pX X)
  let TI ← ctx.polyLayFam P P.Hs X T
  let I' := P.subX P.Hs X (← ctx.ixp)
  let ιf ← lam `j P.I fun j => ctx.polyIota P P.Hs X j
  let idxAt (i : Expr) : MetaM (Array Expr) := do ctx.projs (← ctx.polyIota P P.Hs X i)
  let yL (w : Level) := [(P.fresh[2]!, w)]
  let toL (Y i a : Expr) (w : Level) := ctx.polyAt P "toL" (yL w) #[X, Y, i, a]
  let ofL (Y i z : Expr) (w : Level) := ctx.polyAt P "ofL" (yL w) #[X, Y, i, z]
  let dtorAt (i t : Expr) : MetaM Expr := do
    return mkAppN (← ctx.constWith ctx.dtor []) (pX X ++ (← idxAt i) |>.push t)
  let dL ← lam `i P.I (bi := .implicit) fun i => do
    lam `a (mkApp TI i).headBeta fun a => do toL T i (← dtorAt i a) L
  let K := mkAppN (← ctx.constWith ctx.contract []) (pX X)
  -- The layer on families over `I'`, the contract's, curried for `T.F`.
  let curry (Y : Expr) : TermElabM Expr := do return P.subX P.Hs X (← ctx.curryFam Y)
  let ofLz (ty : Expr) : TermElabM Expr := lamOf ty fun xs => do
    ofL (← curry xs[0]!) xs[1]! xs[2]! (← famLevel xs[0]!)
  let toLz (ty : Expr) : TermElabM Expr := lamOf ty fun xs => do
    toL (← curry xs[0]!) xs[1]! xs[2]! (← famLevel xs[0]!)
  let ofL_toL (Y i a : Expr) : TermElabM Expr := do
    ctx.polyAt P "ofL_toL" (yL (← famLevel Y)) #[X, Y, i, a]
  let ofL_map (ty : Expr) : TermElabM Expr := lamOf ty fun xs => do
    ctx.polyAt P "ofL_map" [(P.fresh[2]!, ← famLevel xs[0]!), (P.fresh[3]!, ← famLevel xs[1]!)]
      #[X, ← curry xs[0]!, ← curry xs[1]!, P.subX P.Hs X (← ctx.curryN xs[2]! 1), xs[3]!, xs[4]!]
  -- `T.F (H X) Y` over `I'`, for the states.
  let FOn (Y : Expr) (w : Level) : TermElabM Expr := lam `j I' fun j => do
    return mkAppN (← ctx.polyF P X Y w) (← ctx.projs j)
  let value ← withUnfolding do
    if ctx.co then
      let f ← mkAppOptM ``Codata.icoFix #[σE, Pc, X, TI, dL]
      let f ← fillArg f fun ty => lamOf ty fun xs => do
        let (St, c, i, s) := (xs[0]!, xs[1]!, xs[2]!, xs[3]!)
        let lSt ← famLevel St
        let Al ← mkAppOptM ``Codata.Along #[σE, I', ιf, St]
        let AlC ← curry Al
        let ofL' ← lam `i P.I (bi := .implicit) fun i => do
          lam `z (← ctx.polyILay P X AlC i) fun z => ofL AlC i z lSt
        let co ← mkAppOptM ``Codata.Along.coalg
          #[σE, Pc, X, I', ιf, St, ← FOn AlC lSt, ofL', c]
        let mk ← mkAppOptM ``Codata.Along.mk #[σE, I', ιf, St, i, s]
        return mkAppN (← ctx.constWith ctx.corec [lSt])
          (pX X ++ #[AlC, P.subX P.Hs X (← ctx.curryN co 1)] ++ (← idxAt i) |>.push mk)
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.dtor_corec), (false, ``Codata.Along.coalg_mk),
          (true, ctx.polyName "ofL_map"), (false, ctx.polyName "toL_ofL")])
      let bis ← mkAppFirst ``Codata.ico_bisim #[σE, Pc, X] 6
      let bis ← fillArg bis fun _ => pure K
      let bis ← fillArg bis fun _ => pure ιf
      let bis ← fillArg bis fun _ => pure dL
      let bis ← fillArg bis ofLz
      let bis ← fillArg bis fun ty => lamOf ty fun xs => do
        ofL_toL T xs[0]! (← dtorAt xs[0]! xs[1]!)
      let bis ← fillArg bis ofL_map
      fillArg f fun _ => pure bis
    else
      let ctorL ← lam `i P.I (bi := .implicit) fun i => do
        lam `z (← ctx.polyILay P X T i) fun z => do
          return mkAppN (← ctx.constWith ctx.ctor []) (pX X ++ (← idxAt i) |>.push
            (← ofL T i z L))
      let f ← mkAppOptM ``Codata.iinFix #[σE, Pc, X, TI, ctorL, dL]
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.dtor_ctor), (false, ctx.polyName "toL_ofL")])
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.polyName "ofL_toL"), (false, ctx.ctor_dtor)])
      let f ← fillArg f fun ty => lamOf ty fun xs => do
        let (St, a, i, t) := (xs[0]!, xs[1]!, xs[2]!, xs[3]!)
        let lSt ← famLevel St
        let Ov ← mkAppOptM ``Codata.Over #[σE, I', ιf, St]
        let OvC ← curry Ov
        let toL' ← lam `i P.I (bi := .implicit) fun i => do
          lam `y (← ctx.polyFI P X OvC i lSt) fun y => toL OvC i y lSt
        let alg ← mkAppOptM ``Codata.Over.alg #[σE, Pc, X, I', ιf, St, ← FOn OvC lSt, toL', a]
        let folded := mkAppN (← ctx.constWith ctx.fold [lSt])
          (pX X ++ #[OvC, P.subX P.Hs X (← ctx.curryN alg 1)] ++ (← idxAt i) |>.push t)
        return mkApp2 folded i (← mkEqRefl (← ctx.polyIota P P.Hs X i))
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.fold_ctor), (false, ``Codata.Over.alg_apply),
          (true, ctx.polyName "ofL_map"), (false, ctx.polyName "toL_ofL")])
      let ind ← mkAppFirst ``Codata.iin_ind #[σE, Pc, X] 6
      let ind ← fillArg ind fun _ => pure K
      let ind ← fillArg ind fun _ => pure ιf
      let ind ← fillArg ind toLz
      let ind ← fillArg ind ofLz
      let ind ← fillArg ind fun ty => lamOf ty fun xs => do
        ofL_toL (← curry xs[0]!) xs[1]! xs[2]!
      let ind ← fillArg ind ofL_map
      fillArg f fun _ => pure ind
  let value ← instantiateMVars value
  let type ← inferType value
  let (type, value) ← withBinderInfo (P.consts ++ P.SR) .implicit do
    let xs := P.premises.push X
    return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  addDef (ctx.polyName "fix") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref

/-- `T.Poly.fix (X) : PolyFix P tree X (T (H X))`, from the public declarations of the type:
`coFix` (`inFix` for `data`), its proof arguments by `rw` on goal metavariables, and the
bisimulation (induction) principle from the contract (`co_bisim`, `in_ind`). -/
def genPolyFix (P : Poly) : TermElabM Unit := do
  if ctx.idxed then return ← ctx.genIPolyFix P
  let L ← ctx.tLvl
  let pX (X : Expr) := ctx.polyParams P P.Hs X
  let ident (n : Name) : Ident := mkCIdent n
  let rwTac (steps : Array (Bool × Name)) : TermElabM (TSyntax `tactic) := do
    let rules ← steps.mapM fun (rev, n) =>
      if rev then `(Parser.Tactic.rwRule| ← $(ident n):ident)
      else `(Parser.Tactic.rwRule| $(ident n):ident)
    `(tactic| rw [$rules,*])
  withLocalDeclD `X (mkSort P.lx.succ) fun X => do
  let TX := mkAppN (← ctx.constWith ctx.name []) (pX X)
  let yL (w : Level) := [(P.fresh[2]!, w)]
  let toL (Y a : Expr) (w : Level) := ctx.polyAt P "toL" (yL w) #[X, Y, a]
  let ofL (Y z : Expr) (w : Level) := ctx.polyAt P "ofL" (yL w) #[X, Y, z]
  let dtorAt (t : Expr) : MetaM Expr := return mkAppN (← ctx.constWith ctx.dtor []) (pX X |>.push t)
  let dL ← lam `a TX fun a => do toL TX (← dtorAt a) L
  let K := mkAppN (← ctx.constWith ctx.contract []) (pX X)
  let ofLz (ty : Expr) : TermElabM Expr := lamOf ty fun xs => do
    ofL xs[0]! xs[1]! (← typeLevel xs[0]!)
  let ofL_toL (Y a : Expr) : TermElabM Expr := do
    ctx.polyAt P "ofL_toL" (yL (← typeLevel Y)) #[X, Y, a]
  let ofL_map (ty : Expr) : TermElabM Expr := lamOf ty fun xs => do
    ctx.polyAt P "ofL_map" [(P.fresh[2]!, ← typeLevel xs[0]!), (P.fresh[3]!, ← typeLevel xs[1]!)]
      (#[X] ++ xs)
  let value ← withUnfolding do
    if ctx.co then
      let f ← mkAppOptM ``Codata.coFix #[none, none, none, none, none, dL]
      let f ← fillArg f fun ty => lamOf ty fun xs => do
        let (St, c, s) := (xs[0]!, xs[1]!, xs[2]!)
        let lSt ← typeLevel St
        let c' ← lam `st St fun st => ofL St (mkApp c st) lSt
        return mkAppN (← ctx.constWith ctx.corec [lSt]) (pX X ++ #[St, c', s])
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.dtor_corec), (true, ctx.polyName "ofL_map"),
          (false, ctx.polyName "toL_ofL")])
      let bis ← fillArg (← mkAppMVars ``Codata.co_bisim 6) fun _ => pure K
      let bis ← fillArg bis fun _ => pure dL
      let bis ← fillArg bis ofLz
      let bis ← fillArg bis fun ty => lamOf ty fun xs => do ofL_toL TX (← dtorAt xs[0]!)
      let bis ← fillArg bis ofL_map
      fillArg f fun _ => pure bis
    else
      let ctorL ← lam `z (← ctx.polyLay P X TX) fun z => do
        return mkAppN (← ctx.constWith ctx.ctor []) (pX X |>.push (← ofL TX z L))
      let f ← mkAppOptM ``Codata.inFix #[none, none, none, none, none, ctorL, dL]
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.dtor_ctor), (false, ctx.polyName "toL_ofL")])
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.polyName "ofL_toL"), (false, ctx.ctor_dtor)])
      let f ← fillArg f fun ty => lamOf ty fun xs => do
        let (St, a, t) := (xs[0]!, xs[1]!, xs[2]!)
        let lSt ← typeLevel St
        let a' ← lam `y (← ctx.polyF P X St lSt) fun y => do return mkApp a (← toL St y lSt)
        return mkAppN (← ctx.constWith ctx.fold [lSt]) (pX X ++ #[St, a', t])
      let f ← fillArg f fun ty => do
        proveOn ty (← rwTac #[(false, ctx.fold_ctor), (true, ctx.polyName "ofL_map"),
          (false, ctx.polyName "toL_ofL")])
      let ind ← fillArg (← mkAppMVars ``Codata.in_ind 6) fun _ => pure K
      let ind ← fillArg ind fun ty => lamOf ty fun xs => do toL xs[0]! xs[1]! (← typeLevel xs[0]!)
      let ind ← fillArg ind ofLz
      let ind ← fillArg ind fun ty => lamOf ty fun xs => ofL_toL xs[0]! xs[1]!
      let ind ← fillArg ind ofL_map
      fillArg f fun _ => pure ind
  let value ← instantiateMVars value
  let type ← inferType value
  let (type, value) ← withBinderInfo (P.consts ++ P.SR) .implicit do
    let xs := P.premises.push X
    return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  addDef (ctx.polyName "fix") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref

/-- `T.Poly.fix` at the premises `Hs` (with their instances `insts`) and `X`, at the universes
`σ`. -/
def polyFixAt (P : Poly) (σ : List (Name × Level)) (Hs insts : Array Expr) (X : Expr) :
    MetaM Expr := do
  return mkAppN (← polyConst (ctx.polyName "fix") σ) (P.consts ++ Hs ++ P.SR ++ insts |>.push X)

/-- Add the instance `n` of type `type` with value `value`, closed over `xs`. -/
def addPolyInstance (P : Poly) (n : Name) (xs : Array Expr) (type value : Expr) :
    TermElabM Unit := do
  let (type, value) ← withBinderInfo (P.consts ++ P.Hs ++ P.Hs' ++ P.SR) .implicit do
    return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  addDef n (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref
  registerInstance n .global (eval_prio default)

/-- When the last parameter is the last hole, the instances `T.Poly.instPolyIsoEta`,
`T.Poly.instPolyMapEta` for `T a₁ … aₙ₋₁` itself, a type `T` without indices: `fun X => T a X` is
`T a`, the instances at the identity in the last parameter, the other holes constant. -/
def genPolyEta (P : Poly) (T : Name) : TermElabM Unit := do
  let isoN := T ++ `Poly ++ `instPolyIso
  let mapN := T ++ `Poly ++ `instPolyMap
  let some last := ctx.params.back? | return
  unless P.holes.back? == some last do return
  let others := P.holes.pop
  let lastLvl ← typeLevel last
  let lastTy ← inferType last
  let idH ← lam `X lastTy fun X => pure X
  let etaHs ← others.mapM fun a => lam `X lastTy fun _ => pure a
  let etaSR ← (others.mapM fun a => do return #[a, ← lam `x a fun _ => pure (Lean.mkConst ``Empty)])
  let etaSR := etaSR.flatten ++
    #[Lean.mkConst ``Unit, ← lam `x (Lean.mkConst ``Unit) fun _ => pure (Lean.mkConst ``Unit)]
  let etaHs := etaHs.push idH
  let synth (Hs : Array Expr) : TermElabM (Array Expr) :=
    (Array.range Hs.size).mapM fun i => do
      synthInstance (← mkAppM ``Codata.PolyIso #[Hs[i]!, etaSR[2 * i]!, etaSR[2 * i + 1]!])
  let insts ← synth etaHs
  -- The universes of the instances at these premises.
  let levelsOf (es : Array Expr) : MetaM (List (Name × Level)) := do
    let mut σ := [(P.fresh[0]!, lastLvl)]
    for i in [0:P.holes.size] do
      σ := σ ++ [(P.fresh[5 + 2 * i]!, ← typeLevel es[2 * i]!), (P.fresh[6 + 2 * i]!, Level.zero)]
    return σ
  let σ ← levelsOf etaSR
  let isoE := mkAppN (← polyConst isoN σ) (P.consts ++ etaHs ++ etaSR ++ insts)
  -- The functors `fun X => T a X` of the types, eta-reduced.
  let etaType (ty : Expr) : Expr :=
    mkAppN ty.getAppFn (ty.getAppArgs.modify 0 Expr.eta |>.modify 1 Expr.eta)
  ctx.addPolyInstance P (T ++ `Poly ++ `instPolyIsoEta) (P.consts ++ others)
    (etaType (← whnfR (← inferType isoE))) isoE
  -- Across universes only when the universe of the last parameter is its own.
  let tied ← match lastLvl with
    | .param u => do
      let shared ← others.anyM fun a => do
        return (collectLevelParams {} (← inferType a)).params.contains u
      pure (!P.primes.any (·.1 == u) || shared)
    | _ => pure true
  -- The primed universes of `instPolyMap`: that of the last parameter, if it is its own, the
  -- others unprimed (the other holes are fixed).
  let lastLvl' := match lastLvl with
    | .param _ => if tied then lastLvl else P.lvl 4
    | _ => lastLvl
  let σu := P.primes.filterMap fun (v, v') => match v' with
    | .param n => some (n, if !tied && lastLvl == .param v then lastLvl' else .param v)
    | _ => none
  let idH' ← lam `X (mkSort lastLvl'.succ) fun X => pure X
  let etaHs' := (← others.mapM fun a => lam `X (mkSort lastLvl'.succ) fun _ => pure a).push idH'
  let insts' ← synth etaHs'
  let σm := σ ++ [(P.fresh[1]!, lastLvl')] ++ σu
  let mapE := mkAppN (← polyConst mapN σm)
    (P.consts ++ etaHs ++ etaHs' ++ etaSR ++ insts ++ insts')
  let mapTy ← whnfR (← inferType mapE)
  ctx.addPolyInstance P (T ++ `Poly ++ `instPolyMapEta) (P.consts ++ others)
    (etaType mapTy) mapE

/-- With indices, for each type `Tₘ` (the family, or the types of a block) at its indices `idx`,
which are arguments of the instances: `Tₘ.Poly.instPolyIso` for `fun X => Tₘ (H X) idx`, at the
trees of shapes at its index `i` of the presentation (`⟨idx⟩`, or `Blk.Poly.Ix.Tₘ idx`), and
`Tₘ.Poly.instPolyMap`; for a type of a block without indices, the eta forms (`genPolyEta`). -/
def genIPolyInstances (P : Poly) : TermElabM Unit := do
  let σE ← ctx.polySig P
  let Pc ← ctx.polyP P
  let fam := if ctx.co then ``Codata.Signature.Cotype else ``Codata.Signature.Intype
  let tree ← mkAppM (if ctx.co then ``Codata.coITree else ``Codata.inITree) #[σE]
  for m in [0:ctx.types.size] do
    let t := ctx.types[m]!
    let i ← ctx.polyIdx P (ctx.wrap m t.idx)
    let W ← mkAppM fam #[σE, i]
    let path ← mkAppOptM ``Codata.IPath #[σE, Pc, none, tree, i]
    -- The functor `fun X => Tₘ (H X) idx`, and at the primed universes `fun X => Tₘ (H' X) idx`.
    let Tc ← ctx.constWith t.name []
    let funT ← lam `X (mkSort P.lx.succ) fun X =>
      return mkAppN Tc (ctx.polyParams P P.Hs X ++ t.idx)
    let funT' ← lam `X (mkSort P.lx'.succ) fun X =>
      return mkAppN (P.prime Tc) (ctx.polyParams P P.Hs' X ++ t.idx)
    let isoN := t.name ++ `Poly ++ `instPolyIso
    let mapN := t.name ++ `Poly ++ `instPolyMap
    -- `PolyIso`
    do
      let equiv ← lam `X (mkSort P.lx.succ) (bi := .implicit) fun X => do
        mkAppOptM ``Codata.IPolyFix.equiv #[none, none, none, none, none, none,
          ← ctx.polyFixAt P [] P.Hs P.insts X, i]
      let value ← mkAppOptM ``Codata.PolyIso.mk #[funT, W, path, equiv]
      ctx.addPolyInstance P isoN (P.premises ++ t.idx) (← mkAppM ``Codata.PolyIso #[funT, W, path])
        value
    -- `PolyMap`
    do
      let iso := mkAppN (← polyConst isoN) (P.premises ++ t.idx)
      let σ' := (P.fresh[0]!, P.lx') :: P.primes
      let iso' := mkAppN (← polyConst isoN σ') (P.consts ++ P.Hs' ++ P.SR ++ P.insts' ++ t.idx)
      let mp ← mkAppOptM ``Codata.PolyMap.mk #[funT, funT', W, path, iso, iso']
      let fix (X Y : Expr) : MetaM (Expr × Expr) := do
        return (← ctx.polyFixAt P [] P.Hs P.insts X, ← ctx.polyFixAt P σ' P.Hs' P.insts' Y)
      let along (n : Name) (xs : Array Expr) : TermElabM Expr := do
        let (M, M') ← fix xs[0]! xs[1]!
        mkAppOptM n #[none, none, none, none, none, none, M, none, none, M', xs[2]!, i, xs[3]!]
      let mp ← fillArg mp fun ty => lamOf ty (along ``Codata.IPolyFix.map)
      let mp ← withUnfolding <| fillArg mp fun ty => lamOf ty (along ``Codata.IPolyFix.equiv_map)
      let xs := P.consts ++ P.Hs ++ P.Hs' ++ P.SR ++ P.insts ++ P.insts' ++ t.idx
      ctx.addPolyInstance P mapN xs (← inferType mp) (← instantiateMVars mp)
    if t.idx.isEmpty then ctx.genPolyEta P t.name

/-- `T.Poly.instPolyIso`, `T.Poly.instPolyMap`, and when the last parameter is the last hole,
the instances `T.Poly.instPolyIsoEta`, `T.Poly.instPolyMapEta` for `T a₁ … aₙ₋₁` itself. -/
def genPolyInstances (P : Poly) : TermElabM Unit := do
  if ctx.idxed then return ← ctx.genIPolyInstances P
  let B ← ctx.polyB P
  let fam := if ctx.co then ``Codata.Signature.Cotype else ``Codata.Signature.Intype
  let W ← mkAppM fam #[← mkAppOptM ``Codata.shapeSig #[none, B], mkConst ``Unit.unit]
  let tree ← mkAppM (if ctx.co then ``Codata.coTree else ``Codata.inTree) #[B]
  let path ← mkAppM ``Codata.Path #[← ctx.polyP P, tree]
  -- The functor `fun X => T (H X)`, and at the primed universes `fun X => T (H' X)`.
  let Tc ← ctx.constWith ctx.name []
  let funT ← lam `X (mkSort P.lx.succ) fun X => return mkAppN Tc (ctx.polyParams P P.Hs X)
  let funT' ← lam `X (mkSort P.lx'.succ) fun X =>
    return mkAppN (P.prime Tc) (ctx.polyParams P P.Hs' X)
  let isoN := ctx.polyName "instPolyIso"
  let mapN := ctx.polyName "instPolyMap"
  -- `PolyIso`
  do
    let equiv ← lam `X (mkSort P.lx.succ) (bi := .implicit) fun X => do
      mkAppM ``Codata.PolyFix.equiv #[← ctx.polyFixAt P [] P.Hs P.insts X]
    let value ← mkAppOptM ``Codata.PolyIso.mk #[funT, W, path, equiv]
    ctx.addPolyInstance P isoN P.premises (← mkAppM ``Codata.PolyIso #[funT, W, path]) value
  -- `PolyMap`
  do
    let iso := mkAppN (← polyConst isoN) P.premises
    let σ' := (P.fresh[0]!, P.lx') :: P.primes
    let iso' := mkAppN (← polyConst isoN σ') (P.consts ++ P.Hs' ++ P.SR ++ P.insts')
    let m ← mkAppOptM ``Codata.PolyMap.mk #[funT, funT', W, path, iso, iso']
    let fix (X Y : Expr) : MetaM (Expr × Expr) := do
      return (← ctx.polyFixAt P [] P.Hs P.insts X, ← ctx.polyFixAt P σ' P.Hs' P.insts' Y)
    let m ← fillArg m fun ty => lamOf ty fun xs => do
      let (M, M') ← fix xs[0]! xs[1]!
      mkAppM ``Codata.PolyFix.map #[M, M', xs[2]!, xs[3]!]
    let m ← withUnfolding <| fillArg m fun ty => lamOf ty fun xs => do
      let (M, M') ← fix xs[0]! xs[1]!
      mkAppM ``Codata.PolyFix.equiv_map #[M, M', xs[2]!, xs[3]!]
    let xs := P.consts ++ P.Hs ++ P.Hs' ++ P.SR ++ P.insts ++ P.insts'
    ctx.addPolyInstance P mapN xs (← inferType m) (← instantiateMVars m)
  ctx.genPolyEta P ctx.name

/-- Generate the instances for the holes. -/
def genPoly (holes : Array Expr) : TermElabM Unit := do
  let nh := holes.size
  let consts := ctx.params.filter (!holes.contains ·)
  let holeTys ← holes.mapM fun a => do instantiateMVars (← inferType a)
  let holeLvls ← holes.mapM fun a => typeLevel a
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
  let sub (s : String) (i : Nat) : Name :=
    if nh == 1 then Name.mkSimple s else Name.mkSimple (s ++ Nat.toSubscriptString (i + 1))
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
  -- The fields at parameter positions, with their structures in the premises.
  let fields ← ctx.ctors.mapM fun c => c.args.zipIdx.filterMapM fun (a, k) => do
    unless a.kind.isData do return none
    let some i := holes.findIdx? (a.type.containsFVar ·.fvarId!) | return none
    let oH ← mkAppOptM ``Codata.Occ.ofIso #[Hs[i]!, none, none, none]
    let o ← instantiateMVars
      (← occOf (paramHoles holes[i]! holeLvls[i]! (some (oH, lv 0))) a.type)
    let oty ← whnfR (← inferType o)
    unless oty.isAppOfArity ``Codata.Occ 3 do
      throwError "internal error: unexpected occurrence structure{indentExpr oty}"
    return some ({
      k, occ := o, sh := oty.getAppArgs[0]!, pos := oty.getAppArgs[1]! } : HoleField)
  let P := { P0 with Hs, Hs', Ss, Rs, insts, insts', fields }
  -- With indices, the index of the presentation: in a block a new one, without the holes.
  let P ← if ctx.isBlock then withCurrHeartbeats <| ctx.genPolyIx P
    else pure { P with I := ctx.J }
  -- Each part with its own heartbeat budget, as the steps of the pipeline.
  withCurrHeartbeats <| ctx.genPolyShapes P
  if ctx.idxed then
    withCurrHeartbeats do
      ctx.genPolyIdx P
      ctx.genPolySig P
  withCurrHeartbeats <| ctx.genPolyLayer P
  withCurrHeartbeats <| ctx.genPolyLaws P
  withCurrHeartbeats <| ctx.genPolyFix P
  withCurrHeartbeats <| ctx.genPolyInstances P

/-- Step 5: the instances of the types of a declaration that has holes. Failure is a warning,
whatever the exception (a timeout too): the declarations of this step are rolled back, and the
types stay as they are. -/
def deriveInstances : TermElabM Unit := do
  let s ← saveState
  tryCatchRuntimeEx
    (withCurrHeartbeats do
      let holes ← ctx.polyHoles
      if holes.isEmpty then return
      ctx.genPoly holes)
    fun e => do
      s.restore (restoreInfo := true)
      let ns ← getCurrNamespace
      let shorts := ctx.types.map fun t => m!"`{t.name.replacePrefix ns .anonymous}`"
      let types := if ctx.isBlock then "The types themselves are" else "The type itself is"
      logWarning m!"{MessageData.joinSep shorts.toList ", "} cannot be nested through: no \
        `Codata.PolyIso` instance was generated. {types} not affected.\n{e.toMessageData}"

end Ctx

end Codata.Gen
