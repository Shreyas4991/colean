import Colean.Gen.Derive.Holes

/-!
# Generators on `Expr`, step 5: the presentation

The local variables of the generated declarations (`Poly`), the index of the presentation
(`genPolyIx`), the constructors of the presentation with their split arguments (`VCtor`,
`withVCtors`), and its shapes, positions, index and signature (`T.Poly.S`, `T.Poly.P`,
`T.Poly.B`, `T.Poly.idx`, `T.Poly.sig`).
-/

open Lean Meta Elab Term

namespace Codata.Gen

namespace Ctx

variable (ctx : Ctx)

/-! ### The context of the instances -/

/-- A field at a parameter position: its position among the constructor's arguments, and its
structure in the premise, with its shapes and positions. -/
structure HoleField where
  k : Nat
  occ : Expr
  sh : Expr
  pos : Expr
  deriving Inhabited

/-- A nested argument with a parameter that varies outside the occurrences under a named type
constructor or a function (`p : List (α × T α)`, `k : Nat → α × T α`), or in a block one whose
positions are at a type of the block only after cases on them (`p : List (RA α × Nat)`): its
position among the constructor's arguments, its structure in two variables (`Occ₂`, `mixOf`;
with indices `IOcc₂` over the index of the presentation, `imixOcc`) over the premises, the
occurrences at the analysis' universe, with its shapes and positions of both kinds (and with
indices the index of a position in `Y`), and the argument as the analysis has it, with its
structure in the occurrences alone. -/
structure MixField where
  k : Nat
  occ : Expr
  sh : Expr
  px : Expr
  py : Expr
  arg : ArgInfo
  nest : Nest
  /-- With indices, the index of a position in `Y`, in the index of the presentation. -/
  pidx? : Option Expr := none
  /-- With indices, when the positions in `Y` are all at one index after cases on them: the
  structure is the plain one `o₂` at that index `i₀` of the presentation (`IOcc₂.ofOcc₂`), and
  the rules are stated with `o₂`, as without indices. -/
  flat? : Option (Expr × Expr) := none
  deriving Inhabited

/-- How an argument of a constructor is presented (`VCtor`): as an argument of the presentation,
or split through a product or a sum, whose two types (of the analysis) are kept. -/
inductive Tpl where
  | part (a : ArgInfo)
  | prod (l r : Tpl)
  | sum (l r : Tpl) (A B : Expr)
  deriving Inhabited

/-- Does the template split through a sum? -/
def Tpl.hasSum : Tpl → Bool
  | .part _ => false
  | .prod l r => l.hasSum || r.hasSum
  | .sum .. => true

/-- The ways through the template: the alternative taken at each sum on the way, and the parts
reached, in order. -/
def Tpl.paths : Tpl → Array (Array Bool × Array ArgInfo)
  | .part a => #[(#[], #[a])]
  | .prod l r => l.paths.flatMap fun (cl, al) => r.paths.map fun (cr, ar) => (cl ++ cr, al ++ ar)
  | .sum l r _ _ => l.paths.map (fun (c, as) => (#[true] ++ c, as)) ++
      r.paths.map (fun (c, as) => (#[false] ++ c, as))

/-- A constructor of the presentation: a constructor `real` of the type with an alternative at
each sum of its split arguments (`tpls`, per argument), its arguments the parts on the way, in
`ctor`. Without splits it is the constructor itself. The arguments of a constructor are split when
a nested one mentions a parameter that varies outside the occurrences (`α × T α`), or in a block
has its positions at several types (`A × B`), so that each part is a field at a parameter
position, a recursive argument or data. -/
structure VCtor where
  real : Nat
  tpls : Array Tpl
  choices : Array Bool
  ctor : Ctor
  deriving Inhabited

/-- Does the constructor split an argument? -/
def VCtor.split (v : VCtor) : Bool := v.tpls.any fun | .part _ => false | _ => true

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
  /-- The premises `PolyMap Hᵢ H'ᵢ` of `instPolyMap`, so that it is a map between instantiations
  of one functor only when the premises are. -/
  maps : Array Expr := #[]
  fields : Array (Array HoleField)
  /-- The arguments with a structure in two variables of each constructor of the presentation,
  which there are of kind `.data`. -/
  mixed : Array (Array MixField) := #[]
  /-- The constructors of the presentation, `fields` and `mixed` by their position. -/
  vc : Array VCtor := #[]
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

/-- The arguments with a structure in two variables of the `m`-th constructor. -/
def mixAt (m : Nat) : Array MixField := (P.mixed[m]?).getD #[]

/-- `∀ xs, type` and `fun xs => value`, the constants and the presentations `Sᵢ`, `Rᵢ` implicit:
a declaration of this step over the premises. -/
def close (xs : Array Expr) (type value : Expr) : TermElabM (Expr × Expr) :=
  withBinderInfo (P.consts ++ P.SR) .implicit do
    return (← mkForallFVars xs type, ← mkLambdaFVars xs value)

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

/-- Add the definition `T.Poly.s` of type `type` and value `value`, closed over `xs`
(`Poly.close`). -/
def addPolyDef (P : Poly) (s : String) (xs : Array Expr) (type value : Expr) : TermElabM Unit := do
  let (type, value) ← P.close xs type value
  addDef (ctx.polyName s) (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref

/-- Add the theorem `T.Poly.s` of statement `stmt` and proof `pf`, closed over `xs`
(`Poly.close`). -/
def addPolyThm (P : Poly) (s : String) (xs : Array Expr) (stmt pf : Expr) : TermElabM Unit := do
  let (type, value) ← P.close xs stmt pf
  addThm (ctx.polyName s) (← ctx.levelParamsOf P.fresh #[type]) type value ctx.ref

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
  let ty ← mkForallFVars P.consts (mkSort r.succ)
  let ctorName (m : Nat) : Name :=
    name ++ Name.mkSimple (ctx.shortName m)
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

/-! ### Split arguments -/

/-- The kind of a part of a split argument, as the front end classifies an argument. -/
def classifyPart (ty : Expr) : TermElabM ArgKind := do
  unless ctx.mentions ty do return .data
  let e ← whnfOcc ty
  if let some idx := ctx.holeOf? e then return .plain idx
  if ctx.isTypeApp e then throwError badOcc
  let arity? ← withReducible <| forallTelescopeReducing ty fun ys body => do
    if ys.isEmpty || (ctx.holeOf? (← whnfOcc body)).isNone then return none
    for y in ys do
      if ctx.mentions (← inferType y) then throwError badDomain
    return some ys.size
  if let some n := arity? then return .fn n
  let occ ← instantiateMVars (← occOf (ctx.holes ctx.famIdx?) ty)
  let args := (← whnfR (← inferType occ)).getAppArgs
  if ctx.idxed then
    return .nest { occ, sh := args[1]!, pos := args[2]!, pidx? := some args[3]! }
  return .nest { occ, sh := args[0]!, pos := args[1]!, pidx? := none }

/-- With indices, is `ty` nested with positions at an index only after cases on them (at several
indices, or through a product or a sum)? In a block the index of a position must be a type of the
block at variables (the presentation's index); in a family, the rules of the map and of
membership are stated by components then, each at the type at its index, rather than through the
indexed structure (`IOcc.map`, `IPolyIso.Mem` at an index). -/
def severalIdx (ty : Expr) : TermElabM Bool := do
  if !ctx.idxed || !ctx.mentions ty then return false
  let .nest n ← ctx.classifyPart ty | return false
  let some pidx := n.pidx? | return false
  withLocalDeclD `s n.sh fun s => withLocalDeclD `q (mkApp n.pos s).headBeta fun q => do
    let i ← Core.betaReduce (mkApp2 pidx s q)
    return i.containsFVar s.fvarId! || i.containsFVar q.fvarId!

/-- Does the type `ty` of a nested argument, or of a part of it, need to be split: does it mention
both the types and a hole outside the occurrences, or with indices is it at several indices? -/
def needsSplit (holes : Array Expr) (ty : Expr) : TermElabM Bool := do
  return ctx.mentions ty && (!(ctx.outside holes ty).isEmpty || (← ctx.severalIdx ty))

/-- The template of the argument `a` at its part `name : ty`, its parts new local variables. -/
partial def splitTpl (holes : Array Expr) (a : ArgInfo) (name : Name) (ty : Expr)
    (k : Tpl → TermElabM α) : TermElabM α := do
  let e ← whnfOcc ty
  if (← ctx.needsSplit holes ty) && (e.isAppOfArity ``Prod 2 || e.isAppOfArity ``Sum 2) then
    let (A, B) := (e.appFn!.appArg!, e.appArg!)
    if e.isAppOfArity ``Prod 2 then
      splitTpl holes a (name.appendAfter "_fst") A fun l =>
        splitTpl holes a (name.appendAfter "_snd") B fun r => k (.prod l r)
    else
      splitTpl holes a (name.appendAfter "_inl") A fun l =>
        splitTpl holes a (name.appendAfter "_inr") B fun r => k (.sum l r A B)
  else
    let kind ← ctx.classifyPart ty
    withLocalDeclD name ty fun x =>
      k (.part { a with fvar := x, name, bi := .default, type := ty, kind })

/-- The number of constructors of the presentation for a nested argument of type `ty` split
through its products and sums (`splitTpl`): the ways through its sums. -/
partial def splitCount (holes : Array Expr) (ty : Expr) : TermElabM Nat := do
  let e ← whnfOcc ty
  if (← ctx.needsSplit holes ty) && (e.isAppOfArity ``Prod 2 || e.isAppOfArity ``Sum 2) then
    let l ← splitCount holes e.appFn!.appArg!
    let r ← splitCount holes e.appArg!
    return if e.isAppOfArity ``Prod 2 then l * r else l + r
  return 1

/-- The most constructors of the presentation for one constructor of the type. Beyond, the
arguments through sums are not split: they have a structure in two variables (`mixOcc`), with
indices or in a block in two variables over the index (`imixOcc`), or without a parameter
outside the occurrences their indexed structure. -/
def maxSplit : Nat := 8

/-- `n`, or `n` with the first suffix `_1`, `_2`, … for which `ok` holds. -/
partial def freshSuffix (n : String) (ok : String → Bool) (k : Nat := 0) : String :=
  let n' := if k == 0 then n else n ++ "_" ++ toString k
  if ok n' then n' else freshSuffix n ok (k + 1)

/-- Run `k` on the constructors of the presentation (`VCtor`): a nested argument that needs it
split through products and sums (`needsSplit`), its parts new local variables, a constructor per
way through the sums, unless that makes more than `maxSplit` constructors, when the arguments
through sums are kept. Arguments that do not split are kept: in a block, a nested argument at
several types that is not a product or a sum fails later, at its positions. The names of the
constructors of the presentation and of the parts are internal: those taken, by a constructor or
an argument, get a suffix (`freshSuffix`). -/
partial def withVCtors (holes : Array Expr) (k : Array VCtor → TermElabM α) : TermElabM α := do
  let rec go (m : Nat) (acc : Array VCtor) : TermElabM α := do
    if h : m < ctx.ctors.size then
      let c := ctx.ctors[m]
      let splits ← c.args.mapM fun a => do
        let e ← whnfOcc a.type
        return a.kind.isNest && (← ctx.needsSplit holes a.type) &&
          (e.isAppOfArity ``Prod 2 || e.isAppOfArity ``Sum 2)
      -- Through sums, at most `maxSplit` constructors of the presentation.
      let counts ← (c.args.zip splits).mapM fun (a, sp) =>
        if sp then ctx.splitCount holes a.type else pure 1
      let keepSums := counts.foldl (· * ·) 1 > maxSplit
      let rec args (i : Nat) (tpls : Array Tpl) : TermElabM α := do
        if h : i < c.args.size then
          let a := c.args[i]
          if splits[i]! && !(keepSums && counts[i]! > 1) then
            ctx.splitTpl holes a a.name a.type fun t => args (i + 1) (tpls.push t)
          else args (i + 1) (tpls.push (.part a))
        else
          let paths := tpls.foldl (init := #[((#[] : Array Bool), (#[] : Array ArgInfo))])
            fun ps t => ps.flatMap fun (c₁, a₁) => t.paths.map fun (c₂, a₂) => (c₁ ++ c₂, a₁ ++ a₂)
          -- The names of the parts, unlike those of the arguments.
          let paths := paths.map fun (choices, as) => Id.run do
            let mut out : Array ArgInfo := #[]
            for a in as do
              if c.args.any (·.fvar == a.fvar) then out := out.push a
              else
                let taken (n : String) : Bool :=
                  c.args.any (·.name.toString == n) || out.any (·.name.toString == n)
                let n := freshSuffix a.name.toString (!taken ·)
                out := out.push { a with name := Name.mkSimple n }
            return (choices, out)
          -- The names of the constructors through sums, unlike those of the type and the others.
          let mut vs : Array VCtor := #[]
          for (choices, as) in paths do
            let sfx := if choices.isEmpty then "" else
              "_" ++ "_".intercalate (choices.map (if · then "inl" else "inr")).toList
            let ok (s : String) : Bool := sfx.isEmpty || (
              !ctx.ctors.any (fun c' => c'.name.toString == c.name.toString ++ s ||
                c'.fname.toString == c.fname.toString ++ s) &&
              !(acc ++ vs).any fun v => v.ctor.name.toString == c.name.toString ++ s ||
                v.ctor.fname.toString == c.fname.toString ++ s)
            let sfx := freshSuffix sfx ok
            let ctor := { c with
              name := Name.mkSimple (c.name.toString ++ sfx)
              fname := Name.mkSimple (c.fname.toString ++ sfx), args := as }
            vs := vs.push { real := m, tpls, choices, ctor }
          go (m + 1) (acc ++ vs)
      args 0 #[]
    else k acc
  go 0 #[]

/-! ### The presentation: `S`, `P`, `B` -/

/-- The data arguments of the `m`-th constructor that are not at parameter positions, nor with
a structure in two variables. -/
def polyPlain (P : Poly) (m : Nat) : Array ArgInfo :=
  (P.vc[m]!.ctor.args.zipIdx.filter fun (a, k) =>
    a.kind.isData && !P.fields[m]!.any (·.k == k) && !(P.mixAt m).any (·.k == k)).map (·.1)

/-- Run `k` on the shape binders of the `m`-th constructor: those of its nested arguments, then
of its fields at parameter positions, then of its arguments with a structure in two variables.
-/
def withPolyShapes (P : Poly) (m : Nat) (bi : BinderInfo) (k : Array Expr → TermElabM α) :
    TermElabM α :=
  let c := P.vc[m]!.ctor
  ctx.withShapeBinders c bi fun nshs =>
    withLocalsN P.fields[m]!.size (fun j => do
      let f := P.fields[m]![j]!
      return (c.args[f.k]!.name.appendAfter "_s", bi, f.sh)) fun fshs =>
    withLocalsN (P.mixAt m).size (fun j => do
      let f := (P.mixAt m)[j]!
      return (c.args[f.k]!.name.appendAfter "_s", bi, f.sh)) fun mshs => k (nshs ++ fshs ++ mshs)

/-- `T.Poly.S.c psB plain shapes`. -/
def polySCtor (P : Poly) (m : Nat) (args : Array Expr) : MetaM Expr := do
  return mkAppN (← polyConst (ctx.polyName "S" ++ P.vc[m]!.ctor.fname)) (P.psB ++ args)

/-- `T.Poly.S psB`, `T.Poly.P psB s`, `T.Poly.B psB s`. -/
def polyS (P : Poly) : MetaM Expr := return mkAppN (← polyConst (ctx.polyName "S")) P.psB
def polyP (P : Poly) : MetaM Expr := return mkAppN (← polyConst (ctx.polyName "P")) P.psB
def polyB (P : Poly) : MetaM Expr := return mkAppN (← polyConst (ctx.polyName "B")) P.psB

/-- The name of the constructor of `P` (`B`) for the argument `a` of `c`. -/
def polyPos (s : String) (c : Ctor) (a : ArgInfo) : Name :=
  ctx.polyName s ++ Name.mkSimple (c.fname.toString ++ "_" ++ a.name.toString)

/-- Declare the inductive `name` with the parameters `psB` (the premises explicit, the parameters
of the type with the binder infos the user wrote) and the constructors `mkCtors I` over a local
variable `I` for it: a type `S` (`idx := false`) or a family over `S`; with indices, `S` is a
family over the index `P.I`, and so are the families over it. Its universe is inferred from the
constructors. -/
def polyInductive (P : Poly) (name : Name) (idx : Bool)
    (mkCtors : Expr → TermElabM (Array (Name × Expr))) : TermElabM Unit := do
  let psB := P.psB
  let declare (lvl : Level) : TermElabM Expr := do
    withBinderInfo (psB.filter (!P.consts.contains ·)) .default do
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
structure), `T.Poly.B` (a position per recursive argument, as in `T.B`); an argument with a
structure in two variables has one of each, with a position of either kind of its structure. -/
def genPolyShapes (P : Poly) : TermElabM Unit := do
  let ms := Array.range P.vc.size
  -- With indices, the index of the presentation of the result of the `m`-th constructor.
  let cIdx (m : Nat) : MetaM (Array Expr) := do
    if ctx.idxed then return #[← ctx.polyIdx P P.vc[m]!.ctor.idx] else return #[]
  -- `S`: the data, the shapes of the nested arguments and of the fields.
  ctx.polyInductive P (ctx.polyName "S") false fun Sv => ms.mapM fun m =>
    ctx.withPolyShapes P m .default fun shs => do
      let plain := (polyPlain P m).map (·.fvar)
      let t ← withBinderInfo P.psB .implicit do
        mkForallFVars (P.psB ++ plain ++ shs) (mkAppN Sv (P.psB ++ (← cIdx m)))
      return (ctx.polyName "S" ++ P.vc[m]!.ctor.fname, t)
  -- A constructor of `P` or `B` for the `m`-th constructor: data and shapes implicit, `extra`.
  let posCtor (Iv : Expr) (m : Nat) (extra : Array Expr → (Array Expr → TermElabM Expr) →
      TermElabM Expr) : TermElabM Expr :=
    ctx.withPolyShapes P m .implicit fun shs => extra shs fun ys => do
      let plain := (polyPlain P m).map (·.fvar)
      withBinderInfo (P.psB ++ plain) .implicit do
        mkForallFVars (P.psB ++ plain ++ shs ++ ys)
          (mkApp (mkAppN Iv (P.psB ++ (← cIdx m))) (← ctx.polySCtor P m (plain ++ shs)))
  -- The constructor of `P` (`B`) for the `j`-th argument with a structure in two variables.
  let mixCtor (Iv : Expr) (m j : Nat) (s : String) : TermElabM (Name × Expr) := do
    let c := P.vc[m]!.ctor
    let f := (P.mixAt m)[j]!
    let i := c.nests.size + P.fields[m]!.size + j
    let t ← posCtor Iv m fun shs k =>
      withLocalDeclD `q (mkApp (if s == "P" then f.px else f.py) shs[i]!).headBeta fun q => k #[q]
    return (ctx.polyPos s c c.args[f.k]!, t)
  ctx.polyInductive P (ctx.polyName "P") true fun Iv => ms.flatMapM fun m => do
    let c := P.vc[m]!.ctor
    let nn := c.nests.size
    let fs ← (Array.range P.fields[m]!.size).mapM fun j => do
      let f := P.fields[m]![j]!
      let t ← posCtor Iv m fun shs k =>
        withLocalDeclD `q (mkApp f.pos shs[nn + j]!).headBeta fun q => k #[q]
      return (ctx.polyPos "P" c c.args[f.k]!, t)
    return fs ++ (← (Array.range (P.mixAt m).size).mapM fun j => mixCtor Iv m j "P")
  ctx.polyInductive P (ctx.polyName "B") true fun Iv => ms.flatMapM fun m => do
    let c := P.vc[m]!.ctor
    let rs ← c.recArgs.mapM fun a => do
      let t ← posCtor Iv m fun shs k => withPosArgs c a (shs.extract 0 c.nests.size) k
      return (ctx.polyPos "B" c a, t)
    return rs ++ (← (Array.range (P.mixAt m).size).mapM fun j => mixCtor Iv m j "B")

/-- The index of the child at a position, from the arguments `bargs` of its constructor in
`T.Poly.B` (the plain data, the shapes, the extra arguments), as `posIdx` for `T.B`. A field at a
parameter position occurs in no index (`refineHoles`). -/
def polyPosIdx (P : Poly) (m : Nat) (a : ArgInfo) (bargs : Array Expr) : MetaM Expr := do
  let c := P.vc[m]!.ctor
  let plain := polyPlain P m
  let np := plain.size
  let nsh := c.nests.size + P.fields[m]!.size + (P.mixAt m).size
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

/-- The index of the child at a position in `Y` of the `j`-th argument with a structure in two
variables of the `m`-th constructor, from the arguments `bargs` of its constructor in `T.Poly.B`
(the plain data, the shapes, the position of the structure): the index of that position. -/
def polyMixIdx (P : Poly) (m j : Nat) (bargs : Array Expr) : MetaM Expr := do
  let c := P.vc[m]!.ctor
  let f := (P.mixAt m)[j]!
  let plain := polyPlain P m
  let np := plain.size
  let some pidx := f.pidx?
    | throwError "internal error: a structure in two variables without indices"
  let σ (e : Expr) := e.replaceFVars (plain.map (·.fvar)) (bargs.extract 0 np)
  let i := np + c.nests.size + P.fields[m]!.size + j
  return (mkApp2 (σ pidx) bargs[i]! bargs.back!).headBeta

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
      -- An argument with a structure in two variables: the index of its position in `Y`.
      let mix? := (Array.range P.vc.size).findSome? fun m =>
        let c := P.vc[m]!.ctor
        ((P.mixAt m).findIdx? (ctx.polyPos "B" c c.args[·.k]! == cname)).map (m, ·)
      if let some (m, j) := mix? then
        let nargs ← ctx.withPolyShapes P m .implicit fun shs =>
          pure ((polyPlain P m).size + shs.size + 1)
        return ← polyMixIdx P m j (← ctorArgsOf Bn P.psB.size args xs nargs)
      let some (m, a) := (Array.range P.vc.size).findSome? fun m =>
          let c := P.vc[m]!.ctor
          (c.recArgs.find? (ctx.polyPos "B" c · == cname)).map (m, ·)
        | throwError "internal error: unexpected constructor {cname}"
      let c := P.vc[m]!.ctor
      let nargs ← ctx.withPolyShapes P m .implicit fun shs =>
        withPosArgs c a (shs.extract 0 c.nests.size) fun ys =>
          pure ((polyPlain P m).size + shs.size + ys.size)
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
  let (type, value) ← withBinderInfo (P.psB.filter (!P.consts.contains ·)) .default do
    return (← mkForallFVars P.psB type, ← mkLambdaFVars P.psB value)
  addDef (ctx.polyName "sig") (← ctx.levelParamsOf P.fresh #[type, value]) type value ctx.ref
    (reducible := true)

end Ctx

end Codata.Gen
