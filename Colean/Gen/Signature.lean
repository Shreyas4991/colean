import Colean.Gen.Functor
import Colean.Model.Intype

/-!
# Generators on `Expr`, step 2: the signature

*Spec.* Input: the context. Output: the fixed data format of `Model/Cotype.lean` for the
declaration:

* `T.Shape (params) : ∀ idx, Type _`, one constructor per constructor of `T` with its data
  arguments and the shape `x_s` of each nested argument `x`;
* `T.B (params) : ∀ idx, T.Shape params idx → Type _`, the positions: one constructor `c_x` per
  recursive argument `x`, with the data and shapes implicit, and the telescope of `x` (under a
  telescope) or a position `q` of its structure (nested);
* with indices, `T.idx`, the index of a position, by cases; with several, `T.Ix`, the packed
  index type, and `T.ShapeP`, the shapes on it;
* `T.sig : Codata.Signature`, all of it bundled.

It also holds the helpers of the later steps for the model's terms: the packed index type, the
signature and its universes, and the conversions between curried families (`∀ j₁ j₂, X j₁ j₂`)
and families on the packed index (`X : Ix → Type`), `curryFam`, `packFam`, `curryN`, `uncurryN`.
-/

open Lean Meta Elab Term

namespace Codata.Gen

/-- The data arguments of a constructor. -/
def Ctor.dataArgs (c : Ctor) : Array ArgInfo := c.args.filter (·.kind.isData)

/-- The recursive arguments of a constructor. -/
def Ctor.recArgs (c : Ctor) : Array ArgInfo := c.args.filter (!·.kind.isData)

/-- The nested arguments of a constructor, with their structures. -/
def Ctor.nests (c : Ctor) : Array (ArgInfo × Nest) := c.args.filterMap fun a =>
  match a.kind with
  | .nest n => some (a, n)
  | _ => none

namespace Ctx

variable (ctx : Ctx)

/-! ### Terms of the model -/

/-- The packed index type as the generated declarations state it: `T.Ix params` for several
indices, the index type for one, `Unit` for none. -/
def ixp : MetaM Expr := do
  if ctx.k ≥ 2 then return mkAppN (← ctx.constWith ctx.Ix []) ctx.params else return ctx.J

/-- `T.sig params`. -/
def sigE : MetaM Expr := return mkAppN (← ctx.constWith ctx.sig []) ctx.params

/-- The universes `w, u, v` of `T.sig params : Signature.{w, u, v}`. -/
def sigLvls : MetaM (Level × Level × Level) := do
  match ← whnfR (← inferType (← ctx.sigE)) with
  | .const _ [w, u, v] => return (w, u, v)
  | ty => throwError "internal error: unexpected type of the signature{indentExpr ty}"

/-- The universe of the type, `max w u v`. -/
def tLvl : MetaM Level := do
  let (w, u, v) ← ctx.sigLvls
  return (mkLevelMax' (mkLevelMax' w u) v).normalize

/-- A constant of the signature theory at the signature's universes, then `extra`. -/
def sigConst (n : Name) (extra : List Level := []) : MetaM Expr := do
  let (w, u, v) ← ctx.sigLvls
  return .const n ([w, u, v] ++ extra)

/-- `Cotype (T.sig params)`, or `Intype` for `datatype`: the model's family on the packed index. -/
def modelFam : MetaM Expr := do
  return mkApp (← ctx.sigConst (if ctx.co then ``Codata.Signature.Cotype
    else ``Codata.Signature.Intype)) (← ctx.sigE)

/-- `σ.Obj X i`, for `X` on the packed index at universe `w`. -/
def objAt (w : Level) (X i : Expr) : MetaM Expr := do
  return mkApp3 (← ctx.sigConst ``Codata.Signature.Obj [w]) (← ctx.sigE) X i

/-- The packed index arguments `pack idx` (`ctx.pack`). -/
def packI : MetaM Expr := ctx.pack ctx.idx

/-- A family on the packed index as a curried family: `fun j₁ j₂ => X ⟨j₁, j₂⟩`, `X`, or `X ()`.
-/
def curryFam (X : Expr) : TermElabM Expr := do
  if ctx.k == 0 then return mkApp X (mkConst ``Unit.unit)
  if ctx.k == 1 then return X
  ctx.withJs fun js => do mkLambdaFVars js (mkApp X (← ctx.pack js))

/-- A curried family on the packed index: `fun p => X p.1 p.2`, `X`, or `fun p => X`. -/
def packFam (X : Expr) : TermElabM Expr := do
  if ctx.k == 1 then return X
  withLocalDeclD `p (← ctx.ixp) fun p => do mkLambdaFVars #[p] (mkAppN X (← ctx.projs p))

/-- A function on the packed index with `extra` further arguments, curried:
`fun j₁ j₂ e… => f ⟨j₁, j₂⟩ e…`, `f`, or `fun e… => f () e…` (`f ()` for none). -/
def curryN (f : Expr) (extra : Nat) : TermElabM Expr := do
  if ctx.k == 1 then return f
  ctx.withJs fun js => do
    let fp := mkApp f (← ctx.pack js)
    forallBoundedTelescope (← whnf (← inferType fp)) extra fun es _ => do
      mkLambdaFVars (js ++ es) (mkAppN fp es)

/-- A curried function with `extra` further arguments on the packed index:
`fun p e… => c p.1 p.2 e…`, `c`, or `fun p e… => c e…`. -/
def uncurryN (c : Expr) (extra : Nat) : TermElabM Expr := do
  if ctx.k == 1 then return c
  withLocalDeclD `p (← ctx.ixp) fun p => do
    let cp := mkAppN c (← ctx.projs p)
    forallBoundedTelescope (← whnf (← inferType cp)) extra fun es _ => do
      mkLambdaFVars (#[p] ++ es) (mkAppN cp es)

/-! ### Arguments -/

/-- Run `k` on the telescope of an argument of kind `.fn n` with type `ty`, as explicit binders.
-/
def withTele (n : Nat) (ty : Expr) (k : Array Expr → Expr → TermElabM α) : TermElabM α :=
  withReducible <| forallBoundedTelescope ty n fun ys body =>
    withNewBinderInfos (ys.map (·.fvarId!, .default)) (k ys body)

/-- The shapes or positions of a structure, checked not to depend on the universe of the
occurrences. -/
def ofStructure (e : Expr) : MetaM Expr := do
  if (collectLevelParams {} e).params.contains ctx.uT then
    throwError "the shapes of a nested argument depend on the universe of the type being \
      defined, which is not supported:{indentExpr e}"
  return e

/-- `T.Shape params idx`. -/
def shapeAt (idx : Array Expr) : MetaM Expr := do
  ctx.genAt ctx.Shape [] idx

/-- `T.B params idx s`. -/
def bAt (idx : Array Expr) (s : Expr) : MetaM Expr := do
  ctx.genAt ctx.B [] (idx |>.push s)

/-- `T.idx params idx s b`. -/
def idxAt (idx : Array Expr) (s b : Expr) : MetaM Expr := do
  ctx.genAt ctx.idxN [] (idx ++ #[s, b])

/-- `@T.Shape.c params data… shapes…`. -/
def shapeCtorApp (c : Ctor) (args : Array Expr) : MetaM Expr := do
  ctx.genAt (ctx.shapeCtor c) [] args

/-- `@T.B.c_x params data… shapes… extra…`. -/
def bCtorApp (c : Ctor) (a : ArgInfo) (args : Array Expr) : MetaM Expr := do
  ctx.genAt (ctx.bCtor c a) [] args

/-- The arguments of `I.c` applied as `mkCasesOnApp` gives them, `xs` after the parameters of
`I`: when `I` took some of its indices `args` as parameters (`fixedIndices`), the constructor's
first arguments are those indices. -/
def ctorArgsOf (I : Name) (nParams : Nat) (args xs : Array Expr) (nArgs : Nat) :
    MetaM (Array Expr) := do
  let info ← getConstInfoInduct I
  let promoted := info.numParams - nParams
  unless promoted + xs.size == nArgs do
    throwError "internal error: unexpected arguments of a constructor of `{I}`"
  return args.extract nParams info.numParams ++ xs

/-! ### The signature -/

/-- Run `k` on the shape binders `x_s` of the nested arguments `x` of `c`, with binder info
`bi`. -/
def withShapeBinders (c : Ctor) (bi : BinderInfo) (k : Array Expr → TermElabM α) :
    TermElabM α := do
  let rec go (i : Nat) (acc : Array Expr) : TermElabM α := do
    if h : i < c.nests.size then
      let (a, n) := c.nests[i]
      withLocalDecl (a.name.appendAfter "_s") bi (← ctx.ofStructure n.sh) fun s =>
        go (i + 1) (acc.push s)
    else k acc
  go 0 #[]

/-- The universe of `T.Shape`. -/
def shapeLevel : TermElabM Level := do
  let lvls ← ctx.ctors.foldlM (init := #[]) fun acc c =>
    ctx.withShapeBinders c .default fun shs => do
      return acc ++ (← (c.dataArgs.map (·.fvar) ++ shs).mapM fun x => do getLevel (← inferType x))
  return resultLevel lvls

/-- `T.Shape`, in the universe `r` (`shapeLevel`). -/
def genShape (r : Level) : TermElabM Unit := do
  let ty ← mkForallFVars (ctx.params ++ ctx.idx) (mkSort r.succ)
  withLocalDeclD `Shape ty fun Sv => do
  let ctorTys ← ctx.ctors.mapM fun c => ctx.withShapeBinders c .default fun shs =>
    withBinderInfo ctx.params .implicit do
      mkForallFVars (ctx.params ++ c.dataArgs.map (·.fvar) ++ shs) (mkAppN Sv (ctx.params ++ c.idx))
  let us ← ctx.levelParamsOf [] (ctorTys.push ty)
  let Sc := Lean.mkConst ctx.Shape (us.map mkLevelParam)
  addInductive us ctx.params.size [{
    name := ctx.Shape, type := ty
    ctors := (ctx.ctors.zip ctorTys).toList.map fun (c, t) =>
      { name := ctx.shapeCtor c, type := t.replaceFVar Sv Sc } }] ctx.ref

/-- The extra arguments of the position constructor of the recursive argument `a` of `c`, at
the shapes `shs` of the nested arguments: its telescope, or a position of its structure. -/
def withPosArgs (c : Ctor) (a : ArgInfo) (shs : Array Expr) (k : Array Expr → TermElabM α) :
    TermElabM α := do
  match a.kind with
  | .fn n => withTele n a.type fun ys _ => k ys
  | .nest n =>
    let some m := c.nests.findIdx? (·.1.fvar == a.fvar) | unreachable!
    withLocalDeclD `q (mkApp n.pos shs[m]!).headBeta fun q => k #[q]
  | _ => k #[]

/-- The universe of `T.B`, from the arguments of every position constructor. -/
def bLevel : TermElabM Level := do
  let lvls ← ctx.ctors.foldlM (init := #[]) fun acc c =>
    ctx.withShapeBinders c .implicit fun shs =>
      c.recArgs.foldlM (init := acc) fun acc a => withPosArgs c a shs fun ys => do
        let data := c.dataArgs.map (·.fvar)
        return acc ++ (← (data ++ shs ++ ys).mapM fun x => do getLevel (← inferType x))
  return resultLevel lvls

/-- `T.B`, in the universe `r` (`bLevel`). -/
def genB (r : Level) : TermElabM Unit := do
  let data (c : Ctor) := c.dataArgs.map (·.fvar)
  let ty ← withLocalDeclD `s (← ctx.shapeAt ctx.idx) fun s =>
    mkForallFVars (ctx.params ++ ctx.idx |>.push s) (mkSort r.succ)
  withLocalDeclD `B ty fun Bv => do
  let mut ctors := #[]
  for c in ctx.ctors do
    for a in c.recArgs do
      let t ← ctx.withShapeBinders c .implicit fun shs => withPosArgs c a shs fun ys =>
        withBinderInfo (ctx.params ++ data c) .implicit do
          let shape ← ctx.shapeCtorApp c (data c ++ shs)
          mkForallFVars (ctx.params ++ data c ++ shs ++ ys)
            (mkAppN Bv (ctx.params ++ c.idx |>.push shape))
      ctors := ctors.push (ctx.bCtor c a, t)
  let us ← ctx.levelParamsOf [] (ctors.map (·.2) |>.push ty)
  let Bc := Lean.mkConst ctx.B (us.map mkLevelParam)
  addInductive us ctx.params.size [{
    name := ctx.B, type := ty
    ctors := ctors.toList.map fun (n, t) => { name := n, type := t.replaceFVar Bv Bc } }] ctx.ref

/-- The packed index of the position of the recursive argument `a` of `c`, from the arguments
`bargs` of its position constructor (data, shapes, extra). -/
def posIdx (c : Ctor) (a : ArgInfo) (bargs : Array Expr) : MetaM Expr := do
  let nd := c.dataArgs.size
  let ns := c.nests.size
  let σ (e : Expr) := e.replaceFVars (c.dataArgs.map (·.fvar)) (bargs.extract 0 nd)
  let extra := bargs.extract (nd + ns) bargs.size
  match a.kind with
  | .plain idx => ctx.pack (idx.map σ)
  | .fn _ =>
    let mut ty := σ a.type
    for y in extra do
      ty ← whnfR ty
      ty := ty.bindingBody!.instantiate1 y
    let some idx := ctx.holeOf? (← whnfOcc ty)
      | throwError "internal error: no occurrence at the end of{indentExpr ty}"
    ctx.pack idx
  | .nest n =>
    let some m := c.nests.findIdx? (·.1.fvar == a.fvar) | unreachable!
    let some pidx := n.pidx? | throwError "internal error: a nested argument without indices"
    return (mkApp2 (σ pidx) bargs[nd + m]! extra[0]!).headBeta
  | .data => throwError "internal error: a data argument has no position"

/-- `T.idx`, the packed index of a position, by cases. -/
def genIdx : TermElabM Unit := do
  let ixp ← ctx.ixp
  withLocalDecl `s .implicit (← ctx.shapeAt ctx.idx) fun s => do
  withLocalDeclD `b (← ctx.bAt ctx.idx s) fun b => do
  let args := ctx.params ++ ctx.idx |>.push s
  let value ← mkCasesOnApp ctx.B (← ctx.levelsWith ctx.B []) args b (← getLevel ixp)
    (fun _ _ => pure ixp)
    (fun cname xs => do
      let some (c, a) := ctx.ctors.findSome? fun c =>
          (c.recArgs.find? (ctx.bCtor c · == cname)).map (c, ·)
        | throwError "internal error: unexpected constructor {cname}"
      let nargs := c.dataArgs.size + c.nests.size +
        (← ctx.withShapeBinders c .implicit fun shs => withPosArgs c a shs fun ys =>
          pure ys.size)
      ctx.posIdx c a (← ctorArgsOf ctx.B ctx.params.size args xs nargs))
  let xs := ctx.params ++ ctx.idx ++ #[s, b]
  let (type, value) ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    return (← mkForallFVars xs ixp, ← mkLambdaFVars xs value)
  addDef ctx.idxN (← ctx.levelParamsOf [] #[type, value]) type value ctx.ref

/-- By cases on a packed index `p` with `n` components: `motive p` from `k` on the components,
by nested `PSigma.casesOn`, as a `match p with | ⟨i₁, i₂⟩ => …` does; so that the result reduces
on `⟨a, b⟩` to `k #[a, b]`. -/
partial def casesPacked (p : Expr) (n : Nat) (motive : Expr → TermElabM Expr)
    (k : Array Expr → TermElabM Expr) : TermElabM Expr := do
  if n == 0 then return ← k #[]
  if n == 1 then return ← k #[p]
  let ty ← whnf (← inferType p)
  unless ty.isAppOfArity ``PSigma 2 do
    throwError "internal error: expected a dependent pair, got{indentExpr ty}"
  let α := ty.appFn!.appArg!
  let β := ty.appArg!
  let mot ← withLocalDeclD `p ty fun q => do mkLambdaFVars #[q] (← motive q)
  let minor ← withLocalDeclD `a α fun a => withLocalDeclD `b (mkApp β a).headBeta fun b => do
    let mk ← mkAppOptM ``PSigma.mk #[α, β, a]
    mkLambdaFVars #[a, b]
      (← casesPacked b (n - 1) (fun b' => motive (mkApp mk b')) fun rest => k (#[a] ++ rest))
  mkAppOptM ``PSigma.casesOn #[α, β, mot, p, minor]

/-- `T.Ix` and `T.ShapeP`, for several indices. -/
def genIx (rShape : Level) : TermElabM Unit := do
  let ty ← mkForallFVars ctx.params (mkSort ctx.Jlvl.succ)
  let value ← mkLambdaFVars ctx.params ctx.J
  addDef ctx.Ix (← ctx.levelParamsOf [] #[ty, value]) ty value ctx.ref (reducible := true)
  withLocalDeclD `p (← ctx.ixp) fun p => do
    let ty ← mkForallFVars (ctx.params.push p) (mkSort rShape.succ)
    let value ← casesPacked p ctx.k (fun _ => pure (mkSort rShape.succ)) fun is => ctx.shapeAt is
    let value ← mkLambdaFVars (ctx.params.push p) value
    addDef ctx.ShapeP (← ctx.levelParamsOf [] #[ty, value]) ty value ctx.ref

/-- `T.sig`. With several indices, its positions and their index go by cases on the packed
index (`casesPacked`). -/
def genSig (rShape rB : Level) : TermElabM Unit := do
  let ixp ← ctx.ixp
  let shapeFn ← match ctx.k with
    | 0 => withLocalDeclD `i ixp fun i => do mkLambdaFVars #[i] (← ctx.shapeAt #[])
    | 1 => ctx.shapeAt #[]
    | _ => pure (mkAppN (← ctx.constWith ctx.ShapeP []) ctx.params)
  let shapeOf (p : Expr) := (mkApp shapeFn p).headBeta
  -- `fun s => T.B params idx s`, at the components of `p`.
  let bAt' (p : Expr) : TermElabM Expr :=
    casesPacked p ctx.k (fun p => do mkArrow (shapeOf p) (mkSort rB.succ)) fun is => do
      withLocalDeclD `s (← ctx.shapeAt is) fun s => do mkLambdaFVars #[s] (← ctx.bAt is s)
  let bFn ← withLocalDeclD `p ixp fun p => do
    withLocalDeclD `s (shapeOf p) fun s => do
      mkLambdaFVars #[p, s] (mkApp (← bAt' p) s).headBeta
  let idxFn ← withLocalDecl `p .implicit ixp fun p => do
    withLocalDecl `s .implicit (shapeOf p) fun s => do
    withLocalDeclD `b (mkApp2 bFn p s).headBeta fun b => do
      let v ← if !ctx.idxed then pure (Lean.mkConst ``Unit.unit) else do
        let f ← casesPacked p ctx.k
          (fun p => withLocalDeclD `s (shapeOf p) fun s => do
            mkForallFVars #[s] (← mkArrow (mkApp2 bFn p s).headBeta ixp))
          fun is => do
            withLocalDeclD `s (← ctx.shapeAt is) fun s => do
            withLocalDeclD `b (← ctx.bAt is s) fun b => do
              mkLambdaFVars #[s, b] (← ctx.idxAt is s b)
        pure (mkApp2 f s b).headBeta
      mkLambdaFVars #[p, s, b] v
  let value := mkApp4 (.const ``Codata.Signature.mk [ctx.Jlvl, rShape, rB]) ixp shapeFn bFn idxFn
  let ty := Lean.mkConst ``Codata.Signature [ctx.Jlvl, rShape, rB]
  let type ← mkForallFVars ctx.params ty
  let value ← mkLambdaFVars ctx.params value
  addDef ctx.sig (← ctx.levelParamsOf [] #[type, value]) type value ctx.ref (reducible := true)

/-- The model's universe at the universes `rShape` of the shapes and `rB` of the positions: the
largest of these and the packed index's. -/
def modelLevelAt (rShape rB : Level) : Level :=
  (mkLevelMax' (mkLevelMax' ctx.Jlvl rShape) rB).normalize

/-- The universe `L` of the types, `Type L`, before anything is declared: the model's (`tLvl`,
once `T.sig` is declared). -/
def modelLevel : TermElabM Level := do
  return ctx.modelLevelAt (← ctx.shapeLevel) (← ctx.bLevel)

/-- Step 2, the signature. The model's universe, `tLvl` once `T.sig` is declared, must be the
one the constructors fixed, if they did: checked before the signature is declared. What is
declared before it (`T.F`, `T.F.map`, and for `codatatype` `T.F.Rel`) is rolled back with the rest
when the command fails (`allOrNothing`). -/
def genSignature : TermElabM Unit := do
  let rShape ← ctx.shapeLevel
  let rB ← ctx.bLevel
  if let some l := ctx.fixedLvl? then
    let L := ctx.modelLevelAt rShape rB
    unless ← isLevelDefEq L l do
      throwError "the constructors fix the universe of `{ctx.name}` to `{l}`, through a type \
        constructor at one universe, but its model lives in `{L}`"
  ctx.genShape rShape
  ctx.genB rB
  if ctx.k ≥ 2 then ctx.genIx rShape
  if ctx.idxed then ctx.genIdx
  ctx.genSig rShape rB

end Ctx

end Codata.Gen
