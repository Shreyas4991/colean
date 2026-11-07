import Colean.Model.Occ
import Colean.Model.Intype

/-!
# The command, analysis

*Spec.* Input: the syntax of a `codata`/`data` declaration (or the declarations of a block).
Output: the context `Ctx`, everything the generators need: the constructors analysed into
binder groups with their kinds (`Kind`: data, plain recursive, under a telescope, nested with
its occurrence structure `OccInfo`), the index telescope, and the names of every generated
declaration. The occurrence structure of a nested argument is built here by recursion on the
syntax of its type (`occTreeOf`, `occTermOf`), with instance search only at named type
constructors, which must have `PolyIso` and `PolyMap` instances (`checkLeaf`); this is the only
place the command elaborates terms during the analysis. No declaration is generated here except
through `mkCtx`'s callers.
-/

open Lean Elab Command Lean.Parser.Term

namespace Codata

/-- A constructor of a `codata` declaration: a name, binders `(x y : A)` or `{x y : A}`, and
optionally its result type `T params idx`. -/
syntax codataCtor := "| " ident (ppSpace bracketedBinder)* (" : " term)?

/-- `codata T (params) [: (i₁ : I₁) → I₂ → Type u] | ctor₁ … | ctor₂ …` declares a coinductive
type, or family, as a subtype of `Raw`. -/
syntax (name := codataCmd) "codata " ident (ppSpace bracketedBinder)* (" : " term)?
  codataCtor* : command

/-- `data T (params) [: (i₁ : I₁) → I₂ → Type u] | ctor₁ … | ctor₂ …` declares an inductive
type, or family, as a subtype of `Raw`. -/
syntax (name := dataCmd) "data " ident (ppSpace bracketedBinder)* (" : " term)?
  codataCtor* : command

/-- The occurrence tree of an argument type: how the occurrences of a *hole* (the types being
defined) sit in it. Built by `occTreeOf` by recursion on the syntax
of the type, and turned into a structure term by `occTermOf` (`Occ.lean`). -/
inductive OccTree where
  | const (ty : Term)
  /-- An occurrence, with its index arguments. -/
  | hole (idx : Array Term)
  | prod (l r : OccTree)
  | sum (l r : OccTree)
  /-- `(a : A) → body`, with `A` constant (`isProp` when `A` is a proposition). -/
  | pi (a : Ident) (A : Term) (isProp : Bool) (body : OccTree)
  /-- `(a : A) × body`, with `A` constant. -/
  | sigma (a : Ident) (A : Term) (body : OccTree)
  /-- `G arg` for a named type constructor `G` (a lambda over the hole-containing argument, or a
  partial application) with its structure `occ`, from its `PolyIso` instance. -/
  | leaf (G : Term) (occ : Term) (arg : OccTree)
  /-- `G (fun p => arg)` for a named functor of families `G`, with its structure `occ`, from its
  `IPolyIso` instance. -/
  | ileaf (G : Term) (occ : Term) (p : Ident) (arg : OccTree)
  deriving Inhabited

def OccTree.isHole : OccTree → Bool
  | .hole _ => true
  | _ => false

/-- A nested argument's structure: its tree, the structure term `o` (an `Occ`, or an `IOcc`
when `indexed`, whose positions carry their index), its shapes and positions (a function term),
and, when not indexed, the fixed full index of its occurrences. -/
structure OccInfo where
  tree : OccTree
  o : Term
  Sh : Term
  Pos : Term
  indexed : Bool
  /-- The positions' indices, a function term, when `indexed`. -/
  pidx : Term
  idx : Array Term := #[]
  deriving Inhabited

/-- The kind of a constructor argument: non-recursive data, a plain recursive argument, a
recursive argument under a function type with the given domain, or a nested one; recursive
arguments carry the index arguments of their type (none without indices). -/
inductive Kind where
  | data
  | pos (idx : Array Term)
  /-- A recursive argument under a telescope, `(y₁ : B₁) → … → (yₙ : Bₙ) → T params idx`, where
  the index may mention the `yⱼ` (fresh names when an arrow is not dependent). -/
  | fn (tele : Array (Ident × Term)) (idx : Array Term)
  /-- A nested recursive argument: any other type mentioning the types being defined, through
  its occurrence structure (`List (T params idx)`, `T i × T j`, `A → List (T i)`, …). -/
  | occ (info : OccInfo)

/-- A binder group of a constructor. -/
structure Group where
  ids : Array Ident
  ty : Term
  kind : Kind
  implicit : Bool

/-- A constructor, analysed: its name, binder groups, and the index arguments of its result type
(none without indices; in a mutual block, one term of `Blk.Ix`, and the user's `uidx`).
-/
structure CtorInfo where
  name : Ident
  groups : Array Group
  idx : Array Term
  /-- The index arguments as the user wrote them. Outside mutual blocks, the same as `idx`. -/
  uidx : Array Term
  /-- The position of the type it belongs to in the block (`0` outside mutual blocks). -/
  owner : Nat
  /-- Its name in the block-level inductives `F`, `Shape`, `B`: the name itself, or `T_name`
  when another type of the block has a constructor of the same name. -/
  fname : Ident

def idT (x : Ident) : Term := ⟨x.raw⟩

def Kind.isData : Kind → Bool
  | .data => true
  | _ => false

def Kind.idx : Kind → Array Term
  | .data => #[]
  | .pos idx => idx
  | .fn _ idx => idx
  | .occ info => info.idx

def Kind.isOcc : Kind → Bool
  | .occ .. => true
  | _ => false

/-- A nested occurrence whose positions carry their index. -/
def Kind.isFam : Kind → Bool
  | .occ info => info.indexed
  | _ => false

/-- `Codata.Occ.n` or `Codata.IOcc.n`. -/
def occId (indexed : Bool) (n : Name) : Ident :=
  mkIdent ((if indexed then `Codata.IOcc else `Codata.Occ) ++ n)

/-- The identifiers of the explicit arguments, in order: what the constructor is applied to. -/
def CtorInfo.args (c : CtorInfo) : Array Ident :=
  c.groups.foldl (fun acc g => if g.implicit then acc else acc ++ g.ids) #[]

/-- The identifiers of the explicit non-recursive arguments: what the shape is applied to. -/
def CtorInfo.dataArgs (c : CtorInfo) : Array Ident :=
  c.groups.foldl (fun acc g => if g.implicit || !g.kind.isData then acc else acc ++ g.ids) #[]

/-- All binder identifiers, implicit ones included, in order. -/
def CtorInfo.allIds (c : CtorInfo) : Array Ident := c.groups.foldl (fun acc g => acc ++ g.ids) #[]

/-- All non-recursive binder identifiers, implicit ones included. -/
def CtorInfo.allDataIds (c : CtorInfo) : Array Ident :=
  c.groups.foldl (fun acc g => if g.kind.isData then acc ++ g.ids else acc) #[]

def CtorInfo.hasRec (c : CtorInfo) : Bool := c.groups.any fun g => !g.kind.isData

def CtorInfo.hasImplicit (c : CtorInfo) : Bool := c.groups.any (·.implicit)

/-- Does `stx` contain one of the identifiers `ids`? -/
partial def mentionsAny (stx : Syntax) (ids : Array Name) : Bool :=
  match stx with
  | .ident _ _ n _ => ids.contains n.eraseMacroScopes
  | .node _ _ args => args.any (mentionsAny · ids)
  | _ => false

/-- Substitute identifiers by terms. -/
partial def substTerms (stx : Syntax) (f : Name → Option Term) : Syntax :=
  match stx with
  | .ident _ _ n _ =>
    match f n with
    | some t => t.raw
    | none => stx
  | .node info k args => .node info k (args.map (substTerms · f))
  | _ => stx

/-- Substitute identifiers (without macro scopes, i.e. written by the user) by identifiers. -/
partial def substIds (stx : Syntax) (f : Name → Option Ident) : Syntax :=
  match stx with
  | .ident _ _ n _ =>
    if n.hasMacroScopes then stx else
      match f n with
      | some x => x.raw
      | none => stx
  | .node info k args => .node info k (args.map (substIds · f))
  | _ => stx

/-- Does the index of the result type depend on the constructor's own arguments? -/
def CtorInfo.idxDependent (c : CtorInfo) : Bool :=
  let names := c.groups.foldl (fun acc g => acc ++ g.ids.map (·.getId)) #[]
  c.idx.any fun t => mentionsAny t.raw names

/-- Does the type of a binder depend on an earlier binder? -/
def CtorInfo.dependent (c : CtorInfo) : Bool :=
  (c.groups.foldl (fun (acc : Array Name × Bool) g =>
    (acc.1 ++ g.ids.map (·.getId), acc.2 || mentionsAny g.ty.raw acc.1)) (#[], false)).2

/-- Syntactic equality of index arguments. -/
def idxEq (a b : Array Term) : Bool :=
  a.size == b.size && (a.zip b).all fun (x, y) => x.raw.structEq y.raw

/-- `f` applied to `args`, or just `f` when there are none. -/
def appT (f : Term) (args : Array Term) : CommandElabM Term :=
  if args.isEmpty then pure f else `($f $args*)

def mkAppT (f : Ident) (args : Array Term) : CommandElabM Term := appT (idT f) args

/-- If `ty` is one of the types `T p₁ … pₙ idx…` being defined, applied to its parameters: its
position in the block and its index arguments. -/
def recIdx (tNames : Array Name) (params : Array Ident) (ty : Term) :
    Option (Nat × Array Term) :=
  match ty with
  | `($f:ident $as:term*) =>
    match tNames.findIdx? (· == f.getId) with
    | some m =>
      if as.size ≥ params.size &&
          (params.zip as).all (fun (p, a) => a.raw.isIdent && a.raw.getId == p.getId) then
        some (m, as.extract params.size as.size)
      else none
    | none => none
  | `($f:ident) =>
    match tNames.findIdx? (· == f.getId) with
    | some m => if params.isEmpty then some (m, #[]) else none
    | none => none
  | _ => none

/-- A recursive occurrence with its full index: one of the types `T params idx…` (its indices
turned into the block's by `wrap`), or the block family itself `Blk params idx`, in a mutual
block. -/
def recOcc (tNames : Array Name) (blk : Name) (wrap : Nat → Array Term → Array Term)
    (params : Array Ident) (ty : Term) : Option (Array Term) :=
  match recIdx tNames params ty with
  | some (m, idx) => some (wrap m idx)
  | none => (recIdx #[blk] params ty).map (·.2)

/-- In a mutual block: every occurrence of a type of the block in `stx` has the number of indices
of that type, `arity`. The block index is built from them, so a wrong number has to be caught
before it is. -/
partial def checkArity (tNames : Array Name) (params : Array Ident) (arity : Nat → Nat)
    (stx : Syntax) : CommandElabM Unit := do
  if let some (m, idx) := recIdx tNames params ⟨stx⟩ then
    unless idx.size == arity m do
      throwErrorAt stx "recursive argument with the wrong number of indices"
    return
  match stx with
  | .node _ _ args => args.forM (checkArity tNames params arity)
  | _ => pure ()

/-- A binder `(x y : A)` or `{x y : A}`: its names, type, and whether it is implicit. -/
def readBinder (b : TSyntax ``bracketedBinder) : CommandElabM (Array Ident × Term × Bool) := do
  let toIdents (ids : TSyntaxArray [`ident, ``Parser.Term.hole]) : CommandElabM (Array Ident) := do
    unless ids.all (·.raw.isIdent) do throwErrorAt b "binders must be named"
    return ids.map fun x => ⟨x.raw⟩
  match b with
  | `(bracketedBinderF| ($ids* : $ty)) => return (← toIdents ids, ty, false)
  | `(bracketedBinderF| {$ids* : $ty}) => return (← toIdents ids, ty, true)
  | _ => throwErrorAt b "unsupported binder: expected an explicit or implicit binder with a type"

/-- A fresh hygienic identifier. -/
def freshId (s : String) : CommandElabM Ident :=
  return mkIdent (← MonadQuotation.addMacroScope (Name.mkSimple s))

/-- `t`, without its parentheses. -/
def stripParen (t : Term) : Term :=
  match t with
  | `(($t')) => t'
  | _ => t

/-- Does `stx` elaborate in the scope, instances included? -/
private def elaborates (scope : Array (TSyntax ``bracketedBinderF)) (stx : Term) :
    CommandElabM Bool :=
  liftTermElabM do
    Term.elabBinders scope fun _ => Term.withoutErrToSorry do
      try
        discard <| Term.elabTerm stx none
        Term.synthesizeSyntheticMVarsNoPostponing
        return true
      catch _ => return false

/-- The structure of a leaf: a named type constructor `G`, as a lambda over the hole-containing
argument (or a partial application), with `PolyIso` and `PolyMap` instances in the scope
(`IPolyIso` and `IPolyMap` for a family argument). The instances are the user's interface
(`PolyIso.lean`); `PolyMap` is not used by the generated declarations, it is required because it
is what makes the map they use the intended one. -/
private def checkLeaf (scope : Array (TSyntax ``bracketedBinderF)) (ty G : Term) (fam : Bool) :
    CommandElabM Term := do
  let occ ← if fam then `(Codata.IOcc.ofIso $G) else `(Codata.Occ.ofIso $G)
  let iso := if fam then "IPolyIso" else "PolyIso"
  let mapName := if fam then "IPolyMap" else "PolyMap"
  unless ← elaborates scope occ do
    throwErrorAt ty "no `Codata.{iso}` instance for `{G}`; to nest through a type constructor, \
      give it `Codata.{iso}` and `Codata.{mapName}` instances (`Colean/PolyIso.lean`); products, \
      sums, functions and dependent pairs over constant types need none"
  let map ← if fam then `((inferInstance : Codata.IPolyMap $G $G))
    else `((inferInstance : Codata.PolyMap $G $G))
  unless ← elaborates scope map do
    throwErrorAt ty "no `Codata.{mapName}` instance for `{G}`: the `Codata.{iso}` instance needs \
      the intended action on functions, and its naturality"
  return occ

/-- The shapes, positions and (indexed) position index of a structure term, from its type,
elaborated in the scope. -/
def occShapes (scope : Array (TSyntax ``bracketedBinderF)) (O : Term) (indexed : Bool) :
    CommandElabM (Term × Term × Option Term) :=
  liftTermElabM do
    Term.elabBinders scope fun _ => Term.withoutErrToSorry do
      let e ← Term.elabTerm O none
      Term.synthesizeSyntheticMVarsNoPostponing
      let ty ← Meta.whnfR (← instantiateMVars (← Meta.inferType e))
      let args := ty.getAppArgs
      if indexed then
        unless ty.isAppOfArity ``Codata.IOcc 5 do throwError "unexpected structure type: {ty}"
        return (← PrettyPrinter.delab args[1]!, ← PrettyPrinter.delab args[2]!,
          some (← PrettyPrinter.delab args[3]!))
      unless ty.isAppOfArity ``Codata.Occ 3 do throwError "unexpected structure type: {ty}"
      return (← PrettyPrinter.delab args[0]!, ← PrettyPrinter.delab args[1]!, none)

/-- Is `ty` a proposition, in the scope? -/
def isPropTy (scope : Array (TSyntax ``bracketedBinderF)) (ty : Term) : CommandElabM Bool :=
  liftTermElabM do
    Term.elabBinders scope fun _ => Term.withoutErrToSorry do
      let e ← Term.elabType ty
      Term.synthesizeSyntheticMVarsNoPostponing
      Meta.isProp e

/-- `stx` with every hole replaced by `X`. -/
partial def replaceHoles (holeOf : Term → Option (Array Term)) (X : Ident) (stx : Syntax) :
    CommandElabM Syntax := do
  if (holeOf ⟨stx⟩).isSome then return X.raw
  match stx with
  | .node info k args => return .node info k (← args.mapM (replaceHoles holeOf X))
  | _ => return stx

/-- The indices of the holes of `stx`. -/
partial def collectHoles (holeOf : Term → Option (Array Term)) (stx : Syntax) :
    Array (Array Term) :=
  match holeOf ⟨stx⟩ with
  | some idx => #[idx]
  | none => match stx with
    | .node _ _ args => args.foldl (fun acc a => acc ++ collectHoles holeOf a) #[]
    | _ => #[]

/-- The occurrence tree of `ty`, for the hole recognised by `holeOf` (an occurrence with its
index arguments) among the names `names`: products, sums, functions and dependent pairs over
constant types, and named type constructors applied to one hole-containing argument (a family
`fun p => …` for a functor of families), whose structures come from their `PolyIso` instances.
-/
partial def occTreeOf (holeOf : Term → Option (Array Term)) (names : Array Name)
    (scope : Array (TSyntax ``bracketedBinderF)) (ty : Term) : CommandElabM OccTree := do
  let ty := stripParen ty
  if let some idx := holeOf ty then return .hole idx
  unless mentionsAny ty.raw names do return .const ty
  let go := occTreeOf holeOf names scope
  let noDom (dom : Term) : CommandElabM Unit := do
    if mentionsAny dom.raw names then
      throwErrorAt dom "the types being defined may not occur in the domain of a function"
  -- Under a binder, the scope grows.
  let under (a : Ident) (A : Term) (t : Term) : CommandElabM OccTree := do
    occTreeOf holeOf names (scope.push (← `(bracketedBinderF| ($a:ident : $A)))) t
  match ty with
  | `(($a:ident : $A) × $body) =>
    noDom A
    return .sigma a A (← under a A body)
  | `($l × $r) => return .prod (← go l) (← go r)
  | `($l ⊕ $r) => return .sum (← go l) (← go r)
  | `($b:bracketedBinder → $cod) =>
    let (ids, dom, _) ← readBinder b
    noDom dom
    let isProp ← isPropTy scope dom
    let mut scope' := scope
    for a in ids do
      scope' := scope'.push (← `(bracketedBinderF| ($a:ident : $dom)))
    let body ← occTreeOf holeOf names scope' cod
    return ids.foldr (fun a acc => .pi a dom isProp acc) body
  | `($dom → $cod) =>
    noDom dom
    return .pi (← freshId "y") dom (← isPropTy scope dom) (← go cod)
  | `($f:ident $args:term*) =>
    if mentionsAny f.raw names then
      throwErrorAt ty "recursive occurrence not recognised: a type being defined must be \
        applied to its parameters (and indices)"
    let ks := (Array.range args.size).filter fun k => mentionsAny args[k]!.raw names
    -- Several arguments: the whole type as a functor of the hole, at one index.
    if ks.size ≥ 2 then
      let X ← freshId "X"
      let body ← replaceHoles holeOf X ty.raw
      let found := collectHoles holeOf ty.raw
      let some idx := found[0]? | throwErrorAt ty "recursive occurrence not recognised"
      unless found.all (idxEq idx) do
        throwErrorAt ty "the types being defined occur at different indices in several arguments \
          of `{f}`, which is supported only for products, sums, functions and dependent pairs"
      if mentionsAny body names then
        throwErrorAt ty "recursive occurrence not recognised: a type being defined must be \
          applied to its parameters (and indices)"
      let G ← `(fun $X:ident => $(⟨body⟩))
      return .leaf G (← checkLeaf scope ty G false) (.hole idx)
    let k := ks[0]!
    let arg := stripParen args[k]!
    let X ← freshId "X"
    -- The leaf as a functor of the argument: a partial application when the argument is last,
    -- a lambda otherwise.
    let G ← if k == args.size - 1 then
        (if k == 0 then pure (idT f) else `($f $(args.extract 0 k)*))
      else `(fun $X:ident => $f $(args.set! k (idT X))*)
    let famBody? : Option (Ident × Term) := match arg with
      | `(fun $p:ident => $body) => some (p, body)
      | `(fun ($p:ident : $_) => $body) => some (p, body)
      | _ => none
    match famBody? with
    | some (p, body) =>
      return .ileaf G (← checkLeaf scope ty G true) p (← go body)
    | none =>
      return .leaf G (← checkLeaf scope ty G false) (← go arg)
  | _ =>
    throwErrorAt ty "recursive occurrence not recognised: expected a type being defined \
      applied to its parameters (and indices), possibly under arrows, products, sums, \
      dependent pairs or type constructors with an occurrence structure"

/-- The structure term of a tree: an `Occ`, or an `IOcc` over `J` when `indexed`, with the
holes' indices packed by `packIdx`. A leaf at a hole is the leaf's own structure (at a fixed
index, or reindexed along the family variable). -/
partial def occTermOf (indexed : Bool) (J : Term) (packIdx : Array Term → CommandElabM Term) :
    OccTree → CommandElabM Term
  | .const ty =>
    if indexed then `(Codata.IOcc.const (J := $J) $ty) else `(Codata.Occ.const $ty)
  | .hole idx =>
    if indexed then do `(Codata.IOcc.hole (J := $J) $(← packIdx idx)) else `(Codata.Occ.hole)
  | .prod l r => do `($(occId indexed `prod) $(← occTermOf indexed J packIdx l) $(← occTermOf indexed J packIdx r))
  | .sum l r => do `($(occId indexed `sum) $(← occTermOf indexed J packIdx l) $(← occTermOf indexed J packIdx r))
  | .pi a A isProp body => do
    `($(occId indexed (if isProp then `piP else `pi)) $A (fun $a:ident => $(← occTermOf indexed J packIdx body)))
  | .sigma a A body => do
    `($(occId indexed `sigma) $A (fun $a:ident => $(← occTermOf indexed J packIdx body)))
  | .leaf _ occ arg => do
    match arg with
    | .hole idx => if indexed then `(Codata.IOcc.ofOcc $occ $(← packIdx idx)) else pure occ
    | _ =>
      let inner ← occTermOf indexed J packIdx arg
      if indexed then `(Codata.IOcc.compC $occ $inner) else `(Codata.Occ.comp $occ $inner)
  | .ileaf _ occ p arg => do
    match arg with
    | .hole idx =>
      if indexed then
        let pk ← packIdx idx
        -- The family at its own index: the leaf itself.
        if pk.raw.isIdent && pk.raw.getId == p.getId then pure occ
        else `(Codata.IOcc.reidx $occ (fun $p:ident => $pk))
      else `(Codata.Occ.ofI $occ)
    | _ =>
      let inner ← occTermOf indexed J packIdx arg
      `($(occId indexed `compI) $occ (fun $p:ident => $inner))

/-- The type of a tree, with the holes replaced by `mkHole idx`. -/
partial def OccTree.ty (mkHole : Array Term → CommandElabM Term) : OccTree → CommandElabM Term
  | .const t => pure t
  | .hole idx => mkHole idx
  | .prod l r => do `($(← l.ty mkHole) × $(← r.ty mkHole))
  | .sum l r => do `($(← l.ty mkHole) ⊕ $(← r.ty mkHole))
  | .pi a A _ body => do `(($a:ident : $A) → $(← body.ty mkHole))
  | .sigma a A body => do `(($a:ident : $A) × $(← body.ty mkHole))
  | .leaf G _ arg => do
    let arg' ← arg.ty mkHole
    match G with
    | `(fun $X:ident => $body) =>
      pure ⟨substTerms body.raw fun n => if n == X.getId then some arg' else none⟩
    | _ => `($G $arg')
  | .ileaf G _ p arg => do
    let arg' ← arg.ty mkHole
    -- `fun p => X p` is `X`.
    let fam ← match arg' with
      | `($X:ident $q:ident) => if q.getId == p.getId then pure (idT X) else `(fun $p:ident => $arg')
      | _ => `(fun $p:ident => $arg')
    match G with
    | `(fun $X:ident => $body) =>
      pure ⟨substTerms body.raw fun n => if n == X.getId then some fam else none⟩
    | _ => `($G $fam)

/-- The first hole of a tree, if any. -/
partial def OccTree.firstIdx? : OccTree → Option (Array Term)
  | .const _ => none
  | .hole idx => some idx
  | .prod l r | .sum l r => l.firstIdx? <|> r.firstIdx?
  | .pi _ _ _ body | .sigma _ _ body | .leaf _ _ body | .ileaf _ _ _ body => body.firstIdx?

/-- Classify the type of a constructor argument: a plain recursive argument `T params idx`, a
recursive argument under a telescope of arrows ending in one, a nested one (any other type
mentioning the types being defined, through its occurrence structure), or non-recursive data,
which may not mention the types being defined at all. `wrap m` turns the index arguments of the
`m`-th type into those of the block (the identity outside mutual blocks); `blk` is the block
family, which nested occurrences may mention directly. With
indices (`idxed`), the structure of a nested argument is indexed over the packed index type
`Ixp`, the indices packed by `pack`. -/
private partial def classify (tNames : Array Name) (blk : Name) (params : Array Ident)
    (scope : Array (TSyntax ``bracketedBinderF)) (wrap : Nat → Array Term → Array Term)
    (idxed : Bool)
    (Ixp : Term) (pack : Array Term → CommandElabM Term) (ty : Term) : CommandElabM Kind := do
  let names := tNames.push blk
  if let some idx := recOcc tNames blk wrap params ty then return .pos idx
  let rec go (t : Term) (acc : Array (Ident × Term)) : CommandElabM (Option Kind) := do
    match t with
    | `($b:bracketedBinder → $cod) =>
      let (ids, dom, _) ← readBinder b
      go cod (acc ++ ids.map (·, dom))
    | `($dom → $cod) =>
      go cod (acc.push (← freshId s!"y{Nat.toSubscriptString (acc.size + 1)}", dom))
    | _ => return (recOcc tNames blk wrap params t).map fun idx => .fn acc idx
  if let some k ← go ty #[] then
    if let .fn tele _ := k then
      for (_, dom) in tele do
        if mentionsAny dom.raw names then
          throwErrorAt dom "the types being defined may not occur in the domain of a function"
    return k
  unless mentionsAny ty.raw names do return .data
  let tree ← occTreeOf (recOcc tNames blk wrap params) names scope ty
  let o ← occTermOf idxed Ixp pack tree
  let (Sh, Pos, pidx?) ← occShapes scope o idxed
  return .occ { tree, o, Sh, Pos, indexed := idxed, pidx := pidx?.getD Pos }

/-- The binders `(y₁ : B₁) … (yₙ : Bₙ)` of a telescope. -/
def teleBinders (tele : Array (Ident × Term)) : CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  tele.mapM fun (y, B) => `(bracketedBinderF| ($y:ident : $B))

def teleIds (tele : Array (Ident × Term)) : Array Ident := tele.map (·.1)

/-- `(y₁ : B₁) → … → (yₙ : Bₙ) → cod`. -/
def mkPi (tele : Array (Ident × Term)) (cod : Term) : CommandElabM Term :=
  tele.foldrM (init := cod) fun (y, B) acc => `(($y:ident : $B) → $acc)

/-- A binder group as a `bracketedBinder`, explicit or implicit as declared. -/
def mkBinder (implicit : Bool) (ids : Array Ident) (ty : Term) :
    CommandElabM (TSyntax ``bracketedBinderF) :=
  if implicit then `(bracketedBinderF| {$ids* : $ty}) else `(bracketedBinderF| ($ids* : $ty))

/-- The generated declaration `T.s`. Inside its own namespace `T.T` would shadow the type `T`, so
a generated name equal to the type's name is primed (`B.B'` for `codata B`). -/
def genName (tName : Name) (s : String) : Name :=
  .str tName (if tName.getString! == s then s ++ "'" else s)

/-- Everything the generators need: the analysed declaration, the index telescope if any, the
namespaces of the generic theory to instantiate, and the names of the generated declarations
and the types applied to the parameters. -/
structure Ctx where
  /-- `codata` (`true`) or `data`. -/
  co : Bool
  /-- The family being defined: the type itself, or the block `T₁_T₂` of a mutual block. -/
  T : Ident
  tName : Name
  /-- The user-facing types: `#[T]`, or the types of the block, in order. -/
  types : Array Ident
  /-- In a mutual block, the constructors `@Blk.Ix.Tₘ params` of the index of the block, one per
  type. Empty outside mutual blocks. -/
  ixCtors : Array Term
  /-- The user's index binders of every type, and fresh names for a second copy of them. Outside
  mutual blocks, `#[idx]` and `#[jIds]`. -/
  uidx : Array (Array (Ident × Term))
  ujIds : Array (Array Ident)
  pids : Array Ident
  pExp : Array (TSyntax ``bracketedBinderF)
  pImp : Array (TSyntax ``bracketedBinderF)
  pTerms : Array Term
  ctors : Array CtorInfo
  /-- The index binders, with the names the user gave them (or fresh ones) and their types,
  which may mention the earlier names. Empty for a plain type. -/
  idx : Array (Ident × Term)
  /-- Fresh names for a second copy of the index binders (`∀ j₁ j₂, …`). -/
  jIds : Array Ident
  /-- The packed index type, applied to the parameters (`T.Ix params` for several indices, the
  index type itself for one). -/
  Ixp : Term
  /-- The binder names users may refer to (`motive := …`, `S := …`): plain identifiers, unless
  the declaration uses the name itself. -/
  motiveId : Ident
  Sid : Ident
  Ix : Ident
  idxId : Ident
  F : Ident
  Shape : Ident
  /-- The shapes on the packed index (several indices only). -/
  ShapeP : Ident
  B : Ident
  sig : Ident
  Fmap : Ident
  Rel : Ident
  Fmap_id : Ident
  Fmap_comp : Ident
  Frel_map : Ident
  toC : Ident
  ofC : Ident
  ofC_toC : Ident
  ofC_map : Ident
  rel_ofC : Ident
  toC_ofC : Ident
  dtor : Ident
  corec : Ident
  dtor_corec : Ident
  bisim : Ident
  contract : Ident
  ctor : Ident
  dtor_ctor : Ident
  ctor_dtor : Ident
  ctor_injective : Ident
  corec_eq : Ident
  corec_unique : Ident
  casesOnAux : Ident
  casesOnId : Ident
  casesOn_ctor : Ident
  /-- `data` only: the fold, the dependent recursor and their computation rules. -/
  fold : Ident
  fold_ctor : Ident
  fold_eq : Ident
  fold_unique : Ident
  recAux : Ident
  recId : Ident
  rec_ctor : Ident
  Tp : Term
  Fp : Term
  Shapep : Term
  ShapePp : Term
  Bp : Term
  sigp : Term

/-- The short name of the position constructor for the argument `x` of constructor `c`. -/
def posCtorName (c : CtorInfo) (x : Ident) : Ident :=
  mkIdent (Name.mkSimple (c.fname.getId.toString ++ "_" ++ x.getId.toString))

/-- The binders of a constructor, with the user's types. -/
def binders (c : CtorInfo) : CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  c.groups.mapM fun g => mkBinder g.implicit g.ids g.ty

def prime (x : Ident) : Ident := mkIdent (x.getId.appendAfter "'")

/-- The binders of a constructor with primed names, in the types too. -/
def binders' (c : CtorInfo) : CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  let ids := c.allIds.map (·.getId)
  c.groups.mapM fun g =>
    mkBinder g.implicit (g.ids.map prime)
      ⟨substIds g.ty.raw fun n => if ids.contains n then some (prime (mkIdent n)) else none⟩

/-- The binders of a constructor of `F`: recursive types replaced by `X` (at their index). -/
def fBinders (c : CtorInfo) : CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  c.groups.mapM fun g => do
    let ty ← match g.kind with
      | .data => pure g.ty
      | .pos idx => appT (← `(X)) idx
      | .fn tele idx => do mkPi tele (← appT (← `(X)) idx)
      | .occ info => info.tree.ty fun idx => do appT (← `(X)) idx
    mkBinder g.implicit g.ids ty

/-- The shape binder of a nested argument `x`: `x_s`, the shape of its structure. -/
def nestShapeId (x : Ident) : Ident := mkIdent (x.getId.appendAfter "_s")

/-- The nested arguments of a constructor, with their structures. -/
def CtorInfo.nested (c : CtorInfo) : Array (Ident × OccInfo) :=
  c.groups.foldl (init := #[]) fun acc g => match g.kind with
    | .occ info => acc ++ g.ids.map (·, info)
    | _ => acc

/-- The shape binders `(x_s : Sh)` of the nested arguments. -/
def nestShapeBinders (c : CtorInfo) (implicit : Bool) :
    CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  c.nested.mapM fun (x, info) => mkBinder implicit #[nestShapeId x] info.Sh

/-- The data binders of a constructor and the shapes of its nested arguments, all implicit (for
the constructors of `B`, where they are determined by the shape). -/
def dataBindersImplicit (c : CtorInfo) : CommandElabM (Array (TSyntax ``bracketedBinderF)) := do
  return (← (c.groups.filter (·.kind.isData)).mapM fun g => mkBinder true g.ids g.ty) ++
    (← nestShapeBinders c true)

namespace Ctx

variable (ctx : Ctx)

def fCtor (c : CtorInfo) : Ident := mkIdent (ctx.F.getId ++ c.fname.getId)
def shapeCtor (c : CtorInfo) : Ident := mkIdent (ctx.Shape.getId ++ c.fname.getId)
def bCtor (c : CtorInfo) (x : Ident) : Ident := mkIdent (ctx.B.getId ++ (posCtorName c x).getId)

/-! In a mutual block, the user-facing declarations of a constructor live under its own type. -/

/-- The name of the `m`-th type of the block. -/
def tyName (m : Nat) : Name := ctx.types[m]!.getId

/-- `T.s`, for the `m`-th type. -/
def tyId (m : Nat) (s : String) : Ident := mkIdent (.str (ctx.tyName m) s)

def tCtor (c : CtorInfo) : Ident := mkIdent (ctx.tyName c.owner ++ c.name.getId)
def tName' (c : CtorInfo) (pre post : String) : Ident :=
  mkIdent (ctx.tyName c.owner ++ Name.mkSimple (pre ++ c.name.getId.toString ++ post))
def nF (s : String) : Ident := mkIdent (.str (genName ctx.tName "F") s)

def isMutual : Bool := !ctx.ixCtors.isEmpty

/-- `T.s`, for the family being defined. -/
def nm (s : String) : Ident := mkIdent (genName ctx.tName s)

/-- The index arguments of the block for the `m`-th type at the user's arguments `args`: the
constructor of `Blk.Ix` applied to them, or `args` outside mutual blocks. -/
def wrapIdx (m : Nat) (args : Array Term) : Array Term :=
  if ctx.isMutual then #[Syntax.mkApp ctx.ixCtors[m]! args] else args

/-- A declaration of the generic signature theory. -/
def sigId (_ : Ctx) (n : Name) : Ident := mkIdent (`Codata.Signature ++ n)

/-- A declaration derived from the contract. -/
def topId (_ : Ctx) (n : Name) : Ident := mkIdent (`Codata ++ n)

/-- The generic family of the signature: `Cotype sig` or `Intype sig`. -/
def famT : CommandElabM Term :=
  `($(ctx.sigId (if ctx.co then `Cotype else `Intype)) $(ctx.sigp))

/-- The number of indices. -/
def k : Nat := ctx.idx.size

def idxed : Bool := ctx.k > 0

/-- Is the index packed: several indices into a `PSigma`, none into `Unit`? With exactly one
index nothing is packed and the conversions below are the identity. -/
def packed : Bool := ctx.k ≠ 1

def iIds : Array Ident := ctx.idx.map (·.1)
def iArgs : Array Term := ctx.iIds.map idT
def jArgs : Array Term := ctx.jIds.map idT

/-- `_` for every index. -/
def holes : CommandElabM (Array Term) := ctx.idx.mapM fun _ => `(_)

/-- Substitute the index names by the identifiers `names`. -/
def renameTo (names : Array Ident) (t : Term) : Term :=
  ⟨substIds t.raw fun n => (ctx.idx.findIdx? (·.1.getId == n)).map fun m => names[m]!⟩

/-- The index binders, named `names`. -/
def ixBindersWith (names : Array Ident) (implicit : Bool) :
    CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  (Array.range ctx.k).mapM fun m => mkBinder implicit #[names[m]!] (ctx.renameTo names ctx.idx[m]!.2)

/-- The binders `{i₁ : I₁} {i₂ : I₂}`, if indexed. -/
def ixB : CommandElabM (Array (TSyntax ``bracketedBinderF)) := ctx.ixBindersWith ctx.iIds true

/-- The binders `(i₁ : I₁) (i₂ : I₂)`. -/
def ixBExp : CommandElabM (Array (TSyntax ``bracketedBinderF)) := ctx.ixBindersWith ctx.iIds false

/-- The binders `(j₁ : I₁) (j₂ : I₂)`. -/
def jB : CommandElabM (Array (TSyntax ``bracketedBinderF)) := ctx.ixBindersWith ctx.jIds false

/-- The index `i` as arguments, if indexed (kept under the old name). -/
def iArg : Array Term := ctx.iArgs

/-- `t`, or `t i₁ i₂`. -/
def atI (t : Term) : CommandElabM Term := appT t ctx.iArgs

/-- The sort of a family variable: `Type _`, or `∀ j₁ j₂, Type _`. -/
def famTy : CommandElabM Term := do
  let jB ← ctx.jB
  if ctx.idxed then `(∀ $[$jB]*, Type _) else `(Type _)

/-- `X → Y`, or `∀ j₁ j₂, X j₁ j₂ → Y j₁ j₂`. -/
def famFn (X Y : Term) : CommandElabM Term := do
  let jB ← ctx.jB
  let Xj ← appT X ctx.jArgs
  let Yj ← appT Y ctx.jArgs
  if ctx.idxed then `(∀ $[$jB]*, $Xj → $Yj) else `($X → $Y)

/-- `X → Y → Prop`, or `∀ j₁ j₂, X j₁ j₂ → Y j₁ j₂ → Prop`. -/
def famRel (X Y : Term) : CommandElabM Term := do
  let jB ← ctx.jB
  let Xj ← appT X ctx.jArgs
  let Yj ← appT Y ctx.jArgs
  if ctx.idxed then `(∀ $[$jB]*, $Xj → $Yj → Prop) else `($X → $Y → Prop)

/-! Packing the indices into one. With one index, all of these are the identity. -/

/-- `⟨a₁, a₂⟩`, `a₁`, or `()`. -/
def pack (args : Array Term) : CommandElabM Term :=
  if ctx.k == 0 then `(()) else if ctx.k == 1 then pure args[0]! else `(⟨$[$args],*⟩)

/-- The indices `i₁ i₂` packed, with the packed type ascribed. -/
def packI : CommandElabM Term := do `(($(← ctx.pack ctx.iArgs) : $(ctx.Ixp)))

/-- `p.1, p.2.1, p.2.2`, or `p`, or nothing. -/
def projs (p : Term) : CommandElabM (Array Term) := do
  if ctx.k == 0 then return #[]
  if ctx.k == 1 then return #[p]
  let mut out := #[]
  let mut cur := p
  for _ in [0:ctx.k - 1] do
    out := out.push (← `(PSigma.fst $cur))
    cur ← `(PSigma.snd $cur)
  return out.push cur

/-- `fun j₁ j₂ => X ⟨j₁, j₂⟩`, or `X`, or `X ()`: a family on the packed index, curried. -/
def curryFam (X : Term) : CommandElabM Term := do
  if ctx.k == 0 then return ← `($X ())
  if !ctx.packed then return X
  let js := ctx.jIds
  `(fun $[$js:ident]* => $(← appT X #[← ctx.pack ctx.jArgs]))

/-- `fun p => X p.1 p.2`, or `X`: a curried family, on the packed index. -/
def packFam (X : Term) : CommandElabM Term := do
  if !ctx.packed then return X
  `(fun (p : $(ctx.Ixp)) => $(← appT X (← ctx.projs (← `(p)))))

/-- `fun j₁ j₂ e… => f ⟨j₁, j₂⟩ e…`, or `f`, or `fun e… => f () e…`. -/
def curryN (f : Term) (extra : Array Ident) : CommandElabM Term := do
  if !ctx.packed then return f
  if ctx.k == 0 && extra.isEmpty then return ← `($f ())
  let bs := ctx.jIds ++ extra
  `(fun $[$bs:ident]* => $(← appT f (#[← ctx.pack ctx.jArgs] ++ extra.map idT)))

/-- `fun p e… => c p.1 p.2 e…`, or `c`. -/
def uncurryN (c : Term) (extra : Array Ident) : CommandElabM Term := do
  if !ctx.packed then return c
  `(fun (p : $(ctx.Ixp)) $[$extra:ident]* => $(← appT c ((← ctx.projs (← `(p))) ++ extra.map idT)))

/-! Constructor applications are generated with all arguments explicit (`@F.c params X …`),
patterns likewise with `_` for the parameters: with propositions as indices, an implicit proof
argument cannot be inferred by unification, since any two proofs are definitionally equal. -/

/-- `_` for every parameter. -/
def pHoles : CommandElabM (Array Term) := ctx.pids.mapM fun _ => `(_)

/-- If the constructor's binder `x` is one of the indices of its result type, that index
binder. In a `match` whose discriminant has the index binders as indices, the pattern variable
`x` is eliminated in favour of the index binder, so right-hand sides refer to the latter. -/
def bareIdx (c : CtorInfo) (x : Name) : Option Ident :=
  if c.allDataIds.any (·.getId == x) then
    (c.idx.findIdx? fun t => t.raw.isIdent && t.raw.getId == x).map fun m => ctx.iIds[m]!
  else none

/-- Substitute the binders that are indices by the index binders. -/
def substBare (c : CtorInfo) (t : Term) : Term := ⟨substIds t.raw (ctx.bareIdx c)⟩

/-- The constructor's binders as values in a right-hand side after a `match`: the index binders
for those that are indices. -/
def valIds (c : CtorInfo) : Array Ident :=
  c.allIds.map fun x => (ctx.bareIdx c x.getId).getD x

def valDataIds (c : CtorInfo) : Array Ident :=
  c.allDataIds.map fun x => (ctx.bareIdx c x.getId).getD x

def valArgs (c : CtorInfo) : Array Ident :=
  c.args.map fun x => (ctx.bareIdx c x.getId).getD x

/-- The index binders as discriminant patterns for a constructor: the index binder itself where
the constructor's index is one of its binders, at the binder's first occurrence (the binder is
then a hole, and right-hand sides use the index binder), `_` where it is another term or a
repeated binder. Generated `match`es take the index binders as explicit discriminants so that
the generator, not Lean, decides what is generalised and named: a hole is always assigned to
the older, named pattern variable, which is what makes right-hand sides well-typed. -/
def idxPats (c : CtorInfo) : CommandElabM (Array Term) :=
  (Array.range ctx.k).mapM fun m => do
    let t := c.idx[m]!
    let bare := t.raw.isIdent && c.allDataIds.any (·.getId == t.raw.getId)
    if bare && (c.idx.findIdx? fun t' => t'.raw.isIdent && t'.raw.getId == t.raw.getId) == some m
    then pure (idT ctx.iIds[m]!) else `(_)

/-- `i₁, i₂, x`: the discriminants of a `match` on `x` whose type has the index binders as
indices. -/
def discrs (x : Term) : Array Term := ctx.iArgs.push x

/-- A `match` alternative `| i₁, _, pats… => rhs` for the constructor `c`. -/
def alt (c : CtorInfo) (pats : Array Term) (rhs : Term) : CommandElabM (TSyntax ``matchAlt) := do
  let pats := (← ctx.idxPats c) ++ pats
  `(matchAltExpr| | $[$pats:term],* => $rhs:term)

/-! The user's indices, type by type: what the per-type declarations of a mutual block (the
types, `casesOn`, the aliases) are stated with. Outside mutual blocks these coincide with the
helpers above. -/

def uIArgs (m : Nat) : Array Term := ctx.uidx[m]!.map (idT ·.1)
def uJArgs (m : Nat) : Array Term := ctx.ujIds[m]!.map idT

/-- Does the `m`-th type have indices? -/
def uIdxed (m : Nat) : Bool := !ctx.uidx[m]!.isEmpty

/-- The index binders of the `m`-th type, named `names`. -/
def uIxBindersWith (m : Nat) (names : Array Ident) (implicit : Bool) :
    CommandElabM (Array (TSyntax ``bracketedBinderF)) := do
  let tele := ctx.uidx[m]!
  let rename (t : Term) : Term :=
    ⟨substIds t.raw fun n => (tele.findIdx? (·.1.getId == n)).map fun i => names[i]!⟩
  (Array.range tele.size).mapM fun i => mkBinder implicit #[names[i]!] (rename tele[i]!.2)

def uIxB (m : Nat) : CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  ctx.uIxBindersWith m (ctx.uidx[m]!.map (·.1)) true
def uIxBExp (m : Nat) : CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  ctx.uIxBindersWith m (ctx.uidx[m]!.map (·.1)) false
def uJB (m : Nat) : CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  ctx.uIxBindersWith m ctx.ujIds[m]! false

/-- The `m`-th user-facing type applied to the parameters. -/
def tyP (m : Nat) : CommandElabM Term :=
  if ctx.isMutual then mkAppT ctx.types[m]! ctx.pTerms else pure ctx.Tp

/-- `Tₘ params i…`, at the user's index binders. -/
def tyAtU (m : Nat) : CommandElabM Term := do appT (← ctx.tyP m) (ctx.uIArgs m)

/-- The user-facing type of a constructor's result, `Tₘ params idx…`. -/
def tyAt (c : CtorInfo) : CommandElabM Term := do appT (← ctx.tyP c.owner) c.uidx

/-- The index arguments of the block for the `m`-th type at the user's index binders. -/
def fullArgs (m : Nat) : Array Term := ctx.wrapIdx m (ctx.uIArgs m)

/-- The patterns for the user's indices. In a mutual block they are holes: the constructor's
binders are named in its pattern, and its index is reached through the block's. -/
def uIdxPats (c : CtorInfo) : CommandElabM (Array Term) :=
  if ctx.isMutual then c.uidx.mapM fun _ => `(_) else ctx.idxPats c

def uDiscrs (m : Nat) (x : Term) : Array Term := (ctx.uIArgs m).push x

def uAlt (c : CtorInfo) (pats : Array Term) (rhs : Term) : CommandElabM (TSyntax ``matchAlt) := do
  let pats := (← ctx.uIdxPats c) ++ pats
  `(matchAltExpr| | $[$pats:term],* => $rhs:term)

/-- `@F.c params X args…`. -/
def fApp (c : CtorInfo) (X : Term) (args : Array Term) : CommandElabM Term := do
  let pTerms := ctx.pTerms
  `(@$(ctx.fCtor c):ident $pTerms* $X $args*)

/-- Binders as pattern variables: `_` for those that are indices, which the pattern elaborator
would refuse to name (their value is forced by the discriminant's type). -/
def patIds (c : CtorInfo) (ids : Array Ident) : CommandElabM (Array Term) :=
  ids.mapM fun x => if (ctx.bareIdx c x.getId).isSome then `(_) else pure (idT x)

/-- The pattern `@F.c _ _ x₁ x₂ …` binding all arguments. -/
def fPat (c : CtorInfo) : CommandElabM Term := do
  let hs ← ctx.pHoles
  let ids ← ctx.patIds c c.allIds
  `(@$(ctx.fCtor c):ident $hs* _ $ids*)

/-- `@T.c params x₁ x₂ …`. -/
def tApp (c : CtorInfo) : CommandElabM Term := do
  let pTerms := ctx.pTerms
  let ids := c.allIds.map idT
  `(@$(ctx.tCtor c):ident $pTerms* $ids*)

/-- The structure of a nested argument, after a `match` (index binders for the binders that
are indices) or with the constructor's binders in scope. -/
def occOf (c : CtorInfo) (info : OccInfo) (afterMatch : Bool) : Term :=
  if afterMatch then ctx.substBare c info.o else info.o

/-- The packed index of the position `q` of the nested argument with structure `info` at the
shape `xs`: its fixed index, or the index its structure gives it. -/
def occIdxAt (c : CtorInfo) (info : OccInfo) (xs q : Term) : CommandElabM Term := do
  if info.indexed then `($(ctx.substBare c info.pidx) $xs $q)
  else ctx.pack (info.idx.map (ctx.substBare c))

/-- The shapes of the nested arguments, as values: `(Occ.toC o x).1` (after a `match`). -/
def nestShapeVals (c : CtorInfo) : CommandElabM (Array Term) :=
  c.nested.mapM fun (x, info) =>
    `(($(occId info.indexed `toC) $(ctx.occOf c info true) $x).1)

/-- The shapes of the nested arguments as their binders `x_s`. -/
def nestShapeIds (c : CtorInfo) : Array Term := c.nested.map fun (x, _) => idT (nestShapeId x)

/-- `@Shape.c params data… x_s…`, as a term, with the constructor's binders in scope. -/
def shapeApp (c : CtorInfo) : CommandElabM Term := do
  let pTerms := ctx.pTerms
  let ids := c.allDataIds.map idT ++ nestShapeIds c
  `(@$(ctx.shapeCtor c):ident $pTerms* $ids*)

/-- `@Shape.c params data… sh…`, as a term on the right-hand side of a `match` on `F`, with the
given shapes of the nested arguments. -/
def shapeValWith (c : CtorInfo) (nestVals : Array Term) : CommandElabM Term := do
  let pTerms := ctx.pTerms
  let ids := (ctx.valDataIds c).map idT ++ nestVals
  `(@$(ctx.shapeCtor c):ident $pTerms* $ids*)

/-- `@Shape.c params data… (toC x).1…`, as a term on the right-hand side of a `match` on `F`. -/
def shapeVal (c : CtorInfo) : CommandElabM Term := do
  ctx.shapeValWith c (← ctx.nestShapeVals c)

/-- `@Shape.c _ data… x_s…`, as a pattern. -/
def shapePat (c : CtorInfo) : CommandElabM Term := do
  let hs ← ctx.pHoles
  let ids := (← ctx.patIds c c.allDataIds) ++ nestShapeIds c
  `(@$(ctx.shapeCtor c):ident $hs* $ids*)

/-- `@B.c_x params data… (toC x).1… extra…`, as a term after a `match` on `F` (the shapes of the
nested arguments are computed from the arguments). -/
def bApp (c : CtorInfo) (x : Ident) (extra : Array Term) : CommandElabM Term := do
  let pTerms := ctx.pTerms
  let ids := (ctx.valDataIds c).map idT ++ (← ctx.nestShapeVals c)
  `(@$(ctx.bCtor c x):ident $pTerms* $ids* $extra*)

/-- `@B.c_x _ data… x_s… extra…`, as a pattern. -/
def bPat (c : CtorInfo) (x : Ident) (extra : Array Term) : CommandElabM Term := do
  let hs ← ctx.pHoles
  let ids := (← ctx.patIds c c.allDataIds) ++ nestShapeIds c
  `(@$(ctx.bCtor c x):ident $hs* $ids* $extra*)

/-- Does the declaration have nested arguments? Then the proofs of the `F`-lemmas go through
the laws of the occurrence structures. -/
def hasOcc : Bool := ctx.ctors.any fun c => c.groups.any (·.kind.isOcc)

/-- The arguments of a constructor of `F` after `map f`, implicit ones included; with
`afterMatch`, in the value form. `app` applies the function to a recursive argument and `fn` is
the function itself, for nested arguments (by default `f _ _ x` and `f _ _`, for
`f : ∀ j₁ j₂, X j₁ j₂ → Y j₁ j₂`). -/
def mappedArgs (c : CtorInfo) (afterMatch : Bool) (app : Option (Term → CommandElabM Term) := none)
    (fn : Option Term := none) : CommandElabM (Array Term) := do
  let holes ← ctx.holes
  let app := app.getD fun x => `(f $holes* $x)
  -- For an indexed nested argument the packed index is bound by name: a `_` index leaves a
  -- metavariable that unification cannot solve when a hole's index is not a variable (`p.1`).
  let fnP : CommandElabM Term := do
    match fn with
    | some fn => `(fun _ => $fn)
    | none =>
      if ctx.k == 1 then `(f) else
      let pId ← freshId "p"
      let pProjs ← ctx.projs (idT pId)
      `(fun $pId:ident => f $pProjs*)
  let fn ← match fn with
    | some fn => pure fn
    | none => `(f $holes*)
  let args ← c.groups.mapM fun g => do
    g.ids.mapM fun (x : Ident) => match g.kind with
      | .data => pure (idT (if afterMatch then (ctx.bareIdx c x.getId).getD x else x))
      | .pos _ => app (idT x)
      | .fn tele _ => do
        let ys := teleIds tele
        let body ← app (← `($x:ident $ys*))
        `(fun $[$ys:ident]* => $body)
      | .occ info =>
        let o := ctx.occOf c info afterMatch
        if info.indexed then do `(Codata.IOcc.map $o $o $(← fnP) $x:ident)
        else `(Codata.Occ.map $o $o $fn $x:ident)
  return args.foldl (· ++ ·) #[]

end Ctx

open Ctx

/-- The packed index type `(i₁ : I₁) ×' (i₂ : I₂) ×' …` of an index telescope. -/
def mkIxTerm (idx : Array (Ident × Term)) : CommandElabM Term := do
  let mut Ix := idx.back!.2
  for m in [0:idx.size - 1] do
    let (x, ty) := idx[idx.size - 2 - m]!
    Ix ← `(PSigma fun ($x:ident : $ty) => $Ix)
  return Ix

/-- The index telescope of a declared sort `(i₁ : I₁) → I₂ → … → Type u`: names (fresh when
the arrow is not dependent) and types. -/
partial def readSort (t : Term) : CommandElabM (Array (Ident × Term)) := do
  match t with
  | `($b:bracketedBinder → $cod) =>
    let (ids, ty, _) ← readBinder b
    return ids.map (·, ty) ++ (← readSort cod)
  | `($dom → $cod) =>
    let rest ← readSort cod
    return #[(← freshId s!"i{Nat.toSubscriptString (rest.size + 1)}", dom)] ++ rest
  | _ => return #[]

/-- The index telescope of a declared sort, if any, with fresh names numbered from the front
(`readSort` numbers from the back). -/
def readIdx (sortStx : Option Term) : CommandElabM (Array (Ident × Term)) := do
  let idx0 ← match sortStx with
    | none => pure #[]
    | some sort => readSort sort
  idx0.mapIdxM fun m (x, ty) => do
    if x.getId.hasMacroScopes then return (← freshId s!"i{Nat.toSubscriptString (m + 1)}", ty)
    else return (x, ty)

/-- Analyse a declaration, or the declarations of a mutual block, and name everything: shared by
`codata` and `data`. `T` is the family being defined (the type, or the block `T₁_T₂`), `decls`
the types with their declared sorts and constructors. In a mutual block, `ix` is the index of the
block `Blk.Ix`, which has a constructor per type and is the only index of the family, and the
number of leading parameters it takes. -/
def mkCtx (co : Bool) (T : Ident) (paramsStx : Array (TSyntax ``bracketedBinder))
    (decls : Array (Ident × Option Term × Array (TSyntax ``codataCtor)))
    (ix : Option (Ident × Nat)) : CommandElabM Ctx := do
  let tName := T.getId
  let types := decls.map (·.1)
  let tNames := types.map (·.getId)
  let uidxs ← decls.mapM fun (_, sort, _) => readIdx sort
  let params ← paramsStx.mapM fun b => do
    let (ids, ty, _) ← readBinder b
    return (ids, ty)
  let pids : Array Ident := params.foldl (fun acc (ids, _) => acc ++ ids) #[]
  let pExp ← params.mapM fun (ids, ty) => `(bracketedBinderF| ($ids* : $ty))
  let pImp ← params.mapM fun (ids, ty) => `(bracketedBinderF| {$ids* : $ty})
  let rawCtors ← decls.mapM fun (_, _, cs) => cs.mapM fun c => do
    let `(codataCtor| | $name:ident $bs:bracketedBinder* $[: $resTy]?) := c
      | throwUnsupportedSyntax
    let raw ← bs.mapM readBinder
    return (name, raw, resTy, c)
  -- Names the user may refer to: plain unless the declaration uses them.
  let used : Array Name := pids.map (·.getId) ++
    uidxs.foldl (fun acc tele => acc ++ tele.map (·.1.getId)) #[] ++
    rawCtors.foldl (fun acc cs => cs.foldl (fun acc (name, raw, _, _) =>
      acc.push name.getId ++ raw.foldl (fun acc (ids, _, _) => acc ++ ids.map (·.getId)) #[]) acc) #[]
  let plainOr (n : Name) (hyg : Ident) : Ident := if used.contains n then hyg else mkIdent n
  let motiveId := plainOr `motive ⟨(← `(motive)).raw⟩
  let Sid := plainOr `S ⟨(← `(S)).raw⟩
  let mId := plainOr `m ⟨(← `(m)).raw⟩
  -- In a mutual block, `Blk.Ix` is the only index, and the indices of a type are the arguments
  -- of its constructor.
  let (idx, ixCtors) ← match ix with
    | none => pure (uidxs[0]!, #[])
    | some (Ix, nPs) =>
      let ixPs := (pids.extract 0 nPs).map idT
      let ixCtors ← tNames.mapM fun t => do
        let c := mkIdent (Ix.getId ++ Name.mkSimple t.getString!)
        return Syntax.mkApp (← `(@$c:ident)) ixPs
      pure (#[(mId, ← mkAppT Ix ixPs)], ixCtors)
  let nIdx := idx.size
  let wrap (m : Nat) (args : Array Term) : Array Term :=
    if ix.isSome then #[Syntax.mkApp ixCtors[m]! args] else args
  -- Constructor names shared by several types of the block are qualified in `F`, `Shape`, `B`.
  let allNames := rawCtors.map fun cs => cs.map (·.1.getId)
  let clashes (n : Name) : Bool := (allNames.filter (·.contains n)).size ≥ 2
  let n (s : String) : Ident := mkIdent (genName tName s)
  -- The packed index type, written out: `T.Ix` is declared with the signature, after the
  -- analysis.
  let IxpB ← if nIdx ≥ 2 then mkIxTerm idx else if nIdx == 1 then pure idx[0]!.2 else `(Unit)
  let pack (args : Array Term) : CommandElabM Term :=
    if nIdx == 0 then `(()) else if nIdx == 1 then pure args[0]! else `(⟨$[$args],*⟩)
  let mut ctors : Array CtorInfo := #[]
  for m in [0:rawCtors.size] do
    for (name, raw, resTy, c) in rawCtors[m]! do
      let mut groups : Array Group := #[]
      -- The scope of a binder's type: the parameters and the earlier non-recursive binders
      -- (the structure of a nested argument may mention them).
      let mut scope := pExp
      for (ids, ty, implicit) in raw do
        if ix.isSome then checkArity tNames pids (uidxs[·]!.size) ty
        let kind ← classify tNames tName pids scope wrap (nIdx > 0) IxpB pack ty
        if kind.isData then scope := scope.push (← mkBinder implicit ids ty)
        groups := groups.push { ids, ty, kind, implicit }
      for g in groups do
        if g.implicit && !g.kind.isData then
          throwErrorAt g.ty "implicit binders must not be recursive"
        unless g.kind.isData || g.kind.isOcc || g.kind.idx.size == nIdx do
          throwErrorAt g.ty "recursive argument with the wrong number of indices"
      let uidx ← match resTy with
        | none =>
          if uidxs[m]!.size > 0 then throwErrorAt c "the constructor needs a result type"
          else pure #[]
        | some r =>
          match recIdx tNames pids r with
          | some (m', cidx) =>
            unless m' == m do throwErrorAt r "the result type must be the type being declared"
            if cidx.size == uidxs[m]!.size then pure cidx
            else throwErrorAt r "result type with the wrong number of indices"
          | none => throwErrorAt r "the result type must be the declared type applied to its parameters"
      let fname := if clashes name.getId then
          mkIdent (Name.mkSimple (tNames[m]!.getString! ++ "_" ++ name.getId.toString))
        else name
      ctors := ctors.push { name, groups, idx := wrap m uidx, uidx, owner := m, fname }
  let nF (s : String) : Ident := mkIdent (.str (genName tName "F") s)
  let pTerms := pids.map idT
  let jIds ← idx.mapIdxM fun m _ => freshId s!"j{Nat.toSubscriptString (m + 1)}"
  let ujIds ← if ix.isSome then
      uidxs.mapM fun tele => tele.mapIdxM fun m _ => freshId s!"j{Nat.toSubscriptString (m + 1)}"
    else pure #[jIds]
  let Ixp ← if nIdx ≥ 2 then mkAppT (n "Ix") pTerms
    else if nIdx == 1 then pure idx[0]!.2 else `(Unit)
  return {
    co, T, tName, types, ixCtors, uidx := uidxs, ujIds, pids, pExp, pImp, pTerms
    ctors, idx, jIds, Ixp, motiveId, Sid
    Ix := n "Ix", idxId := n "idx", F := n "F", Shape := n "Shape", ShapeP := n "ShapeP"
    B := n "B", sig := n "sig"
    Fmap := nF "map", Rel := nF "Rel"
    Fmap_id := nF "map_id", Fmap_comp := nF "map_comp", Frel_map := nF "rel_map"
    toC := n "toC", ofC := n "ofC"
    ofC_toC := n "ofC_toC", ofC_map := n "ofC_map", rel_ofC := n "rel_ofC", toC_ofC := n "toC_ofC"
    dtor := n "dtor", corec := n "corec", dtor_corec := n "dtor_corec", bisim := n "bisim"
    contract := n "contract", ctor := n "ctor", dtor_ctor := n "dtor_ctor"
    ctor_dtor := n "ctor_dtor", ctor_injective := n "ctor_injective"
    corec_eq := n "corec_eq", corec_unique := n "corec_unique"
    casesOnAux := n "casesOnAux", casesOnId := n "casesOn", casesOn_ctor := n "casesOn_ctor"
    fold := n "fold", fold_ctor := n "fold_ctor", fold_eq := n "fold_eq"
    fold_unique := n "fold_unique", recAux := n "recAux", recId := n "rec", rec_ctor := n "rec_ctor"
    Tp := ← mkAppT T pTerms, Fp := ← mkAppT (n "F") pTerms, Shapep := ← mkAppT (n "Shape") pTerms
    ShapePp := ← mkAppT (n "ShapeP") pTerms
    Bp := ← mkAppT (n "B") pTerms
    sigp := ← mkAppT (n "sig") pTerms }

end Codata
