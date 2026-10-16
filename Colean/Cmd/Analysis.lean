import Colean.Model.Param

/-!
# The command, analysis

*Spec.* Input: the syntax of a `codata`/`data` declaration (or the declarations of a block).
Output: the context `Ctx`, everything the generators need: the constructors analysed into
binder groups with their kinds (`Kind`: data, plain recursive, under a telescope, nested with
its occurrence structure `OccInfo`; `PKind`: how a data binder uses the container parameter),
the index telescope, and the names of every generated declaration. The occurrence structure of
a nested argument is built here by recursion on the syntax of its type (`occTreeOf`,
`occTermOf`), with instance search only at named type constructors (`leafOcc?`); this is the
only place the command elaborates terms during the analysis. No declaration is generated here
except through `mkCtx`'s callers.
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
defined, or the container parameter) sit in it. Built by `occTreeOf` by recursion on the syntax
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
  partial application) with the structure `occ` of its `OccLeaf` instance. -/
  | leaf (G : Term) (occ : Term) (arg : OccTree)
  /-- `G (fun p => arg)` for a named functor of families `G`, with the structure `occ` of its
  `IOccLeaf` instance. -/
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

/-- How a non-recursive argument uses the container parameter (the last parameter, when it is
a type variable `α`): not at all, as its type `α`, under a telescope `(y₁ : B₁) → … → α`, or
nested, through its occurrence structure (`List α`, `α × α`, …). When every argument uses `α`
in one of these ways, the declared type has an occurrence structure in `α`: its erased shapes
`Shape₀` are the non-recursive data without these arguments (plus the shapes of the nested
ones), and its parameter positions `P` are these arguments, one constructor each. -/
inductive PKind where
  | none
  /-- `X j` (`j` is `()` for a type parameter). -/
  | val (j : Term)
  | fn (tele : Array (Ident × Term)) (j : Term)
  | occ (info : OccInfo)

def PKind.isNone : PKind → Bool
  | .none => true
  | _ => false

/-- A binder group of a constructor. -/
structure Group where
  ids : Array Ident
  ty : Term
  kind : Kind
  implicit : Bool
  /-- How the group uses the container parameter (`.none` for recursive groups). -/
  pk : PKind := .none

/-- A constructor, analysed: its name, binder groups, and the index arguments of its result type
(none without indices; in a mutual block, the first index is the type's constructor of `Which`).
-/
structure CtorInfo where
  name : Ident
  groups : Array Group
  idx : Array Term
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

/-- The non-recursive binder identifiers that do not use the container parameter: the data of
the erased shapes. -/
def CtorInfo.allDataIds₀ (c : CtorInfo) : Array Ident :=
  c.groups.foldl (fun acc g => if g.kind.isData && g.pk.isNone then acc ++ g.ids else acc) #[]

/-- The arguments at parameter positions, with how they use the parameter. -/
def CtorInfo.ppos (c : CtorInfo) : Array (Ident × PKind) :=
  c.groups.foldl (fun acc g => if g.pk.isNone then acc else acc ++ g.ids.map (·, g.pk)) #[]

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

/-- A recursive occurrence with its full index: one of the types `T params idx…` (its block
index prepended, `pre`), or the block family itself `Blk params idx…` (in a mutual block, the
block name applied to the block index and the user's indices). -/
def recOcc (tNames : Array Name) (blk : Name) (pre : Nat → Array Term) (params : Array Ident)
    (ty : Term) : Option (Array Term) :=
  match recIdx tNames params ty with
  | some (m, idx) => some (pre m ++ idx)
  | none => (recIdx #[blk] params ty).map (·.2)

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

/-- The structure of a leaf: a named type constructor `G`, as a lambda over the hole-containing
argument (or a partial application), from its `OccLeaf` instance (`IOccLeaf` for a family
argument), found by instance search in the scope; the structure term is the instance's field,
unfolded and delaborated, so that generated declarations mention the structure itself
(`Codata.Occ.list`, `Forest.occ α`) and never the search. -/
def leafOcc? (scope : Array (TSyntax ``bracketedBinderF)) (G : Term) (fam : Bool) :
    CommandElabM (Option Term) :=
  liftTermElabM do
    Term.elabBinders scope fun _ => Term.withoutErrToSorry do
      let stx ← if fam then `(@Codata.IOccLeaf.occ _ $G _ _ _ _) else `(@Codata.OccLeaf.occ $G _ _ _)
      let e? ← try
          let e ← Term.elabTerm stx none
          Term.synthesizeSyntheticMVarsNoPostponing
          pure (some (← instantiateMVars e))
        catch _ => pure none
      let some e := e? | return none
      let e ← (Meta.unfoldProjInst? e) >>= fun | some e' => pure e' | none => pure e
      let e ← Meta.whnfCore e
      return some (← PrettyPrinter.delab e)

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

/-- The occurrence tree of `ty`, for the hole recognised by `holeOf` (an occurrence with its
index arguments) among the names `names`: products, sums, functions and dependent pairs over
constant types, and named type constructors applied to one hole-containing argument (a family
`fun p => …` for a functor of families), whose structures come from the registry. -/
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
    unless ks.size == 1 do
      throwErrorAt ty "the types being defined occur in several arguments of `{f}`, which is \
        supported only for products, sums, functions and dependent pairs"
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
      let some occ ← leafOcc? scope G true
        | throwErrorAt ty "no `Codata.IOccLeaf` instance for the functor of families `{G}`; \
            nested occurrences of a family go through the types declared by `data` and \
            `codata` with a family parameter, and any functor with such an instance"
      return .ileaf G occ p (← go body)
    | none =>
      let some occ ← leafOcc? scope G false
        | throwErrorAt ty "no `Codata.OccLeaf` instance for the type constructor `{G}`; \
            nested occurrences are supported through products, sums, functions and dependent \
            pairs over constant types, `List`, `Option`, `Array`, the types declared by `data` \
            and `codata` with a type parameter, and any type constructor with such an instance"
      return .leaf G occ (← go arg)
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

/-- Does the tree mention one of the names outside its holes: in a constant, the domain of a
function or a dependent pair, the head of a leaf, or the index of a hole? -/
partial def OccTree.mentionsOutside (names : Array Name) : OccTree → Bool
  | .const t => mentionsAny t.raw names
  | .hole idx => idx.any (mentionsAny ·.raw names)
  | .prod l r | .sum l r => l.mentionsOutside names || r.mentionsOutside names
  | .pi _ A _ body | .sigma _ A body => mentionsAny A.raw names || body.mentionsOutside names
  | .leaf G _ arg => mentionsAny G.raw names || arg.mentionsOutside names
  | .ileaf G _ _ arg => mentionsAny G.raw names || arg.mentionsOutside names

/-- Classify the type of a constructor argument: a plain recursive argument `T params idx`, a
recursive argument under a telescope of arrows ending in one, a nested one (any other type
mentioning the types being defined, through its occurrence structure), or non-recursive data,
which may not mention the types being defined at all. `pre m` is the block index of the `m`-th
type (its constructor of `Which`, nothing outside mutual blocks), prepended to the index
arguments; `blk` is the block family, which nested occurrences may mention directly. With
indices (`idxed`), the structure of a nested argument is indexed over the packed index type
`Ixp`, the indices packed by `pack`. -/
private partial def classify (tNames : Array Name) (blk : Name) (params : Array Ident)
    (scope : Array (TSyntax ``bracketedBinderF)) (pre : Nat → Array Term) (idxed : Bool)
    (Ixp : Term) (pack : Array Term → CommandElabM Term) (ty : Term) : CommandElabM Kind := do
  let names := tNames.push blk
  if let some idx := recOcc tNames blk pre params ty then return .pos idx
  let rec go (t : Term) (acc : Array (Ident × Term)) : CommandElabM (Option Kind) := do
    match t with
    | `($b:bracketedBinder → $cod) =>
      let (ids, dom, _) ← readBinder b
      go cod (acc ++ ids.map (·, dom))
    | `($dom → $cod) =>
      go cod (acc.push (← freshId s!"y{Nat.toSubscriptString (acc.size + 1)}", dom))
    | _ => return (recOcc tNames blk pre params t).map fun idx => .fn acc idx
  if let some k ← go ty #[] then
    if let .fn tele _ := k then
      for (_, dom) in tele do
        if mentionsAny dom.raw names then
          throwErrorAt dom "the types being defined may not occur in the domain of a function"
    return k
  unless mentionsAny ty.raw names do return .data
  let tree ← occTreeOf (recOcc tNames blk pre params) names scope ty
  let o ← occTermOf idxed Ixp pack tree
  let (Sh, Pos, pidx?) ← occShapes scope o idxed
  return .occ { tree, o, Sh, Pos, indexed := idxed, pidx := pidx?.getD Pos }

/-- Is `ty` the sort `Type`, `Type u` or `Type _`? -/
private def isTypeSort (ty : Term) : Bool := ty.raw.isOfKind ``Parser.Term.type

/-- The sort of a container parameter: `some none` for a type `Type u`, `some (some J)` for a
family `J → Type u` (or `(j : J) → Type u`), `none` otherwise. -/
private def paramSort (ty : Term) : Option (Option Term) :=
  if isTypeSort ty then some none
  else match ty with
    | `($J → $cod) => if isTypeSort cod then some (some J) else none
    | `(($_:ident : $J) → $cod) => if isTypeSort cod then some (some J) else none
    | _ => none

/-- How the type `ty` of a non-recursive argument uses the parameter `a` (a family over `J` when
`J` is given): `.none` when it does not occur, `.val j`, `.fn tele j` for the recognised forms
`a j`, `(y₁ : B₁) → … → a j` (just `a` for a type parameter, with `j := ()`), `.occ` for any
other type with an occurrence structure in `a`, and no result otherwise. -/
private partial def classifyParam (a : Ident) (J : Option Term)
    (scope : Array (TSyntax ``bracketedBinderF)) (ty : Term) : CommandElabM (Option PKind) := do
  let an := #[a.getId]
  let ty := stripParen ty
  unless mentionsAny ty.raw an do return some .none
  let fam := J.isSome
  let isA (t : Term) : Bool := t.raw.isIdent && t.raw.getId == a.getId
  let unit ← `(())
  -- `a j` (or `a`): the index.
  let occA (t : Term) : Option Term :=
    let t := stripParen t
    if fam then
      match t with
      | `($f:ident $j:term) => if isA f && !mentionsAny j.raw an then some j else none
      | _ => none
    else if isA t then some unit else none
  if let some j := occA ty then return some (.val j)
  let rec go (t : Term) (acc : Array (Ident × Term)) : CommandElabM (Option PKind) := do
    match t with
    | `($b:bracketedBinder → $cod) =>
      let (ids, dom, _) ← readBinder b
      if mentionsAny dom.raw an then return none
      go cod (acc ++ ids.map (·, dom))
    | `($dom → $cod) =>
      if mentionsAny dom.raw an then return none
      go cod (acc.push (← freshId s!"y{Nat.toSubscriptString (acc.size + 1)}", dom))
    | _ => return if acc.isEmpty then none else (occA t).map (.fn acc)
  if let some k ← go ty #[] then return some k
  -- Otherwise the occurrence structure of the type in `a`: a type parameter is a plain hole, a
  -- family parameter a hole at its index.
  let holeOf (t : Term) : Option (Array Term) := (occA t).map fun j => if fam then #[j] else #[]
  let tree? ← try some <$> occTreeOf holeOf an scope ty catch _ => pure none
  let some tree := tree? | return none
  let Jt := J.getD unit
  let o ← occTermOf fam Jt (fun idx => pure idx[0]!) tree
  let res ← try some <$> occShapes scope o fam catch _ => pure none
  let some (Sh, Pos, pidx?) := res | return none
  return some (.occ { tree, o, Sh, Pos, indexed := fam, pidx := pidx?.getD Pos })

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

/-- The container parameter: its name, its sort, and the index type `J` of a family. -/
structure ParamInfo where
  a : Ident
  aTy : Term
  J : Option Term

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
  /-- In a mutual block, the enumeration of the types, which is the first index of the block. -/
  which : Option Ident
  pids : Array Ident
  pExp : Array (TSyntax ``bracketedBinderF)
  pImp : Array (TSyntax ``bracketedBinderF)
  pTerms : Array Term
  /-- The container parameter: the last parameter, when it is a type variable, or a family
  `J → Type u`, that the constructors use only at parameter positions. Then the type is a
  container in it, and the declarations that do not depend on it (`Shape₀`, `P`, `B`, `Ix`,
  `psig`, `Sh`, `Pos`) take the parameters without it, `pids₀` (all of them otherwise). -/
  param : Option ParamInfo
  pids₀ : Array Ident
  pExp₀ : Array (TSyntax ``bracketedBinderF)
  pImp₀ : Array (TSyntax ``bracketedBinderF)
  pTerms₀ : Array Term
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
  /-- With a container parameter: the erased shapes, the parameter positions, the equivalence
  `Shape ≃ Σ s₀, P s₀ → α` and the parameterised signature. -/
  Shape₀ : Ident
  Shape₀P : Ident
  P : Ident
  shapeTo : Ident
  shapeOf : Ident
  shapeOf_shapeTo : Ident
  shapeTo_shapeOf : Ident
  shapeEquiv : Ident
  /-- The index of a parameter position, for a family parameter. -/
  pidxId : Ident
  psig : Ident
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
  Shape₀p : Term
  Shape₀Pp : Term
  Pp : Term
  shapeEquivp : Term
  psigp : Term
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

/-- The arguments nested in the parameter, with their structures. -/
def CtorInfo.pnested (c : CtorInfo) : Array (Ident × OccInfo) :=
  c.groups.foldl (init := #[]) fun acc g => match g.pk with
    | .occ info => acc ++ g.ids.map (·, info)
    | _ => acc

/-- The shape binders `(x_s : Sh)` of the arguments nested in the parameter. -/
def pnestShapeBinders (c : CtorInfo) (implicit : Bool) :
    CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  c.pnested.mapM fun (x, info) => mkBinder implicit #[nestShapeId x] info.Sh

/-- The data binders of a constructor without the parameter positions, and the shapes of its
nested arguments and of its containers in the parameter, all implicit (for the constructors of
`B` and `P`, where they are determined by the erased shape). -/
def dataBindersImplicit (c : CtorInfo) : CommandElabM (Array (TSyntax ``bracketedBinderF)) := do
  return (← (c.groups.filter fun g => g.kind.isData && g.pk.isNone).mapM fun g =>
      mkBinder true g.ids g.ty) ++
    (← nestShapeBinders c true) ++ (← pnestShapeBinders c true)

namespace Ctx

variable (ctx : Ctx)

def fCtor (c : CtorInfo) : Ident := mkIdent (ctx.F.getId ++ c.fname.getId)
def shapeCtor (c : CtorInfo) : Ident := mkIdent (ctx.Shape.getId ++ c.fname.getId)
def bCtor (c : CtorInfo) (x : Ident) : Ident := mkIdent (ctx.B.getId ++ (posCtorName c x).getId)
def shape₀Ctor (c : CtorInfo) : Ident := mkIdent (ctx.Shape₀.getId ++ c.fname.getId)
def pCtor (c : CtorInfo) (x : Ident) : Ident := mkIdent (ctx.P.getId ++ (posCtorName c x).getId)

/-- Does the declaration have a container parameter? -/
def hasParam : Bool := ctx.param.isSome

/-! In a mutual block, the user-facing declarations of a constructor live under its own type. -/

/-- The name of the `m`-th type of the block. -/
def tyName (m : Nat) : Name := ctx.types[m]!.getId

/-- `T.s`, for the `m`-th type. -/
def tyId (m : Nat) (s : String) : Ident := mkIdent (.str (ctx.tyName m) s)

def tCtor (c : CtorInfo) : Ident := mkIdent (ctx.tyName c.owner ++ c.name.getId)
def tName' (c : CtorInfo) (pre post : String) : Ident :=
  mkIdent (ctx.tyName c.owner ++ Name.mkSimple (pre ++ c.name.getId.toString ++ post))
def nF (s : String) : Ident := mkIdent (.str (.str ctx.tName "F") s)

def isMutual : Bool := ctx.which.isSome

/-- `T.s`, for the family being defined. -/
def nm (s : String) : Ident := mkIdent (.str ctx.tName s)

/-- The number of leading indices that are not the user's: one in a mutual block. -/
def off : Nat := if ctx.isMutual then 1 else 0

/-- The constructor of `Which` for the `m`-th type. -/
def whichCtor (m : Nat) : Term :=
  idT (mkIdent (ctx.which.get!.getId ++ Name.mkSimple (ctx.tyName m).getString!))

/-- The block index of the `m`-th type: its constructor of `Which`, or nothing. -/
def pre (m : Nat) : Array Term := if ctx.isMutual then #[ctx.whichCtor m] else #[]

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

/-- `_` for every parameter but the container parameter. -/
def pHoles₀ : CommandElabM (Array Term) := ctx.pids₀.mapM fun _ => `(_)

/-- If the constructor's binder `x` is one of the indices of its result type, that index
binder. In a `match` whose discriminant has the index binders as indices, the pattern variable
`x` is eliminated in favour of the index binder, so right-hand sides refer to the latter. -/
def bareIdx (c : CtorInfo) (x : Name) : Option Ident :=
  (c.idx.findIdx? fun t => t.raw.isIdent && t.raw.getId == x).map fun m => ctx.iIds[m]!

/-- Substitute the binders that are indices by the index binders. -/
def substBare (c : CtorInfo) (t : Term) : Term := ⟨substIds t.raw (ctx.bareIdx c)⟩

/-- The constructor's binders as values in a right-hand side after a `match`: the index binders
for those that are indices. -/
def valIds (c : CtorInfo) : Array Ident :=
  c.allIds.map fun x => (ctx.bareIdx c x.getId).getD x

def valDataIds (c : CtorInfo) : Array Ident :=
  c.allDataIds.map fun x => (ctx.bareIdx c x.getId).getD x

def valDataIds₀ (c : CtorInfo) : Array Ident :=
  c.allDataIds₀.map fun x => (ctx.bareIdx c x.getId).getD x

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

/-! The user's indices, without the block index: what the per-type declarations of a mutual
block (the types, `casesOn`, the aliases) are stated with. Outside mutual blocks these coincide
with the helpers above. -/

/-- The number of the user's indices. -/
def uk : Nat := ctx.k - ctx.off

def uIdxed : Bool := ctx.uk > 0

def uIArgs : Array Term := ctx.iArgs.extract ctx.off ctx.k
def uJArgs : Array Term := ctx.jArgs.extract ctx.off ctx.k

/-- The user's index binders, named as in `names` (which names all indices). -/
def uIxBindersWith (names : Array Ident) (implicit : Bool) :
    CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  (Array.range ctx.k).filterMapM fun m => do
    if m < ctx.off then return none
    return some (← mkBinder implicit #[names[m]!] (ctx.renameTo names ctx.idx[m]!.2))

def uIxB : CommandElabM (Array (TSyntax ``bracketedBinderF)) := ctx.uIxBindersWith ctx.iIds true
def uIxBExp : CommandElabM (Array (TSyntax ``bracketedBinderF)) := ctx.uIxBindersWith ctx.iIds false
def uJB : CommandElabM (Array (TSyntax ``bracketedBinderF)) := ctx.uIxBindersWith ctx.jIds false

/-- The user's index arguments of a constructor's result type. -/
def uIdxOf (c : CtorInfo) : Array Term := c.idx.extract ctx.off c.idx.size

/-- The `m`-th user-facing type applied to the parameters. -/
def tyP (m : Nat) : CommandElabM Term :=
  if ctx.isMutual then mkAppT ctx.types[m]! ctx.pTerms else pure ctx.Tp

/-- `Tₘ params i…`, at the user's index binders. -/
def tyAtU (m : Nat) : CommandElabM Term := do appT (← ctx.tyP m) ctx.uIArgs

/-- The user-facing type of a constructor's result, `Tₘ params idx…`. -/
def tyAt (c : CtorInfo) : CommandElabM Term := do appT (← ctx.tyP c.owner) (ctx.uIdxOf c)

/-- The full index arguments of the `m`-th type at the user's index binders: its block index,
then the user's binders. -/
def fullArgs (m : Nat) : Array Term := ctx.pre m ++ ctx.uIArgs

/-- The user-facing type at a full index (the block index first in a mutual block): the type
whose constructor of `Which` is the first index, at the remaining ones; the block family when
the first index is another term. -/
def recTyOf (idx : Array Term) : CommandElabM Term := do
  if ctx.isMutual then
    for m in [0:ctx.types.size] do
      if idx.size > 0 && idx[0]!.raw.structEq (ctx.whichCtor m).raw then
        return ← appT (← ctx.tyP m) (idx.extract 1 idx.size)
  appT ctx.Tp idx

/-- The occurrence structure in the parameter of the user-facing type at a full index, applied
to its parameters and indices (`T.occ params₀ idx`); the block family's (`Blk.occ`) when the
first index is not a constructor of `Which`. -/
def recOccOf (idx : Array Term) : CommandElabM Term := do
  if ctx.isMutual then
    for m in [0:ctx.types.size] do
      if idx.size > 0 && idx[0]!.raw.structEq (ctx.whichCtor m).raw then
        return ← mkAppT (ctx.tyId m "occ") (ctx.pTerms₀ ++ idx.extract 1 idx.size)
  mkAppT (ctx.nm "occ") (ctx.pTerms₀ ++ idx)

/-- The patterns for the user's indices. -/
def uIdxPats (c : CtorInfo) : CommandElabM (Array Term) :=
  return (← ctx.idxPats c).extract ctx.off ctx.k

def uDiscrs (x : Term) : Array Term := ctx.uIArgs.push x

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

/-- The shapes of the arguments nested in the parameter, as values: `(Occ.toC o x).1`. -/
def pnestShapeVals (c : CtorInfo) : CommandElabM (Array Term) :=
  c.pnested.mapM fun (x, info) => `(($(occId info.indexed `toC) $(info.o) $x).1)

/-- The shapes of the arguments nested in the parameter as their binders `x_s`. -/
def pnestShapeIds (c : CtorInfo) : Array Term := c.pnested.map fun (x, _) => idT (nestShapeId x)

/-- `@Shape₀.c params₀ data₀… x_s…`, as a term, with the constructor's binders in scope. -/
def shape₀App (c : CtorInfo) : CommandElabM Term := do
  let pTerms₀ := ctx.pTerms₀
  let ids := c.allDataIds₀.map idT ++ nestShapeIds c ++ pnestShapeIds c
  `(@$(ctx.shape₀Ctor c):ident $pTerms₀* $ids*)

/-- `@Shape₀.c params₀ data₀… x_s… sh…`, as a term on the right-hand side of a `match` on
`Shape`, with the given shapes of the containers in the parameter. -/
def shape₀ValWith (c : CtorInfo) (pnestVals : Array Term) : CommandElabM Term := do
  let pTerms₀ := ctx.pTerms₀
  let ids := (ctx.valDataIds₀ c).map idT ++ nestShapeIds c ++ pnestVals
  `(@$(ctx.shape₀Ctor c):ident $pTerms₀* $ids*)

/-- `@Shape₀.c _ data₀… x_s…`, as a pattern. -/
def shape₀Pat (c : CtorInfo) : CommandElabM Term := do
  let hs ← ctx.pHoles₀
  let ids := (← ctx.patIds c c.allDataIds₀) ++ nestShapeIds c ++ pnestShapeIds c
  `(@$(ctx.shape₀Ctor c):ident $hs* $ids*)

/-- `@B.c_x params₀ data₀… (toC x).1… extra…`, as a term after a `match` on `F` (the shapes of
the nested arguments and of the containers in the parameter are computed from the arguments).
-/
def bApp (c : CtorInfo) (x : Ident) (extra : Array Term) : CommandElabM Term := do
  let pTerms₀ := ctx.pTerms₀
  let ids := (ctx.valDataIds₀ c).map idT ++ (← ctx.nestShapeVals c) ++ (← pnestShapeVals c)
  `(@$(ctx.bCtor c x):ident $pTerms₀* $ids* $extra*)

/-- `@B.c_x _ data₀… x_s… extra…`, as a pattern. -/
def bPat (c : CtorInfo) (x : Ident) (extra : Array Term) : CommandElabM Term := do
  let hs ← ctx.pHoles₀
  let ids := (← ctx.patIds c c.allDataIds₀) ++ nestShapeIds c ++ pnestShapeIds c
  `(@$(ctx.bCtor c x):ident $hs* $ids* $extra*)

/-- `@P.c_x _ data₀… x_s… extra…`, as a pattern. -/
def pPat (c : CtorInfo) (x : Ident) (extra : Array Term) : CommandElabM Term := do
  let hs ← ctx.pHoles₀
  let ids := (← ctx.patIds c c.allDataIds₀) ++ nestShapeIds c ++ pnestShapeIds c
  `(@$(ctx.pCtor c x):ident $hs* $ids* $extra*)

/-- The shapes `S` and the equivalence `e` of the parameterised signature, `sig = psig.sig S e`
(with the container parameter free): the shapes (on the packed index) and `shapeEquiv` at
every index. -/
def sigSE : CommandElabM (Term × Term) := do
  if !ctx.idxed then return (← `(fun _ => $(ctx.Shapep)), ← `(fun {_} => $(ctx.shapeEquivp)))
  if ctx.packed then
    let iPat ← ctx.pack ctx.iArgs
    let iArgs := ctx.iArgs
    return (ctx.ShapePp,
      ← `(fun {p} => match p with | $iPat:term => $(ctx.shapeEquivp) $iArgs*))
  let i := ctx.iIds[0]!
  return (ctx.Shapep, ← `(fun {$i:ident} => $(ctx.shapeEquivp) $i:ident))

/-- The index type `J` and the position index of the parameterised signature (`Unit` and
`fun _ => ()` for a type parameter; the plain and single-index forms). -/
def psigJ : CommandElabM (Term × Term) := do
  match ctx.param with
  | some { J := some J, .. } => return (J, ← `(fun p => $(ctx.pidxId) p))
  | _ => return (← `(Unit), ← `(fun _ => ()))

/-- The parameter as a family: itself, or `fun _ => α` for a type parameter. -/
def famX (pinfo : ParamInfo) : CommandElabM Term :=
  if pinfo.J.isSome then pure (idT pinfo.a) else `(fun _ => $(pinfo.a))

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

/-- Analyse a declaration, or the declarations of a mutual block, and name everything: shared by
`codata` and `data`. `T` is the family being defined (the type, or the block `T₁_T₂`), `decls`
the types with their constructors, `which` the enumeration of the types of a mutual block, which
becomes the first index. -/
def mkCtx (co : Bool) (T : Ident) (paramsStx : Array (TSyntax ``bracketedBinder))
    (sortStx : Option Term) (decls : Array (Ident × Array (TSyntax ``codataCtor)))
    (which : Option Ident) : CommandElabM Ctx := do
  let tName := T.getId
  let types := decls.map (·.1)
  let tNames := types.map (·.getId)
  let params ← paramsStx.mapM fun b => do
    let (ids, ty, _) ← readBinder b
    return (ids, ty)
  let pids : Array Ident := params.foldl (fun acc (ids, _) => acc ++ ids) #[]
  let pExp ← params.mapM fun (ids, ty) => `(bracketedBinderF| ($ids* : $ty))
  let pImp ← params.mapM fun (ids, ty) => `(bracketedBinderF| {$ids* : $ty})
  -- The index telescope, from the declared sort. Unnamed indices get fresh names numbered from
  -- the front; `readSort` numbers from the back, so renumber.
  let idx0 ← match sortStx with
    | none => pure #[]
    | some sort => readSort sort
  let uidx ← idx0.mapIdxM fun m (x, ty) => do
    if x.getId.hasMacroScopes then return (← freshId s!"i{Nat.toSubscriptString (m + 1)}", ty)
    else return (x, ty)
  let rawCtors ← decls.mapM fun (_, cs) => cs.mapM fun c => do
    let `(codataCtor| | $name:ident $bs:bracketedBinder* $[: $resTy]?) := c
      | throwUnsupportedSyntax
    let raw ← bs.mapM readBinder
    return (name, raw, resTy, c)
  -- Names the user may refer to: plain unless the declaration uses them.
  let used : Array Name := pids.map (·.getId) ++ uidx.map (·.1.getId) ++
    rawCtors.foldl (fun acc cs => cs.foldl (fun acc (name, raw, _, _) =>
      acc.push name.getId ++ raw.foldl (fun acc (ids, _, _) => acc ++ ids.map (·.getId)) #[]) acc) #[]
  let plainOr (n : Name) (hyg : Ident) : Ident := if used.contains n then hyg else mkIdent n
  let motiveId := plainOr `motive ⟨(← `(motive)).raw⟩
  let Sid := plainOr `S ⟨(← `(S)).raw⟩
  let mId := plainOr `m ⟨(← `(m)).raw⟩
  -- In a mutual block, the enumeration of the types is the first index, and every index list
  -- starts with the type's constructor.
  let idx := (match which with | some W => #[(mId, idT W)] | none => #[]) ++ uidx
  let nIdx := idx.size
  let pre (m : Nat) : Array Term := match which with
    | some W => #[idT (mkIdent (W.getId ++ Name.mkSimple tNames[m]!.getString!))]
    | none => #[]
  -- Constructor names shared by several types of the block are qualified in `F`, `Shape`, `B`.
  let allNames := rawCtors.map fun cs => cs.map (·.1.getId)
  let clashes (n : Name) : Bool := (allNames.filter (·.contains n)).size ≥ 2
  -- The container parameter: the last parameter, when it is a single type variable that the
  -- constructors use only at parameter positions (`classifyParam`), which does not occur in
  -- the indices, and which recursive arguments mention only as the parameter.
  let paramCand : Option ParamInfo := match params.back? with
    | some (#[a], ty) => (paramSort ty).map fun J => { a, aTy := ty, J }
    | _ => none
  let an : Option (Array Name) := paramCand.map fun pinfo => #[pinfo.a.getId]
  let mentionsA (t : Term) : Bool := match an with
    | some an => mentionsAny t.raw an
    | none => false
  let mut pOk := paramCand.isSome
  if uidx.any fun (_, ty) => mentionsA ty then pOk := false
  let n (s : String) : Ident := mkIdent (.str tName s)
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
      -- (the container of a nested argument may mention them).
      let mut scope := pExp
      for (ids, ty, implicit) in raw do
        let kind ← classify tNames tName pids scope pre (nIdx > 0) IxpB pack ty
        if kind.isData then scope := scope.push (← mkBinder implicit ids ty)
        let mut pk := PKind.none
        if let some pinfo := paramCand then
          match kind with
          | .data =>
            match ← classifyParam pinfo.a pinfo.J scope ty with
            | some k => pk := k
            | none => pOk := false
          | .pos idx => if idx.any mentionsA then pOk := false
          | .fn tele idx =>
            if idx.any mentionsA || tele.any (fun (_, d) => mentionsA d) then pOk := false
          | .occ info => if info.tree.mentionsOutside (an.getD #[]) then pOk := false
        groups := groups.push { ids, ty, kind, implicit, pk }
      for g in groups do
        if g.implicit && !g.kind.isData then
          throwErrorAt g.ty "implicit binders must not be recursive"
        unless g.kind.isData || g.kind.isOcc || g.kind.idx.size == nIdx do
          throwErrorAt g.ty "recursive argument with the wrong number of indices"
      let cidx ← match resTy with
        | none =>
          if uidx.size > 0 then throwErrorAt c "the constructor needs a result type"
          else pure (pre m)
        | some r =>
          match recIdx tNames pids r with
          | some (m', cidx) =>
            unless m' == m do throwErrorAt r "the result type must be the type being declared"
            if cidx.size == uidx.size then pure (pre m ++ cidx)
            else throwErrorAt r "result type with the wrong number of indices"
          | none => throwErrorAt r "the result type must be the declared type applied to its parameters"
      if cidx.any mentionsA then pOk := false
      let fname := if clashes name.getId then
          mkIdent (Name.mkSimple (tNames[m]!.getString! ++ "_" ++ name.getId.toString))
        else name
      ctors := ctors.push { name, groups, idx := cidx, owner := m, fname }
  let param := if pOk then paramCand else none
  unless pOk do
    ctors := ctors.map fun c => { c with groups := c.groups.map fun g => { g with pk := .none } }
  let params₀ := if param.isSome then params.pop else params
  let pids₀ : Array Ident := params₀.foldl (fun acc (ids, _) => acc ++ ids) #[]
  let pExp₀ ← params₀.mapM fun (ids, ty) => `(bracketedBinderF| ($ids* : $ty))
  let pImp₀ ← params₀.mapM fun (ids, ty) => `(bracketedBinderF| {$ids* : $ty})
  let nF (s : String) : Ident := mkIdent (.str (.str tName "F") s)
  let pTerms := pids.map idT
  let pTerms₀ := pids₀.map idT
  let jIds ← idx.mapIdxM fun m _ => freshId s!"j{Nat.toSubscriptString (m + 1)}"
  let Ixp ← if nIdx ≥ 2 then mkAppT (n "Ix") pTerms₀
    else if nIdx == 1 then pure idx[0]!.2 else `(Unit)
  return {
    co, T, tName, types, which, pids, pExp, pImp, pTerms, param, pids₀, pExp₀, pImp₀, pTerms₀
    ctors, idx, jIds, Ixp, motiveId, Sid
    Ix := n "Ix", idxId := n "idx", F := n "F", Shape := n "Shape", ShapeP := n "ShapeP"
    Shape₀ := n "Shape₀", Shape₀P := n "Shape₀P", P := n "P", shapeTo := n "shapeTo"
    shapeOf := n "shapeOf", shapeOf_shapeTo := n "shapeOf_shapeTo"
    shapeTo_shapeOf := n "shapeTo_shapeOf", shapeEquiv := n "shapeEquiv", pidxId := n "pidx"
    psig := n "psig"
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
    ShapePp := ← mkAppT (n "ShapeP") pTerms, Shape₀p := ← mkAppT (n "Shape₀") pTerms₀
    Shape₀Pp := ← mkAppT (n "Shape₀P") pTerms₀, Pp := ← mkAppT (n "P") pTerms₀
    shapeEquivp := ← mkAppT (n "shapeEquiv") pTerms, psigp := ← mkAppT (n "psig") pTerms₀
    Bp := ← mkAppT (n "B") pTerms₀
    sigp := ← mkAppT (n "sig") pTerms }

end Codata
