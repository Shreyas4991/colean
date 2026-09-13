import MetricCorec.Subtypes.Codata

/-!
# The `codata` command

Current scope: parameters, a single type, any number of indices. Constructor binders may be
explicit or implicit; recursive arguments may be plain (`t : T params idx`) or under a telescope
of arrows (`f : (y₁ : B₁) → … → Bₙ → T params idx`), dependent or not, where the domains may
depend on the constructor's own data and the index on the bound variables. A data binder may not
mention `T`.

```
codata ITree (E : Type → Type) (R : Type)
  | Ret (r : R)
  | Tau (t : ITree E R)
  | Vis {X : Type} (e : E X) (k : X → ITree E R)

codata Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)
```

The command generates, with the parameters as arguments of every declaration (explicit for the
types `T`, `T.F`, `T.Shape`, `T.B`, `T.sig`, implicit elsewhere):

* `T.F (params) (X : Type _)`: the constructor list with `T params` replaced by `X`, as an
  inductive type; `T.F.map` and `T.F.Rel`, its action on functions and its lifting to relations,
  with the laws `T.F.map_id`, `T.F.map_comp`, `T.F.rel_map`, and the simp lemmas `T.F.map_ctorᵢ`;
* the signature: `T.Shape` (the constructors with their non-recursive data only) and
  `T.B : T.Shape → Type`, the positions for recursive arguments, one nullary constructor `ctorᵢ_t`
  per plain argument `t` and one unary constructor `ctorᵢ_f (p : A)` per function argument
  `f : A → T`; bundled as `T.sig`;
* `T.toC`, `T.ofC` with the three laws `T.ofC_toC`, `T.ofC_map`, `T.rel_ofC`;
* the contract: `T`, `T.dtor`, `T.corec`, `T.dtor_corec`, `T.bisim`, transported from the
  generic `Signature` theorems; `T.corec` accepts a state in any universe;
* derived from the contract (`Codata.Contract`): `T.ctor`, `T.dtor_ctor`, `T.ctor_dtor`,
  `T.ctor_injective`, `T.corec_eq`, `T.corec_unique`; the individual constructors `T.ctorᵢ` with
  the simp lemmas `T.dtor_ctorᵢ` and `T.ctor_ctorᵢ` (`T.ctor (T.F.ctorᵢ …) = T.ctorᵢ …`),
  injectivity `T.ctorᵢ_inj` (for constructors without implicit binders) and disjointness
  `T.ctorᵢ_ne_ctorⱼ`, all simp lemmas;
* a case analysis principle `T.casesOn`, registered as the `cases` eliminator for `T`, with
  its computation rules `T.casesOn_ctorᵢ` as simp lemmas.

With indices (`codata T (params) : (i₁ : I₁) → I₂ → Type u`, constructors
`ctorᵢ … : T params idx₁ idx₂`), the same declarations are generated in their indexed form:
`T.F (params) (X : ∀ i₁ i₂, Type _) : ∀ i₁ i₂, Type _`, `T.F.map (f : ∀ j₁ j₂, X j₁ j₂ → Y j₁ j₂)`,
`T.Shape : ∀ i₁ i₂, Type _`, `T.B : ∀ i₁ i₂, T.Shape i₁ i₂ → ∀ j₁ j₂, Type _` (a position records
the indices of its recursive argument), `T : ∀ i₁ i₂, Type _`, `T.dtor {i₁ i₂}`,
`T.corec (c : ∀ j₁ j₂, S j₁ j₂ → T.F S j₁ j₂) {i₁ i₂}`, `T.bisim (R : ∀ j₁ j₂, …)`, a motive
`∀ j₁ j₂, T j₁ j₂ → Sort _` for `T.casesOn`, and so on. The index binders carry the names the
user gave them. Injectivity and disjointness lemmas are generated only when they are well-typed,
that is when the indices involved do not depend on the constructors' arguments and (for
disjointness) coincide.

The generic theory (`Codata.lean`) has one index type. Several indices are packed into one,
`T.Ix (params) := (i₁ : I₁) ×' I₂` (a `PSigma`, so indices may be propositions), and no index is
`Unit`; the user-facing declarations are curried: the internal isomorphism `T.toC`/`T.ofC` with
its three laws takes the family on the packed index, and the instantiations of the generic
theorems convert between the two forms with lambdas (`fun j₁ j₂ => f ⟨j₁, j₂⟩`,
`fun p => c p.1 p.2`), so that every statement above is definitionally the generic one. With one
index nothing is packed.

Only the six lemmas about the generated inductive `T.F` (`map_id`, `map_comp`, `rel_map`,
`ofC_toC`, `ofC_map`, `rel_ofC`) are proved by tactic scripts, and those are `cases` followed by
`rfl` or `solve_by_elim`; everything else instantiates a theorem of `Codata.lean` or
`CodataIdx.lean`. The declarations from `T` on are generated in a `noncomputable section`, since
the encoding decides equality of shapes classically.
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

/-- The kind of a constructor argument: non-recursive data, a plain recursive argument, or a
recursive argument under a function type with the given domain; recursive arguments carry the
index arguments of their type (none without indices). -/
inductive Kind where
  | data
  | pos (idx : Array Term)
  /-- A recursive argument under a telescope, `(y₁ : B₁) → … → (yₙ : Bₙ) → T params idx`, where
  the index may mention the `yⱼ` (fresh names when an arrow is not dependent). -/
  | fn (tele : Array (Ident × Term)) (idx : Array Term)

/-- A binder group of a constructor. -/
structure Group where
  ids : Array Ident
  ty : Term
  kind : Kind
  implicit : Bool

/-- A constructor, analysed: its name, binder groups, and the index arguments of its result type
(none without indices). -/
structure CtorInfo where
  name : Ident
  groups : Array Group
  idx : Array Term

private def idT (x : Ident) : Term := ⟨x.raw⟩

def Kind.isData : Kind → Bool
  | .data => true
  | _ => false

def Kind.idx : Kind → Array Term
  | .data => #[]
  | .pos idx => idx
  | .fn _ idx => idx

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

/-- Syntactic equality of index arguments. -/
def idxEq (a b : Array Term) : Bool :=
  a.size == b.size && (a.zip b).all fun (x, y) => x.raw.structEq y.raw

/-- `f` applied to `args`, or just `f` when there are none. -/
def appT (f : Term) (args : Array Term) : CommandElabM Term :=
  if args.isEmpty then pure f else `($f $args*)

private def mkAppT (f : Ident) (args : Array Term) : CommandElabM Term := appT (idT f) args

/-- If `ty` is the type `T p₁ … pₙ idx…` being defined, applied to its parameters, its index
arguments. -/
private def recIdx (tName : Name) (params : Array Ident) (ty : Term) : Option (Array Term) :=
  match ty with
  | `($f:ident $as:term*) =>
    if f.getId == tName && as.size ≥ params.size &&
        (params.zip as).all (fun (p, a) => a.raw.isIdent && a.raw.getId == p.getId) then
      some (as.extract params.size as.size)
    else none
  | `($f:ident) => if params.isEmpty && f.getId == tName then some #[] else none
  | _ => none

/-- A binder `(x y : A)` or `{x y : A}`: its names, type, and whether it is implicit. -/
private def readBinder (b : TSyntax ``bracketedBinder) : CommandElabM (Array Ident × Term × Bool) := do
  let toIdents (ids : TSyntaxArray [`ident, ``Parser.Term.hole]) : CommandElabM (Array Ident) := do
    unless ids.all (·.raw.isIdent) do throwErrorAt b "binders must be named"
    return ids.map fun x => ⟨x.raw⟩
  match b with
  | `(bracketedBinderF| ($ids* : $ty)) => return (← toIdents ids, ty, false)
  | `(bracketedBinderF| {$ids* : $ty}) => return (← toIdents ids, ty, true)
  | _ => throwErrorAt b "unsupported binder: expected an explicit or implicit binder with a type"

/-- A fresh hygienic identifier. -/
private def freshId (s : String) : CommandElabM Ident :=
  return mkIdent (← MonadQuotation.addMacroScope (Name.mkSimple s))

/-- Classify the type of a constructor argument: a plain recursive argument `T params idx`, a
recursive argument under a telescope of arrows ending in one, or non-recursive data, which may
not mention `T` at all. -/
private partial def classify (tName : Name) (params : Array Ident) (ty : Term) :
    CommandElabM Kind := do
  if let some idx := recIdx tName params ty then return .pos idx
  let rec go (t : Term) (acc : Array (Ident × Term)) : CommandElabM (Option Kind) := do
    match t with
    | `($b:bracketedBinder → $cod) =>
      let (ids, dom, _) ← readBinder b
      go cod (acc ++ ids.map (·, dom))
    | `($dom → $cod) =>
      go cod (acc.push (← freshId s!"y{Nat.toSubscriptString (acc.size + 1)}", dom))
    | _ => return (recIdx tName params t).map (.fn acc)
  if let some k ← go ty #[] then
    if let .fn tele _ := k then
      for (_, dom) in tele do
        if mentionsAny dom.raw #[tName] then
          throwErrorAt dom "the type being defined may not occur in the domain of a function"
    return k
  if mentionsAny ty.raw #[tName] then
    throwErrorAt ty "recursive occurrence not recognised: expected the type being defined \
      applied to its parameters (and indices), possibly under arrows"
  return .data

/-- The binders `(y₁ : B₁) … (yₙ : Bₙ)` of a telescope. -/
def teleBinders (tele : Array (Ident × Term)) : CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  tele.mapM fun (y, B) => `(bracketedBinderF| ($y:ident : $B))

def teleIds (tele : Array (Ident × Term)) : Array Ident := tele.map (·.1)

/-- `(y₁ : B₁) → … → (yₙ : Bₙ) → cod`. -/
def mkPi (tele : Array (Ident × Term)) (cod : Term) : CommandElabM Term :=
  tele.foldrM (init := cod) fun (y, B) acc => `(($y:ident : $B) → $acc)

/-- A binder group as a `bracketedBinder`, explicit or implicit as declared. -/
private def mkBinder (implicit : Bool) (ids : Array Ident) (ty : Term) :
    CommandElabM (TSyntax ``bracketedBinderF) :=
  if implicit then `(bracketedBinderF| {$ids* : $ty}) else `(bracketedBinderF| ($ids* : $ty))

/-- Everything the generators need: the analysed declaration, the index telescope if any, the
namespaces of the generic theory to instantiate, and the names of the generated declarations
and the types applied to the parameters. -/
structure Ctx where
  T : Ident
  tName : Name
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
  Tp : Term
  Fp : Term
  Shapep : Term
  Bp : Term
  sigp : Term

/-- The short name of the position constructor for the argument `x` of constructor `c`. -/
def posCtorName (c : CtorInfo) (x : Ident) : Ident :=
  mkIdent (Name.mkSimple (c.name.getId.toString ++ "_" ++ x.getId.toString))

/-- The binders of a constructor, with the user's types. -/
def binders (c : CtorInfo) : CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  c.groups.mapM fun g => mkBinder g.implicit g.ids g.ty

def prime (x : Ident) : Ident := mkIdent (x.getId.appendAfter "'")

/-- The binders of a constructor with primed names. -/
def binders' (c : CtorInfo) : CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  c.groups.mapM fun g => mkBinder g.implicit (g.ids.map prime) g.ty

/-- The binders of a constructor of `F`: recursive types replaced by `X` (at their index). -/
def fBinders (c : CtorInfo) : CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  c.groups.mapM fun g => do
    let ty ← match g.kind with
      | .data => pure g.ty
      | .pos idx => appT (← `(X)) idx
      | .fn tele idx => do mkPi tele (← appT (← `(X)) idx)
    mkBinder g.implicit g.ids ty

/-- The data binders of a constructor, all implicit (for the constructors of `B`, where the
data is determined by the shape). -/
def dataBindersImplicit (c : CtorInfo) : CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  (c.groups.filter (·.kind.isData)).mapM fun g => mkBinder true g.ids g.ty

namespace Ctx

variable (ctx : Ctx)

def fCtor (c : CtorInfo) : Ident := mkIdent (ctx.F.getId ++ c.name.getId)
def shapeCtor (c : CtorInfo) : Ident := mkIdent (ctx.Shape.getId ++ c.name.getId)
def bCtor (c : CtorInfo) (x : Ident) : Ident := mkIdent (ctx.B.getId ++ (posCtorName c x).getId)
def tCtor (c : CtorInfo) : Ident := mkIdent (ctx.tName ++ c.name.getId)
def tName' (c : CtorInfo) (pre post : String) : Ident :=
  mkIdent (ctx.tName ++ Name.mkSimple (pre ++ c.name.getId.toString ++ post))
def nF (s : String) : Ident := mkIdent (.str (.str ctx.tName "F") s)

/-- A declaration of the generic signature theory. -/
def sigId (_ : Ctx) (n : Name) : Ident := mkIdent (`Codata.Signature ++ n)

/-- A declaration derived from the contract. -/
def topId (_ : Ctx) (n : Name) : Ident := mkIdent (`Codata ++ n)

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
  (c.idx.findIdx? fun t => t.raw.isIdent && t.raw.getId == x).map fun m => ctx.iIds[m]!

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

/-- `@Shape.c params data…`, as a term, with the constructor's binders in scope. -/
def shapeApp (c : CtorInfo) : CommandElabM Term := do
  let pTerms := ctx.pTerms
  let ids := c.allDataIds.map idT
  `(@$(ctx.shapeCtor c):ident $pTerms* $ids*)

/-- `@Shape.c params data…`, as a term on the right-hand side of a `match`. -/
def shapeVal (c : CtorInfo) : CommandElabM Term := do
  let pTerms := ctx.pTerms
  let ids := (ctx.valDataIds c).map idT
  `(@$(ctx.shapeCtor c):ident $pTerms* $ids*)

/-- `@Shape.c _ data…`, as a pattern. -/
def shapePat (c : CtorInfo) : CommandElabM Term := do
  let hs ← ctx.pHoles
  let ids ← ctx.patIds c c.allDataIds
  `(@$(ctx.shapeCtor c):ident $hs* $ids*)

/-- The arguments of a constructor of `F` after `map f`, implicit ones included; with
`afterMatch`, in the value form. -/
def mappedArgs (c : CtorInfo) (afterMatch : Bool) : CommandElabM (Array Term) := do
  let holes ← ctx.holes
  let args ← c.groups.mapM fun g => do
    g.ids.mapM fun (x : Ident) => match g.kind with
      | .data => pure (idT (if afterMatch then (ctx.bareIdx c x.getId).getD x else x))
      | .pos _ => `(f $holes* $x:ident)
      | .fn tele _ =>
        let ys := teleIds tele
        `(fun $[$ys:ident]* => f $holes* ($x:ident $ys*))
  return args.foldl (· ++ ·) #[]

end Ctx

open Ctx

/-! ### The functor `F` and its laws -/

def genFunctor (ctx : Ctx) : CommandElabM Unit := do
  let pExp := ctx.pExp
  let pImp := ctx.pImp
  let xTy ← ctx.famTy
  let ib ← ctx.ixB
  let jB ← ctx.jB
  let holes ← ctx.holes
  let jArgs := ctx.jArgs
  let X ← `(X)
  let Y ← `(Y)
  let fTy ← ctx.famFn X Y
  let FX ← ctx.atI (← `($(ctx.Fp) X))
  let FY ← ctx.atI (← `($(ctx.Fp) Y))
  let fCtors ← ctx.ctors.mapM fun c => do
    let bs ← fBinders c
    if ctx.idxed then
      let res ← appT (← `($(ctx.Fp) X)) c.idx
      `(Parser.Command.ctor| | $(c.name):ident $[$bs]* : $res)
    else
      `(Parser.Command.ctor| | $(c.name):ident $[$bs]*)
  if ctx.idxed then
    elabCommand (← `(inductive $(ctx.F):ident $[$pExp]* (X : $xTy) : $xTy where
      $[$fCtors:ctor]*))
  else
    elabCommand (← `(inductive $(ctx.F):ident $[$pExp]* (X : $xTy) where
      $[$fCtors:ctor]*))
  -- `F.map`, and its computation on constructors.
  let mapAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.mapM fun c => do
    ctx.alt c #[← ctx.fPat c] (← ctx.fApp c Y (← ctx.mappedArgs c true))
  let discrsA := ctx.discrs (← `(a))
  elabCommand (← `(def $(ctx.Fmap):ident $[$pImp]* {X Y : $xTy} (f : $fTy) $[$ib]*
      (a : $FX) : $FY := match $[$discrsA:term],* with $mapAlts:matchAlt*))
  for c in ctx.ctors do
    let bs ← fBinders c
    let lhs ← ctx.fApp c X (c.allIds.map idT)
    let rhs ← ctx.fApp c Y (← ctx.mappedArgs c false)
    let FXc ← appT (← `($(ctx.Fp) X)) c.idx
    elabCommand (← `(@[simp] theorem $(ctx.nF ("map_" ++ c.name.getId.toString)):ident
        $[$pImp]* {X Y : $xTy} (f : $fTy) $[$bs]* :
        $(ctx.Fmap) f ($lhs : $FXc) = $rhs := rfl))
  -- `F.Rel`: same constructor, equal non-recursive data, related recursive arguments.
  let relCtors ← ctx.ctors.mapM fun c => do
    let mut bs : Array (TSyntax ``bracketedBinderF) := #[]
    let mut hyps : Array (TSyntax ``bracketedBinderF) := #[]
    let mut xs : Array Term := #[]
    let mut ys : Array Term := #[]
    for g in c.groups do
      match g.kind with
      | .data =>
        bs := bs.push (← mkBinder g.implicit g.ids g.ty)
        xs := xs ++ g.ids.map idT
        ys := ys ++ g.ids.map idT
      | .pos idx =>
        let Xi ← appT X idx
        let Yi ← appT Y idx
        for t in g.ids do
          let t' := prime t
          bs := bs.push (← `(bracketedBinderF| ($t : $Xi)))
          bs := bs.push (← `(bracketedBinderF| ($t' : $Yi)))
          hyps := hyps.push (← `(bracketedBinderF| (_ : R $holes* $t $t')))
          xs := xs.push (idT t)
          ys := ys.push (idT t')
      | .fn tele idx =>
        let Xi ← mkPi tele (← appT X idx)
        let Yi ← mkPi tele (← appT Y idx)
        let ps := teleIds tele
        for t in g.ids do
          let t' := prime t
          bs := bs.push (← `(bracketedBinderF| ($t : $Xi)))
          bs := bs.push (← `(bracketedBinderF| ($t' : $Yi)))
          hyps := hyps.push
            (← `(bracketedBinderF| (_ : ∀ $[$ps:ident]*, R $holes* ($t $ps*) ($t' $ps*))))
          xs := xs.push (idT t)
          ys := ys.push (idT t')
    let lhs ← ctx.fApp c X xs
    let rhs ← ctx.fApp c Y ys
    `(Parser.Command.ctor| | $(c.name):ident $[$bs]* $[$hyps]* : $(ctx.Rel) R $lhs $rhs)
  let relTy ← ctx.famRel X Y
  if ctx.idxed then
    elabCommand (← `(inductive $(ctx.Rel):ident $[$pImp]* {X Y : $xTy} (R : $relTy) :
        ∀ $[$ib]*, $FX → $FY → Prop where
      $[$relCtors:ctor]*))
  else
    elabCommand (← `(inductive $(ctx.Rel):ident $[$pImp]* {X Y : $xTy} (R : $relTy) :
        $FX → $FY → Prop where
      $[$relCtors:ctor]*))
  -- The functor laws.
  let idFn ← if ctx.idxed then `(fun $[$holes]* x => x) else `(id)
  elabCommand (← `(theorem $(ctx.Fmap_id):ident $[$pImp]* {X : $xTy} $[$ib]* (a : $FX) :
      $(ctx.Fmap) $idFn a = a := by
    cases a
    all_goals rfl))
  let gTy ← ctx.famFn Y (← `(Z))
  let jIds := ctx.jIds
  let gf ← if ctx.idxed then `(fun $[$jIds:ident]* x => g $jArgs* (f $jArgs* x)) else `(g ∘ f)
  elabCommand (← `(theorem $(ctx.Fmap_comp):ident $[$pImp]* {X Y Z : $xTy} (g : $gTy)
      (f : $fTy) $[$ib]* (a : $FX) : $(ctx.Fmap) $gf a = $(ctx.Fmap) g ($(ctx.Fmap) f a) := by
    cases a
    all_goals rfl))
  let rTy ← ctx.famRel Y (← `(Z))
  let gTy' ← ctx.famFn X (← `(Z))
  let hTy ← if ctx.idxed then `(∀ $[$jB]* x, R $jArgs* (f $jArgs* x) (g $jArgs* x))
    else `(∀ x, R (f x) (g x))
  elabCommand (← `(theorem $(ctx.Frel_map):ident $[$pImp]* {X Y Z : $xTy}
      (R : $rTy) (f : $fTy) (g : $gTy') $[$ib]* (a : $FX) (h : $hTy) :
      $(ctx.Rel) R ($(ctx.Fmap) f a) ($(ctx.Fmap) g a) := by
    cases a
    all_goals simp only [$(ctx.Fmap):ident]
    all_goals constructor
    all_goals intros
    all_goals apply h))

/-! ### The signature: shapes, positions and their indices -/

def genSignature (ctx : Ctx) : CommandElabM Unit := do
  let pExp := ctx.pExp
  let pImp := ctx.pImp
  let shapeCtors ← ctx.ctors.mapM fun c => do
    let bs ← (c.groups.filter (·.kind.isData)).mapM fun g => mkBinder g.implicit g.ids g.ty
    if ctx.idxed then
      let res ← appT ctx.Shapep c.idx
      `(Parser.Command.ctor| | $(c.name):ident $[$bs]* : $res)
    else
      `(Parser.Command.ctor| | $(c.name):ident $[$bs]*)
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
  let pHoles ← ctx.pHoles
  for c in ctx.ctors do
    let dbs ← dataBindersImplicit c
    let shape ← ctx.shapeApp c
    for g in c.groups do
      match g.kind with
      | .data => pure ()
      | .pos idx =>
        let res ← appT ctx.Bp (c.idx ++ #[shape])
        for x in g.ids do
          bCtors := bCtors.push
            (← `(Parser.Command.ctor| | $(posCtorName c x):ident $[$dbs]* : $res))
          if ctx.idxed then
            let packed ← ctx.pack (idx.map (ctx.substBare c))
            let dataPats ← ctx.patIds c c.allDataIds
            idxAlts := idxAlts.push
              (← ctx.alt c #[← `(_), ← `(@$(ctx.bCtor c x):ident $pHoles* $dataPats*)] packed)
      | .fn tele idx =>
        let res ← appT ctx.Bp (c.idx ++ #[shape])
        let tbs ← teleBinders tele
        let ys := (teleIds tele).map idT
        for x in g.ids do
          bCtors := bCtors.push (← `(Parser.Command.ctor|
            | $(posCtorName c x):ident $[$dbs]* $[$tbs]* : $res))
          if ctx.idxed then
            let packed ← ctx.pack (idx.map (ctx.substBare c))
            let dataPats ← ctx.patIds c c.allDataIds
            idxAlts := idxAlts.push
              (← ctx.alt c #[← `(_), ← `(@$(ctx.bCtor c x):ident $pHoles* $dataPats* $ys*)] packed)
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
    let mut Ix := ctx.idx.back!.2
    for m in [0:ctx.k - 1] do
      let (x, ty) := ctx.idx[ctx.k - 2 - m]!
      Ix ← `(PSigma fun ($x:ident : $ty) => $Ix)
    elabCommand (← `(abbrev $(ctx.Ix):ident $[$pExp]* : Type _ := $Ix))
  let BIs ← appT ctx.Bp (ctx.iArgs ++ #[← `(s)])
  -- The shape is a discriminant too (with the pattern `_`), so that it is refined.
  let discrsB := ctx.discrs (← `(s)) |>.push (← `(b))
  let idxBody ← if idxAlts.isEmpty then `(nomatch b)
    else `(match $[$discrsB:term],* with $idxAlts:matchAlt*)
  elabCommand (← `(def $(ctx.idxId):ident $[$pImp]* $[$ib]* {s : $ShapeI} (b : $BIs) :
      $(ctx.Ixp) := $idxBody))
  if ctx.packed then
    let iPat ← ctx.pack ctx.iArgs
    elabCommand (← `(abbrev $(ctx.sig):ident $[$pExp]* : Codata.Signature where
      I := $(ctx.Ixp)
      Shape := fun p => match p with | $iPat:term => $ShapeI
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
    let shape ← ctx.shapeVal c
    let mut alts : Array (TSyntax ``matchAlt) := #[]
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
    let child ← if alts.isEmpty then `(fun b => nomatch b)
      else `(fun b => match b with $alts:matchAlt*)
    ctx.alt c #[lhs] (← `(⟨$shape, $child⟩))
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
    let rhs ← ctx.fApp c (← `(_)) args
    let pat ← if c.hasRec then `(⟨$shape, ch⟩) else `(⟨$shape, _⟩)
    ctx.alt c #[pat] rhs
  let discrsZ := ctx.discrs (← `(z))
  elabCommand (← `(def $(ctx.ofC):ident $[$pImp]* $[$famBX]* $[$ib]* (z : $ObjX) : $FXi :=
    match $[$discrsZ:term],* with $ofCAlts:matchAlt*))
  elabCommand (← `(theorem $(ctx.ofC_toC):ident $[$pImp]* $[$famBX]* $[$ib]* (a : $FXi) :
      $(ctx.ofC) ($(ctx.toC) a) = a := by
    cases a
    all_goals rfl))
  -- `f : ∀ q, X q → Y q` on the packed index, curried for `F.map`.
  let fTyP ← `(∀ q, X q → Y q)
  let fCur ← ctx.curryN (← `(f)) #[⟨(← `(x)).raw⟩]
  elabCommand (← `(theorem $(ctx.ofC_map):ident $[$pImp]* $[$famB]* (f : $fTyP) $[$ib]*
      (z : $ObjX) : $(ctx.ofC) ($(ctx.sigId `Obj.map) f z) = $(ctx.Fmap) $fCur ($(ctx.ofC) z) := by
    obtain ⟨s, ch⟩ := z
    cases s
    all_goals rfl))
  let relTyP ← `(∀ q, X q → Y q → Prop)
  let RCur ← ctx.curryN (← `(R)) #[]
  elabCommand (← `(theorem $(ctx.rel_ofC):ident $[$pImp]* $[$famB]* (R : $relTyP) $[$ib]*
      (z : $ObjX) (z' : $ObjY) (h : $(ctx.Rel) $RCur ($(ctx.ofC) z) ($(ctx.ofC) z')) :
      $(ctx.sigId `Obj.Rel) R z z' := by
    obtain ⟨s, ch⟩ := z
    obtain ⟨s', ch'⟩ := z'
    cases s
    all_goals cases s'
    all_goals try simp only [$(ctx.ofC):ident] at h
    all_goals cases h
    all_goals refine ⟨_, _, _, rfl, rfl, fun b => ?_⟩
    all_goals cases b
    all_goals solve_by_elim))

/-! ### The contract, and what is derived from it -/

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
  let Cot ← `($(ctx.sigId `Cotype) $(ctx.sigp))
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

def genDerived (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let xTy ← ctx.famTy
  let ib ← ctx.ixB
  let iArgs := ctx.iArgs
  let S := ctx.Sid
  let Ti ← ctx.atI ctx.Tp
  let FTi ← ctx.atI (← `($(ctx.Fp) $(ctx.Tp)))
  let Si ← ctx.atI (idT S)
  let cTy ← ctx.famFn (idT S) (← `($(ctx.Fp) $S))
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
  elabCommand (← `(def $(ctx.ctor):ident $[$pImp]* $[$ib]* : $FTi → $Ti :=
    $(ctx.topId `Contract.ctor) $(ctx.contract) (i := $(cv.pI))))
  elabCommand (← `(theorem $(ctx.dtor_ctor):ident $[$pImp]* $[$ib]* (y : $FTi) :
      $(ctx.dtor) ($(ctx.ctor) y) = y :=
    $(ctx.topId `Contract.dtor_ctor) $(ctx.contract) (i := $(cv.pI)) y))
  elabCommand (← `(theorem $(ctx.ctor_dtor):ident $[$pImp]* $[$ib]* (t : $Ti) :
      $(ctx.ctor) ($(ctx.dtor) t) = t :=
    $(ctx.topId `Contract.ctor_dtor) $(ctx.contract) (i := $(cv.pI)) t))
  elabCommand (← `(theorem $(ctx.ctor_injective):ident $[$pImp]* $[$ib]* :
      Function.Injective ($(ctx.ctor) : $FTi → $Ti) :=
    $(ctx.topId `Contract.ctor_injective) $(ctx.contract) (i := $(cv.pI))))
  -- `corec_eq` and `corec_unique`, for states in any universe.
  let corecFn ← if ctx.k == 0 then `($(ctx.corec) c)
    else `(fun $[$(← ctx.holes)]* s => $(ctx.corec) c s)
  let cs ← appT (← `(c)) (iArgs ++ #[← `(s)])
  elabCommand (← `(theorem $(ctx.corec_eq):ident $[$pImp]* {$S : $xTy} (c : $cTy) $[$ib]*
      (s : $Si) : $(ctx.corec) c s = $(ctx.ctor) ($(ctx.Fmap) $corecFn $cs) :=
    $(ctx.topId `corec_eq_of) (T := $(cv.Tpk)) (S := $(cv.Sp)) (FS := $(cv.FSp)) (FT := $(cv.FTp))
      (i := $(cv.pI)) (fun {_} t => $(ctx.dtor) t) (fun {_} y => $(ctx.ctor) y)
      (fun c {_} s => $(ctx.corec) $(← cur (← `(c)) #[sId]) s) $(cv.map)
      (fun c {_} s => $(ctx.dtor_corec) $(← cur (← `(c)) #[sId]) s) (fun {_} t => $(ctx.ctor_dtor) t)
      $(cv.c) s))
  let hTy ← ctx.famFn (idT S) ctx.Tp
  let ixBExp ← ctx.ixBExp
  let hs ← appT (← `(h)) (iArgs ++ #[← `(s)])
  let hhTy ← `(∀ $[$ixBExp]* (s : $Si), $(ctx.dtor) $hs = $(ctx.Fmap) h $cs)
  elabCommand (← `(theorem $(ctx.corec_unique):ident $[$pImp]* {$S : $xTy} (c : $cTy) (h : $hTy)
      (hh : $hhTy) $[$ib]* (s : $Si) : $hs = $(ctx.corec) c s :=
    $(ctx.topId `corec_unique_of) (T := $(cv.Tpk)) (S := $(cv.Sp)) (FS := $(cv.FSp))
      (FT := $(cv.FTp)) (i := $(cv.pI)) (fun {_} t => $(ctx.dtor) t)
      (fun c {_} s => $(ctx.corec) $(← cur (← `(c)) #[sId]) s) $(cv.map) $(cv.Rel)
      (fun R H {_ _ _} h => $(ctx.bisim) $(← cur (← `(R)) #[]) $Hcur h)
      (fun c {_} s => $(ctx.dtor_corec) $(← cur (← `(c)) #[sId]) s)
      (fun R f g {_} a h => $(ctx.Frel_map) $(← cur (← `(R)) #[]) $(← cur (← `(f)) #[])
        $(← cur (← `(g)) #[]) a $(← cur (← `(h)) #[x]))
      $(cv.c) $(← ctx.uncurryN (← `(h)) #[sId]) $(← ctx.uncurryN (← `(hh)) #[sId]) s))

/-- The individual constructors, with their destructor equations, the `ctor` equations,
injectivity and disjointness (the last two when well-typed). -/
def genCtors (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  for c in ctx.ctors do
    let cId := ctx.tCtor c
    let bs ← binders c
    let fapp ← ctx.fApp c ctx.Tp (c.allIds.map idT)
    let capp ← ctx.tApp c
    let Tc ← appT ctx.Tp c.idx
    let FTc ← appT (← `($(ctx.Fp) $(ctx.Tp))) c.idx
    elabCommand (← `(def $cId:ident $[$pImp]* $[$bs]* : $Tc := $(ctx.ctor) $fapp))
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "dtor_" ""):ident $[$pImp]* $[$bs]* :
        $(ctx.dtor) ($capp : $Tc) = $fapp := $(ctx.dtor_ctor) $fapp))
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "ctor_" ""):ident $[$pImp]* $[$bs]* :
        $(ctx.ctor) ($fapp : $FTc) = $capp := rfl))
  for c in ctx.ctors do
    if c.args.isEmpty || c.hasImplicit || c.idxDependent then continue
    let bs ← binders c
    let bs' ← binders' c
    let Tc ← appT ctx.Tp c.idx
    let capp ← mkAppT (ctx.tCtor c) (c.args.map idT)
    let capp' ← mkAppT (ctx.tCtor c) ((c.args.map prime).map idT)
    let eqs ← (c.args.zip (c.args.map prime)).mapM fun (x, x') => `($x:ident = $x':ident)
    let conj ← eqs.foldrM (init := eqs.back!) (start := eqs.size - 1) fun e acc => `($e ∧ $acc)
    let injEq := mkIdent (ctx.F.getId ++ c.name.getId ++ `injEq)
    let fapp ← mkAppT (ctx.fCtor c) (c.args.map idT)
    let fapp' ← mkAppT (ctx.fCtor c) ((c.args.map prime).map idT)
    let args := c.args.map idT ++ (c.args.map prime).map idT
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "" "_inj"):ident $[$pImp]* $[$bs]*
        $[$bs']* : ($capp : $Tc) = $capp' ↔ $conj :=
      Codata.inj_of $(ctx.ctor) $(ctx.ctor_injective) $fapp $fapp' ($injEq $args:term*)))
  for c in ctx.ctors do
    for c' in ctx.ctors do
      if c.name.getId == c'.name.getId then continue
      unless idxEq c.idx c'.idx && !c.idxDependent && !c'.idxDependent do continue
      let bs ← binders c
      let bs' ← binders' c'
      let Tc ← appT ctx.Tp c.idx
      let capp ← mkAppT (ctx.tCtor c) (c.args.map idT)
      let capp' ← mkAppT (ctx.tCtor c') ((c'.args.map prime).map idT)
      let name := mkIdent (ctx.tName ++
        Name.mkSimple (c.name.getId.toString ++ "_ne_" ++ c'.name.getId.toString))
      let dtorC ← mkAppT (ctx.tName' c "dtor_" "") (c.args.map idT)
      let dtorC' ← mkAppT (ctx.tName' c' "dtor_" "") ((c'.args.map prime).map idT)
      elabCommand (← `(@[simp] theorem $name:ident $[$pImp]* $[$bs]* $[$bs']* :
          ($capp : $Tc) ≠ $capp' :=
        Codata.ne_of $(ctx.dtor) $dtorC $dtorC' fun h => nomatch h))

/-- Case analysis: `t = ctor (dtor t)`, and `dtor t` is an inductive value. -/
def genCases (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let pTerms := ctx.pTerms
  let ib ← ctx.ixB
  let jB ← ctx.jB
  let iArg := ctx.iArg
  let motive := ctx.motiveId
  let mTy ← if ctx.idxed then `(∀ $[$jB]*, $(← appT ctx.Tp ctx.jArgs) → Sort _)
    else `($(ctx.Tp) → Sort _)
  let mI ← appT (idT motive) iArg
  let Ti ← ctx.atI ctx.Tp
  let FTi ← ctx.atI (← `($(ctx.Fp) $(ctx.Tp)))
  let minors ← ctx.ctors.mapM fun c => do
    let bs ← binders c
    let capp ← ctx.tApp c
    let mc ← appT (idT motive) c.idx
    let ty ← if c.groups.isEmpty then `($mc $capp) else `(∀ $[$bs]*, $mc $capp)
    `(bracketedBinderF| ($(c.name) : $ty))
  let auxAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.mapM fun c => do
    ctx.alt c #[← ctx.fPat c] (← mkAppT c.name ((ctx.valArgs c).map idT))
  let discrsY := ctx.discrs (← `(y))
  elabCommand (← `(def $(ctx.casesOnAux):ident $[$pImp]* {$motive : $mTy} $[$ib]* (y : $FTi)
      $[$minors]* : $mI ($(ctx.ctor) y) := match $[$discrsY:term],* with $auxAlts:matchAlt*))
  let minorIds := ctx.ctors.map fun c => idT c.name
  elabCommand (← `(@[elab_as_elim, cases_eliminator]
    def $(ctx.casesOnId):ident $[$pImp]* {$motive : $mTy} $[$ib]* (t : $Ti) $[$minors]* :
        $mI t :=
      (congrArg $mI ($(ctx.ctor_dtor) t)).mp ($(ctx.casesOnAux) ($(ctx.dtor) t) $minorIds:term*)))
  -- Its computation rules: the cast disappears once `dtor (ctor y) = y` is substituted.
  elabCommand (← `(theorem $(ctx.casesOn_ctor):ident $[$pImp]* {$motive : $mTy} $[$ib]*
      (y : $FTi) $[$minors]* :
      @$(ctx.casesOnId) $pTerms:term* $motive $iArg:term* ($(ctx.ctor) y) $minorIds:term* =
        $(ctx.casesOnAux) y $minorIds:term* :=
    Codata.cast_ctor_dtor $(ctx.ctor) $(ctx.dtor) $(ctx.ctor_dtor) $(ctx.dtor_ctor)
      (fun y => $(ctx.casesOnAux) y $minorIds:term*) y))
  for c in ctx.ctors do
    let bs ← binders c
    let capp ← ctx.tApp c
    let fapp ← ctx.fApp c ctx.Tp (c.allIds.map idT)
    let rhs ← mkAppT c.name (c.args.map idT)
    let cidx := c.idx
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "casesOn_" ""):ident $[$pImp]*
        {$motive : $mTy} $[$bs]* $[$minors]* :
        @$(ctx.casesOnId) $pTerms:term* $motive $cidx:term* $capp $minorIds:term* = $rhs :=
      $(ctx.casesOn_ctor) $fapp $minorIds:term*))

/-! ### The command -/

/-- The index telescope of a declared sort `(i₁ : I₁) → I₂ → … → Type u`: names (fresh when
the arrow is not dependent) and types. -/
private partial def readSort (t : Term) : CommandElabM (Array (Ident × Term)) := do
  match t with
  | `($b:bracketedBinder → $cod) =>
    let (ids, ty, _) ← readBinder b
    return ids.map (·, ty) ++ (← readSort cod)
  | `($dom → $cod) =>
    let rest ← readSort cod
    return #[(← freshId s!"i{Nat.toSubscriptString (rest.size + 1)}", dom)] ++ rest
  | _ => return #[]

@[command_elab codataCmd] def elabCodata : CommandElab := fun stx => do
  let `(codata $T:ident $paramsStx:bracketedBinder* $[: $sortStx]? $ctorsStx:codataCtor*) := stx
    | throwUnsupportedSyntax
  let tName := T.getId
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
  let idx ← idx0.mapIdxM fun m (x, ty) => do
    if x.getId.hasMacroScopes then return (← freshId s!"i{Nat.toSubscriptString (m + 1)}", ty)
    else return (x, ty)
  let nIdx := idx.size
  let ctors : Array CtorInfo ← ctorsStx.mapM fun c => do
    let `(codataCtor| | $name:ident $bs:bracketedBinder* $[: $resTy]?) := c
      | throwUnsupportedSyntax
    let raw ← bs.mapM readBinder
    let groups ← raw.mapM fun (ids, ty, implicit) => do
      return { ids, ty, kind := ← classify tName pids ty, implicit : Group }
    for g in groups do
      if g.implicit && !g.kind.isData then
        throwErrorAt g.ty "implicit binders must not be recursive"
      unless g.kind.isData || g.kind.idx.size == nIdx do
        throwErrorAt g.ty "recursive argument with the wrong number of indices"
    let cidx ← match resTy with
      | none =>
        if nIdx > 0 then throwErrorAt c "the constructor needs a result type" else pure #[]
      | some r =>
        match recIdx tName pids r with
        | some cidx =>
          if cidx.size == nIdx then pure cidx
          else throwErrorAt r "result type with the wrong number of indices"
        | none => throwErrorAt r "the result type must be the declared type applied to its parameters"
    return { name, groups, idx := cidx }
  let n (s : String) : Ident := mkIdent (.str tName s)
  let nF (s : String) : Ident := mkIdent (.str (.str tName "F") s)
  let pTerms := pids.map idT
  -- Names the user may refer to: plain unless the declaration uses them.
  let used : Array Name := pids.map (·.getId) ++ idx.map (·.1.getId) ++ ctors.foldl (fun acc c =>
    acc.push c.name.getId ++ c.groups.foldl (fun acc g => acc ++ g.ids.map (·.getId)) #[]) #[]
  let plainOr (n : Name) (hyg : Ident) : Ident := if used.contains n then hyg else mkIdent n
  let motiveId := plainOr `motive ⟨(← `(motive)).raw⟩
  let Sid := plainOr `S ⟨(← `(S)).raw⟩
  let jIds ← idx.mapIdxM fun m _ => freshId s!"j{Nat.toSubscriptString (m + 1)}"
  let Ixp ← if nIdx ≥ 2 then mkAppT (n "Ix") pTerms
    else if nIdx == 1 then pure idx[0]!.2 else `(Unit)
  let ctx : Ctx := {
    T, tName, pids, pExp, pImp, pTerms, ctors, idx, jIds, Ixp, motiveId, Sid
    Ix := n "Ix", idxId := n "idx", F := n "F", Shape := n "Shape", B := n "B", sig := n "sig"
    Fmap := nF "map", Rel := nF "Rel"
    Fmap_id := nF "map_id", Fmap_comp := nF "map_comp", Frel_map := nF "rel_map"
    toC := n "toC", ofC := n "ofC"
    ofC_toC := n "ofC_toC", ofC_map := n "ofC_map", rel_ofC := n "rel_ofC"
    dtor := n "dtor", corec := n "corec", dtor_corec := n "dtor_corec", bisim := n "bisim"
    contract := n "contract", ctor := n "ctor", dtor_ctor := n "dtor_ctor"
    ctor_dtor := n "ctor_dtor", ctor_injective := n "ctor_injective"
    corec_eq := n "corec_eq", corec_unique := n "corec_unique"
    casesOnAux := n "casesOnAux", casesOnId := n "casesOn", casesOn_ctor := n "casesOn_ctor"
    Tp := ← mkAppT T pTerms, Fp := ← mkAppT (n "F") pTerms, Shapep := ← mkAppT (n "Shape") pTerms
    Bp := ← mkAppT (n "B") pTerms, sigp := ← mkAppT (n "sig") pTerms }
  genFunctor ctx
  genSignature ctx
  genIso ctx
  -- The encoding decides equality of shapes classically: the type's corecursor and constructors
  -- are noncomputable.
  elabCommand (← `(noncomputable section))
  genContract ctx
  genDerived ctx
  genCtors ctx
  genCases ctx
  elabCommand (← `(end))

end Codata
