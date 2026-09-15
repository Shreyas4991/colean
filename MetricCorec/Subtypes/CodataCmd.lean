import MetricCorec.Subtypes.Codata
import MetricCorec.Subtypes.Container
import MetricCorec.Subtypes.Param

/-!
# The `codata` command

Current scope: parameters, a single type or a mutual block, any number of indices. Constructor
binders may be explicit or implicit; recursive arguments may be plain (`t : T params idx`),
under a telescope of arrows (`f : (y₁ : B₁) → … → Bₙ → T params idx`), dependent or not, where
the domains may depend on the constructor's own data and the index on the bound variables, or
nested through a container (`children : List (T params idx)`, see `Container.lean`). A data
binder may not mention `T`. When the last parameter is a type `α`, or a family `X : J → Type u`,
used only at parameter positions (`(a : α)`, `(f : A → α)`, `(as : G α)` through a container
`G`; `(t : X j)`, …), the type is itself a container in it (see `Param.lean`), so that later
declarations may nest through it: `children : Forest (T params idx)` through a declared
`Forest`, or `children : Forest (fun p => T params (idx p))` through a declared `Forest` with a
family parameter (an indexed container, `IContainer`), which is what mixed `mutual` blocks
elaborate to (`MutualCmd.lean`).

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
* the signature: `T.Shape` (the constructors with their non-recursive data only, plus the shape
  `x_s` of each nested argument `x`) and `T.B : T.Shape → Type`, the positions for recursive
  arguments, one nullary constructor `ctorᵢ_t` per plain argument `t`, one unary constructor
  `ctorᵢ_f (p : A)` per function argument `f : A → T` and one `ctorᵢ_x (q : Pos x_s)` per nested
  argument; bundled as `T.sig`;
* with a container parameter `α`: the erased shapes `T.Shape₀` (the shapes without the
  arguments at parameter positions, plus the shape of each container `G α`), the parameter
  positions `T.P : T.Shape₀ → Type`, one constructor `ctorᵢ_a` per argument `(a : α)`,
  `ctorᵢ_f (y : A)` per `(f : A → α)` and `ctorᵢ_as (q : Pos as_s)` per `(as : G α)`, the
  equivalence `T.shapeEquiv : T.Shape α ≃ Σ s₀, T.P s₀ → α` (by `T.shapeTo`/`T.shapeOf`), the
  parameterised signature `T.psig` (`T.B` is then over `T.Shape₀`, `T.sig := T.psig.sig …`),
  and after the type the container `T.Sh`, `T.Pos` and
  `instance : Container (fun α => T params α idx) T.Sh T.Pos`; for a family parameter
  `X : J → Type u`, also the positions' indices `T.pidx : T.P s₀ → J`, `T.posIdx` and
  `instance : IContainer (fun X => T params X idx) T.Sh T.Pos T.posIdx`;
* `T.toC`, `T.ofC` with the four laws `T.ofC_toC`, `T.toC_ofC`, `T.ofC_map`, `T.rel_ofC`;
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

Only the seven lemmas about the generated inductive `T.F` (`map_id`, `map_comp`, `rel_map`,
`ofC_toC`, `toC_ofC`, `ofC_map`, `rel_ofC`) are proved by tactic scripts, and those are `cases`
followed by `rfl` or `solve_by_elim`, with the laws of `Container.lean` for nested arguments;
everything else instantiates a theorem of `Codata.lean`.
The declarations from `T` on are generated in a `noncomputable section`, since the encoding
decides equality of shapes classically.

The analysis of the declaration (`mkCtx`) and the generators of `T.F`, the signature, the
isomorphism, the constructors and `casesOn` are shared with the `data` command
(`DataCmd.lean`), which differs only in the contract and what is derived from it; `T.F.Rel`,
`rel_map` and `rel_ofC` are generated for `codata` only. A mutual block (`MutualCmd.lean`) is
one family whose first index enumerates its types: `mkCtx` receives the types with their
constructors and the enumeration, every generator works on the block, and the user-facing
types, constructors, `casesOn` and aliases are per type (`genTypes`, `genCases`, `genAliases`).
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
  /-- A nested recursive argument `G (T params idx)` through a container `G` (`List`, `Option`,
  `A × ·`, …), with the shapes and positions of its `Container` instance; or, with `fam`, a
  nested occurrence of the family `G (fun p => T params idx)` through an indexed container,
  where `idx` mention `p` and `fam` is `p` with the container's position index `pidx`. -/
  | nest (G Sh Pos : Term) (fam : Option (Ident × Term)) (idx : Array Term)

/-- How a non-recursive argument uses the container parameter (the last parameter, when it is
a type variable `α`): not at all, as its type `α`, under a telescope `(y₁ : B₁) → … → α`, or
through a container `G α`. When every argument uses `α` in one of these ways, the declared type
is a container in `α`: its erased shapes `Shape₀` are the non-recursive data without these
arguments (plus the shapes of the containers), and its parameter positions `P` are these
arguments, one constructor each. -/
inductive PKind where
  | none
  /-- `X j` (`j` is `()` for a type parameter). -/
  | val (j : Term)
  | fn (tele : Array (Ident × Term)) (j : Term)
  | nest (G Sh Pos : Term) (j : Term)

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
  | .nest _ _ _ _ idx => idx

def Kind.isNest : Kind → Bool
  | .nest .. => true
  | _ => false

/-- A nested occurrence of the family, through an indexed container. -/
def Kind.isFam : Kind → Bool
  | .nest _ _ _ (some _) _ => true
  | _ => false

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

/-- A nested occurrence `G (T params idx)`, or of the family `G (fun p => T params idx)`: the
type constructor `G` (the head applied to the other arguments, as a lambda when the occurrence
is not the last argument, or `Prod A` for `A × T params idx`), the family variable `p` if any,
and the full index arguments. -/
def nestedOcc (tNames : Array Name) (blk : Name) (pre : Nat → Array Term)
    (params : Array Ident) (ty : Term) :
    CommandElabM (Option (Term × Option Ident × Array Term)) := do
  let names := tNames.push blk
  let occ (t : Term) : Option (Option Ident × Array Term) :=
    match recOcc tNames blk pre params (stripParen t) with
    | some idx => some (none, idx)
    | none =>
      match stripParen t with
      | `(fun $p:ident => $body) => (recOcc tNames blk pre params (stripParen body)).map (some p, ·)
      | `(fun ($p:ident : $_) => $body) =>
        (recOcc tNames blk pre params (stripParen body)).map (some p, ·)
      | _ => none
  match ty with
  | `($a × $b) =>
    match occ b with
    | some (fam, idx) => return some (← `(Prod $a), fam, idx)
    | none => return none
  | `($f:ident $as:term*) =>
    if as.isEmpty || names.contains f.getId then return none
    let ks := (Array.range as.size).filter fun k => mentionsAny as[k]!.raw names
    if ks.size != 1 then return none
    let k := ks[0]!
    match occ as[k]! with
    | some (fam, idx) =>
      let G ← if k == as.size - 1 then
          if as.size == 1 then pure (idT f) else `($f $(as.pop)*)
        else do
          let Xv ← freshId "X"
          `(fun $Xv:ident => $f $(as.set! k (idT Xv))*)
      return some (G, fam, idx)
    | none => return none
  | _ => return none

/-- The shapes and positions of the container `G`, from its `Codata.Container` instance (or,
with `fam`, the shapes, positions and position index of its `Codata.IContainer` instance), as
syntax (delaborated, in the scope of the parameters); `none` without an instance. -/
def containerOf? (pExp : Array (TSyntax ``bracketedBinderF)) (G : Term) (fam : Bool := false) :
    CommandElabM (Option (Term × Term × Option Term)) :=
  liftTermElabM do
    Term.elabBinders pExp fun _ => do
      let cls ← Term.elabTerm (← if fam then `(Codata.IContainer $G _ _ _)
        else `(Codata.Container $G _ _)) none
      Term.synthesizeSyntheticMVarsNoPostponing
      let cls ← instantiateMVars cls
      let some _ ← Meta.synthInstance? cls | return none
      let cls ← instantiateMVars cls
      let args := cls.getAppArgs
      if fam then
        unless args.size == 5 do throwError "unexpected form of the container class: {cls}"
        return some (← PrettyPrinter.delab args[2]!, ← PrettyPrinter.delab args[3]!,
          some (← PrettyPrinter.delab args[4]!))
      unless args.size == 3 do throwError "unexpected form of the container class: {cls}"
      return some (← PrettyPrinter.delab args[1]!, ← PrettyPrinter.delab args[2]!, none)

/-- Classify the type of a constructor argument: a plain recursive argument `T params idx`, a
recursive argument under a telescope of arrows ending in one, a nested one `G (T params idx)`
(or `G (fun p => T params idx)` through an indexed container), or non-recursive data, which
may not mention the types being defined at all. `pre m` is the block index of the `m`-th type
(its constructor of `Which`, nothing outside mutual blocks), prepended to the index arguments;
`blk` is the block family, which nested occurrences may mention directly. -/
private partial def classify (tNames : Array Name) (blk : Name) (params : Array Ident)
    (pExp : Array (TSyntax ``bracketedBinderF)) (pre : Nat → Array Term) (ty : Term) :
    CommandElabM Kind := do
  let names := tNames.push blk
  if let some idx := recOcc tNames blk pre params ty then return .pos idx
  if let some (G, fam, idx) ← nestedOcc tNames blk pre params ty then
    if mentionsAny G.raw names then
      throwErrorAt ty "a type being defined may occur only as one argument of a container"
    let some (Sh, Pos, pidx) ← containerOf? pExp G fam.isSome
      | throwErrorAt G "no `Codata.Container` instance for the type constructor `{G}`; \
          nested occurrences are supported through `List`, `Option`, `A × ·`, the types \
          declared by `data` and `codata` with a type parameter, and any type constructor \
          with such an instance (`Codata.IContainer` for a family)"
    let fam := match fam, pidx with
      | some p, some pidx => some (p, pidx)
      | _, _ => none
    return .nest G Sh Pos fam idx
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
  if mentionsAny ty.raw names then
    throwErrorAt ty "recursive occurrence not recognised: expected a type being defined \
      applied to its parameters (and indices), possibly under arrows"
  return .data

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

/-- How the type `ty` of a non-recursive argument uses the parameter `a` (a family when `fam`):
`.none` when it does not occur, `.val j`, `.fn tele j` or `.nest G Sh Pos j` for the recognised
forms `a j`, `(y₁ : B₁) → … → a j`, `G (a j)` (just `a` for a type parameter, with `j := ()`;
the domains of the telescope, the container and the index `j` must not mention `a`), and no
result otherwise. -/
private partial def classifyParam (a : Ident) (fam : Bool)
    (pExp : Array (TSyntax ``bracketedBinderF)) (ty : Term) : CommandElabM (Option PKind) := do
  let an := #[a.getId]
  let ty := stripParen ty
  unless mentionsAny ty.raw an do return some .none
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
  let withJ (j : Term) (G : Term) : Option (Term × Term) := some (G, j)
  let G? : Option (Term × Term) ← match ty with
    | `($a' × $b) =>
      match occA b with
      | some j => if mentionsAny a'.raw an then pure none else withJ j <$> `(Prod $a')
      | none => pure none
    | `($f:ident $as:term*) =>
      match (if as.isEmpty then none else occA as.back!) with
      | some j =>
        if mentionsAny f.raw an || as.pop.any (mentionsAny ·.raw an) then pure none
        else withJ j <$> (if as.size == 1 then pure (idT f) else `($f $(as.pop)*))
      | none => pure none
    | _ => pure none
  let some (G, j) := G? | return none
  let some (Sh, Pos, _) ← containerOf? pExp G | return none
  return some (.nest G Sh Pos j)

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

/-- `t`, or `fun p => t` for a nested occurrence of the family. -/
def famApp (fam : Option (Ident × Term)) (t : Term) : CommandElabM Term :=
  match fam with
  | none => pure t
  | some (p, _) => `(fun $p:ident => $t)

/-- The container's namespace, `Codata.Container` or `Codata.IContainer` for a family. -/
def contId (fam : Bool) (n : Name) : Ident :=
  mkIdent ((if fam then `Codata.IContainer else `Codata.Container) ++ n)

/-- The binders of a constructor of `F`: recursive types replaced by `X` (at their index). -/
def fBinders (c : CtorInfo) : CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  c.groups.mapM fun g => do
    let ty ← match g.kind with
      | .data => pure g.ty
      | .pos idx => appT (← `(X)) idx
      | .fn tele idx => do mkPi tele (← appT (← `(X)) idx)
      | .nest G _ _ fam idx => do appT G #[← famApp fam (← appT (← `(X)) idx)]
    mkBinder g.implicit g.ids ty

/-- The shape binder of a nested argument `x`: `x_s`, the shape of the container value. -/
def nestShapeId (x : Ident) : Ident := mkIdent (x.getId.appendAfter "_s")

/-- A nested argument: its name, its container's shapes and positions, the family variable
and position index if it nests the family, and its full index (mentioning the family variable).
-/
structure NestInfo where
  x : Ident
  G : Term
  Sh : Term
  Pos : Term
  fam : Option (Ident × Term)
  idx : Array Term

/-- The nested arguments of a constructor. -/
def CtorInfo.nested (c : CtorInfo) : Array NestInfo :=
  c.groups.foldl (init := #[]) fun acc g => match g.kind with
    | .nest G Sh Pos fam idx => acc ++ g.ids.map fun x => { x, G, Sh, Pos, fam, idx }
    | _ => acc

/-- The shape binders `(x_s : Sh)` of the nested arguments. -/
def nestShapeBinders (c : CtorInfo) (implicit : Bool) :
    CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  c.nested.mapM fun n => mkBinder implicit #[nestShapeId n.x] n.Sh

/-- The index of the recursive position `q` of the nested argument `n` (at the shape `xs`): its
index, with the family variable replaced by the position's index. -/
def nestIdxAt (n : NestInfo) (xs : Term) (q : Term) : CommandElabM (Array Term) := do
  match n.fam with
  | none => pure n.idx
  | some (p, pidx) =>
    let at_ ← `($pidx $xs $q)
    return n.idx.map fun t => ⟨substTerms t.raw fun m => if m == p.getId then some at_ else none⟩

/-- The arguments through a container in the parameter, with the container's shapes and
positions. -/
def CtorInfo.pnested (c : CtorInfo) : Array (Ident × Term × Term) :=
  c.groups.foldl (init := #[]) fun acc g => match g.pk with
    | .nest _ Sh Pos _ => acc ++ g.ids.map (·, Sh, Pos)
    | _ => acc

/-- The shape binders `(x_s : Sh)` of the arguments through a container in the parameter. -/
def pnestShapeBinders (c : CtorInfo) (implicit : Bool) :
    CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  c.pnested.mapM fun (x, Sh, _) => mkBinder implicit #[nestShapeId x] Sh

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

/-- The container `G` of a nested argument, after a `match` (index binders for the binders
that are indices) or with the constructor's binders in scope. The container is passed
explicitly to `toC`, `ofC`, `map`, `Rel`: it is a lambda when the nested occurrence is not the
last argument, which unification would not find. -/
def nestG (c : CtorInfo) (G : Term) (afterMatch : Bool) : Term :=
  if afterMatch then ctx.substBare c G else G

/-- The shapes of the nested arguments, as values: `(Container.toC x).1` (after a `match`). -/
def nestShapeVals (c : CtorInfo) : CommandElabM (Array Term) :=
  c.nested.mapM fun n => `(($(contId n.fam.isSome `toC) (G := $(ctx.nestG c n.G true)) $(n.x)).1)

/-- The shapes of the nested arguments as their binders `x_s`. -/
def nestShapeIds (c : CtorInfo) : Array Term := c.nested.map fun n => idT (nestShapeId n.x)

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

/-- The shapes of the containers in the parameter, as values: `(Container.toC x).1`. -/
def pnestShapeVals (c : CtorInfo) : CommandElabM (Array Term) :=
  c.pnested.mapM fun (x, _, _) => `((Codata.Container.toC $x).1)

/-- The shapes of the containers in the parameter as their binders `x_s`. -/
def pnestShapeIds (c : CtorInfo) : Array Term := c.pnested.map fun (x, _, _) => idT (nestShapeId x)

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
the container laws. -/
def hasNest : Bool := ctx.ctors.any fun c => c.groups.any (·.kind.isNest)

/-- The arguments of a constructor of `F` after `map f`, implicit ones included; with
`afterMatch`, in the value form. `app` applies the function to a recursive argument and `fn` is
the function itself, for nested arguments (by default `f _ _ x` and `f _ _`, for
`f : ∀ j₁ j₂, X j₁ j₂ → Y j₁ j₂`). -/
def mappedArgs (c : CtorInfo) (afterMatch : Bool) (app : Option (Term → CommandElabM Term) := none)
    (fn : Option Term := none) : CommandElabM (Array Term) := do
  let holes ← ctx.holes
  let app := app.getD fun x => `(f $holes* $x)
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
      | .nest G _ _ none _ =>
        let G := ctx.nestG c G afterMatch
        `(Codata.Container.map (G := $G) (G' := $G) $fn $x:ident)
      | .nest G _ _ (some _) _ =>
        let G := ctx.nestG c G afterMatch
        `(Codata.IContainer.map (G := $G) (G' := $G) (fun _ => $fn) $x:ident)
  return args.foldl (· ++ ·) #[]

end Ctx

open Ctx

/-! ### The functor `F` and its laws -/

/-- `F.Rel`, the lifting to relations, and `F.rel_map`; for `codata` only. -/
def genRel (ctx : Ctx) : CommandElabM Unit := do
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
      | .nest G _ _ fam idx =>
        let Xi ← appT G #[← famApp fam (← appT X idx)]
        let Yi ← appT G #[← famApp fam (← appT Y idx)]
        for t in g.ids do
          let t' := prime t
          bs := bs.push (← `(bracketedBinderF| ($t : $Xi)))
          bs := bs.push (← `(bracketedBinderF| ($t' : $Yi)))
          hyps := hyps.push (← if fam.isSome then
              `(bracketedBinderF| (_ : Codata.IContainer.Rel (G := $G) (G' := $G) (fun _ => R $holes*) $t $t'))
            else `(bracketedBinderF| (_ : Codata.Container.Rel (G := $G) (G' := $G) (R $holes*) $t $t')))
          xs := xs.push (idT t)
          ys := ys.push (idT t')
    let lhs ← ctx.fApp c X xs
    let rhs ← ctx.fApp c Y ys
    `(Parser.Command.ctor| | $(c.fname):ident $[$bs]* $[$hyps]* : $(ctx.Rel) R $lhs $rhs)
  let relTy ← ctx.famRel X Y
  if ctx.idxed then
    elabCommand (← `(inductive $(ctx.Rel):ident $[$pImp]* {X Y : $xTy} (R : $relTy) :
        ∀ $[$ib]*, $FX → $FY → Prop where
      $[$relCtors:ctor]*))
  else
    elabCommand (← `(inductive $(ctx.Rel):ident $[$pImp]* {X Y : $xTy} (R : $relTy) :
        $FX → $FY → Prop where
      $[$relCtors:ctor]*))
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
    all_goals first | apply h | (apply Codata.Container.rel_map; intro; apply h) | (apply Codata.IContainer.rel_map; intro; intro; apply h)))

def genFunctor (ctx : Ctx) : CommandElabM Unit := do
  let pExp := ctx.pExp
  let pImp := ctx.pImp
  let xTy ← ctx.famTy
  let ib ← ctx.ixB
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
      `(Parser.Command.ctor| | $(c.fname):ident $[$bs]* : $res)
    else
      `(Parser.Command.ctor| | $(c.fname):ident $[$bs]*)
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
    elabCommand (← `(@[simp] theorem $(ctx.nF ("map_" ++ c.fname.getId.toString)):ident
        $[$pImp]* {X Y : $xTy} (f : $fTy) $[$bs]* :
        $(ctx.Fmap) f ($lhs : $FXc) = $rhs := rfl))
  -- The functor laws.
  let idFn ← if ctx.idxed then `(fun $[$holes]* x => x) else `(id)
  elabCommand (← `(theorem $(ctx.Fmap_id):ident $[$pImp]* {X : $xTy} $[$ib]* (a : $FX) :
      $(ctx.Fmap) $idFn a = a := by
    cases a
    all_goals first | rfl | simp only [$(ctx.Fmap):ident, id_eq, Codata.Container.map_id, Codata.Container.map_id', Codata.IContainer.map_id, Codata.IContainer.map_id']))
  let gTy ← ctx.famFn Y (← `(Z))
  let jIds := ctx.jIds
  let gf ← if ctx.idxed then `(fun $[$jIds:ident]* x => g $jArgs* (f $jArgs* x)) else `(g ∘ f)
  elabCommand (← `(theorem $(ctx.Fmap_comp):ident $[$pImp]* {X Y Z : $xTy} (g : $gTy)
      (f : $fTy) $[$ib]* (a : $FX) : $(ctx.Fmap) $gf a = $(ctx.Fmap) g ($(ctx.Fmap) f a) := by
    cases a
    all_goals first | rfl | simp only [$(ctx.Fmap):ident, Codata.Container.map_map, Codata.IContainer.map_map, Function.comp_def]))
  if ctx.co then genRel ctx

/-! ### The signature: shapes, positions and their indices

With a container parameter `α`, the signature is a parameterised one, `PSignature`: the erased
shapes `Shape₀` (the data without the parameter positions), the parameter positions `P`, the
recursive positions `B` and their indices over the erased shapes, and `sig = psig.sig Shape e`
with the equivalence `e : Shape ≃ Σ s₀, P s₀ → α` (by `shapeTo`/`shapeOf`); the type is then
a container in `α` by the generic `PSignature.container`. -/

/-- The erased shapes `Shape₀`, the parameter positions `P`, and the equivalence
`Shape ≃ Σ s₀, P s₀ → α` by `shapeTo`, `shapeOf` and their two laws (proved as `ofC_toC` and
`toC_ofC` are). -/
def genParamShapes (ctx : Ctx) : CommandElabM Unit := do
  let some pinfo := ctx.param | return
  let a := pinfo.a
  let pExp := ctx.pExp
  let pExp₀ := ctx.pExp₀
  let pImp := ctx.pImp
  let pImp₀ := ctx.pImp₀
  let ib ← ctx.ixB
  let ixBExp ← ctx.ixBExp
  let shape₀Ctors ← ctx.ctors.mapM fun c => do
    let bs := (← (c.groups.filter fun g => g.kind.isData && g.pk.isNone).mapM fun g =>
        mkBinder g.implicit g.ids g.ty)
      ++ (← nestShapeBinders c false) ++ (← pnestShapeBinders c false)
    if ctx.idxed then
      let res ← appT ctx.Shape₀p c.idx
      `(Parser.Command.ctor| | $(c.fname):ident $[$bs]* : $res)
    else
      `(Parser.Command.ctor| | $(c.fname):ident $[$bs]*)
  if ctx.idxed then
    elabCommand (← `(inductive $(ctx.Shape₀):ident $[$pExp₀]* : ∀ $[$ixBExp]*, Type _ where
      $[$shape₀Ctors:ctor]*))
  else
    elabCommand (← `(inductive $(ctx.Shape₀):ident $[$pExp₀]* where $[$shape₀Ctors:ctor]*))
  -- The parameter positions, one constructor per argument at one.
  let mut pCtors : Array (TSyntax ``Parser.Command.ctor) := #[]
  for c in ctx.ctors do
    let dbs ← dataBindersImplicit c
    let res ← appT ctx.Pp (c.idx ++ #[← ctx.shape₀App c])
    for (x, pk) in c.ppos do
      match pk with
      | .none => pure ()
      | .val _ =>
        pCtors := pCtors.push (← `(Parser.Command.ctor| | $(posCtorName c x):ident $[$dbs]* : $res))
      | .fn tele _ =>
        let tbs ← teleBinders tele
        pCtors := pCtors.push (← `(Parser.Command.ctor|
          | $(posCtorName c x):ident $[$dbs]* $[$tbs]* : $res))
      | .nest _ _ Pos _ =>
        let xs := nestShapeId x
        pCtors := pCtors.push (← `(Parser.Command.ctor|
          | $(posCtorName c x):ident $[$dbs]* (q : $Pos $xs) : $res))
  let Shape₀I ← ctx.atI ctx.Shape₀p
  if ctx.idxed then
    elabCommand (← `(inductive $(ctx.P):ident $[$pExp₀]* : ∀ $[$ixBExp]*, $Shape₀I → Type _ where
      $[$pCtors:ctor]*))
  else
    elabCommand (← `(inductive $(ctx.P):ident $[$pExp₀]* : $Shape₀I → Type _ where
      $[$pCtors:ctor]*))
  let ShapeI ← ctx.atI ctx.Shapep
  let PI ← ctx.atI ctx.Pp
  -- For a family: the index of every parameter position.
  if let some J := pinfo.J then
    let mut pAlts : Array (TSyntax ``matchAlt) := #[]
    for c in ctx.ctors do
      for (x, pk) in c.ppos do
        match pk with
        | .none => pure ()
        | .val j =>
          pAlts := pAlts.push (← ctx.alt c #[← `(_), ← ctx.pPat c x #[]] (ctx.substBare c j))
        | .fn tele j =>
          let ys := (teleIds tele).map idT
          pAlts := pAlts.push (← ctx.alt c #[← `(_), ← ctx.pPat c x ys] (ctx.substBare c j))
        | .nest _ _ _ j =>
          pAlts := pAlts.push
            (← ctx.alt c #[← `(_), ← ctx.pPat c x #[← `(q)]] (ctx.substBare c j))
    let discrsP := ctx.discrs (← `(s₀)) |>.push (← `(p))
    let body ← if pAlts.isEmpty then `(nomatch p)
      else `(match $[$discrsP:term],* with $pAlts:matchAlt*)
    elabCommand (← `(def $(ctx.pidxId):ident $[$pImp₀]* $[$ib]* {s₀ : $Shape₀I} (p : $PI s₀) :
        $J := $body))
  -- The equivalence: a shape is its erased shape with the values at the parameter positions.
  let sigmaTy ← if pinfo.J.isSome then `(Σ s₀ : $Shape₀I, (p : $PI s₀) → $a ($(ctx.pidxId) p))
    else `(Σ s₀ : $Shape₀I, $PI s₀ → $a)
  let pId ← freshId "p"
  let vId ← freshId "v"
  let toAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.mapM fun c => do
    let lhs ← ctx.shapePat c
    -- The layers of the containers in the parameter are bound by a lambda, as in `toC`.
    let zs : Array Ident ← c.pnested.mapM fun (x, _, _) => freshId s!"z_{x.getId.toString}"
    let shape₀ ← ctx.shape₀ValWith c (← zs.mapM fun z => `($z:ident.1))
    let mut alts : Array (TSyntax ``matchAlt) := #[]
    let mut k := 0
    for (x, pk) in c.ppos do
      match pk with
      | .none => pure ()
      | .val _ => alts := alts.push (← `(matchAltExpr| | $(ctx.pCtor c x):ident => $x:ident))
      | .fn tele _ =>
        let ys := teleIds tele
        alts := alts.push (← `(matchAltExpr| | $(ctx.pCtor c x):ident $ys* => $x:ident $ys*))
      | .nest .. =>
        let z := zs[k]!
        k := k + 1
        alts := alts.push (← `(matchAltExpr| | $(ctx.pCtor c x):ident q => $z:ident.2 q))
    let vals ← if alts.isEmpty then `(fun $pId:ident => nomatch $pId:ident)
      else `(fun $pId:ident => match $pId:ident with $alts:matchAlt*)
    let layer ← `(⟨$shape₀, $vals⟩)
    let rhs ← if zs.isEmpty then pure layer else do
      let toCs ← c.pnested.mapM fun (x, _, _) => `(Codata.Container.toC $x:ident)
      `((fun $[$zs:ident]* => $layer) $toCs*)
    ctx.alt c #[lhs] rhs
  let discrsS := ctx.discrs (← `(s))
  elabCommand (← `(def $(ctx.shapeTo):ident $[$pImp]* $[$ib]* (s : $ShapeI) : $sigmaTy :=
    match $[$discrsS:term],* with $toAlts:matchAlt*))
  let ofAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.mapM fun c => do
    let shape₀ ← ctx.shape₀Pat c
    let mut args : Array Term := #[]
    for g in c.groups do
      if g.kind.isData then
        for x in g.ids do
          match g.pk with
          | .none => args := args.push (idT ((ctx.bareIdx c x.getId).getD x))
          | .val _ => args := args.push (← `($vId $(ctx.pCtor c x)))
          | .fn tele _ =>
            let ys := teleIds tele
            args := args.push (← `(fun $[$ys:ident]* => $vId ($(ctx.pCtor c x) $ys*)))
          | .nest .. =>
            let xs := nestShapeId x
            args := args.push
              (← `(Codata.Container.ofC ⟨$xs, fun q => $vId ($(ctx.pCtor c x) q)⟩))
    let pTerms := ctx.pTerms
    let ns := nestShapeIds c
    let rhs ← `(@$(ctx.shapeCtor c):ident $pTerms* $args* $ns*)
    let pat ← if c.ppos.isEmpty then `(⟨$shape₀, _⟩) else `(⟨$shape₀, $vId⟩)
    ctx.alt c #[pat] rhs
  let discrsZ := ctx.discrs (← `(z))
  elabCommand (← `(def $(ctx.shapeOf):ident $[$pImp]* $[$ib]* (z : $sigmaTy) : $ShapeI :=
    match $[$discrsZ:term],* with $ofAlts:matchAlt*))
  let pnest := ctx.ctors.any fun c => !c.pnested.isEmpty
  let seq (tacs : Array (TSyntax `tactic)) : CommandElabM (TSyntax ``Parser.Tactic.tacticSeq) :=
    `(tacticSeq| $[$tacs:tactic]*)
  let pf₁ ← seq (#[← `(tactic| cases s)] ++ (← if pnest then
      return #[← `(tactic| all_goals first | rfl | simp only [$(ctx.shapeTo):ident, $(ctx.shapeOf):ident, Codata.Container.ofC_toC'])]
    else return #[← `(tactic| all_goals rfl)]))
  elabCommand (← `(theorem $(ctx.shapeOf_shapeTo):ident $[$pImp]* $[$ib]* (s : $ShapeI) :
      $(ctx.shapeOf) ($(ctx.shapeTo) s) = s := by $pf₁))
  let pf₂ ← seq (#[← `(tactic| obtain ⟨s, v⟩ := z), ← `(tactic| cases s)] ++
    (← if pnest then
      return #[← `(tactic| all_goals try simp only [$(ctx.shapeTo):ident, $(ctx.shapeOf):ident]),
        ← `(tactic| all_goals repeat rw [Codata.Container.toC_ofC])]
    else return #[]) ++
    #[← `(tactic| all_goals refine congrArg (Sigma.mk _) (funext fun p => ?_)),
      ← `(tactic| all_goals cases p), ← `(tactic| all_goals rfl)])
  elabCommand (← `(theorem $(ctx.shapeTo_shapeOf):ident $[$pImp]* $[$ib]* (z : $sigmaTy) :
      $(ctx.shapeTo) ($(ctx.shapeOf) z) = z := by $pf₂))
  elabCommand (← `(def $(ctx.shapeEquiv):ident $[$pExp]* $[$ixBExp]* : $ShapeI ≃ $sigmaTy :=
    ⟨$(ctx.shapeTo), $(ctx.shapeOf), $(ctx.shapeOf_shapeTo), $(ctx.shapeTo_shapeOf)⟩))

/-- The packed index type `(i₁ : I₁) ×' (i₂ : I₂) ×' …` of an index telescope. -/
def mkIxTerm (idx : Array (Ident × Term)) : CommandElabM Term := do
  let mut Ix := idx.back!.2
  for m in [0:idx.size - 1] do
    let (x, ty) := idx[idx.size - 2 - m]!
    Ix ← `(PSigma fun ($x:ident : $ty) => $Ix)
  return Ix

def genSignature (ctx : Ctx) : CommandElabM Unit := do
  let pExp := ctx.pExp
  let pExp₀ := ctx.pExp₀
  let pImp₀ := ctx.pImp₀
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
  genParamShapes ctx
  -- The positions are over the erased shapes when there is a container parameter.
  let Shape₀p := if ctx.hasParam then ctx.Shape₀p else ctx.Shapep
  let Shape₀Pp := if ctx.hasParam then ctx.Shape₀Pp else ctx.ShapePp
  -- The positions, one constructor per recursive argument; and (indexed) their indices.
  let mut bCtors : Array (TSyntax ``Parser.Command.ctor) := #[]
  let mut idxAlts : Array (TSyntax ``matchAlt) := #[]
  for c in ctx.ctors do
    let dbs ← dataBindersImplicit c
    let shape ← if ctx.hasParam then ctx.shape₀App c else ctx.shapeApp c
    let res ← appT ctx.Bp (c.idx ++ #[shape])
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
      | .nest G Sh Pos fam idx =>
        for x in g.ids do
          let xs := nestShapeId x
          bCtors := bCtors.push (← `(Parser.Command.ctor|
            | $(posCtorName c x):ident $[$dbs]* (q : $Pos $xs) : $res))
          if ctx.idxed then
            let idx ← nestIdxAt { x, G, Sh, Pos, fam, idx } (idT xs) (← `(q))
            let packed ← ctx.pack (idx.map (ctx.substBare c))
            idxAlts := idxAlts.push (← ctx.alt c #[← `(_), ← ctx.bPat c x #[← `(q)]] packed)
  if !ctx.idxed then
    -- A plain type is a family over `Unit`.
    elabCommand (← `(inductive $(ctx.B):ident $[$pExp₀]* : $Shape₀p → Type _ where
      $[$bCtors:ctor]*))
    if let some pinfo := ctx.param then
      let (J, pidx) ← ctx.psigJ
      elabCommand (← `(abbrev $(ctx.psig):ident $[$pExp₀]* : Codata.PSignature where
        I := Unit
        J := $J
        Shape₀ := fun _ => $Shape₀p
        P := fun s => $(ctx.Pp) s
        pidx := $pidx
        B := fun _ s => $(ctx.Bp) s
        idx := fun _ => ()))
      let (S, e) ← ctx.sigSE
      elabCommand (← `(abbrev $(ctx.sig):ident $[$pExp]* : Codata.Signature :=
        Codata.PSignature.sig $(ctx.psigp) (X := $(← famX pinfo)) $S $e))
    else
      elabCommand (← `(abbrev $(ctx.sig):ident $[$pExp]* : Codata.Signature where
        I := Unit
        Shape := fun _ => $(ctx.Shapep)
        Shape₀ := fun _ => $(ctx.Shapep)
        sh₀ := fun s => s
        B := fun _ s => $(ctx.Bp) s
        idx := fun _ => ()))
    return
  let ShapeI ← ctx.atI ctx.Shapep
  let Shape₀I ← ctx.atI Shape₀p
  elabCommand (← `(inductive $(ctx.B):ident $[$pExp₀]* : ∀ $[$ixBExp]*, $Shape₀I → Type _ where
    $[$bCtors:ctor]*))
  if ctx.packed then
    elabCommand (← `(abbrev $(ctx.Ix):ident $[$pExp₀]* : Type _ := $(← mkIxTerm ctx.idx)))
  let BIs ← appT ctx.Bp (ctx.iArgs ++ #[← `(s)])
  -- The shape is a discriminant too (with the pattern `_`), so that it is refined.
  let discrsB := ctx.discrs (← `(s)) |>.push (← `(b))
  let idxBody ← if idxAlts.isEmpty then `(nomatch b)
    else `(match $[$discrsB:term],* with $idxAlts:matchAlt*)
  elabCommand (← `(def $(ctx.idxId):ident $[$pImp₀]* $[$ib]* {s : $Shape₀I} (b : $BIs) :
      $(ctx.Ixp) := $idxBody))
  if ctx.packed then
    let iPat ← ctx.pack ctx.iArgs
    -- The shapes on the packed index, named once so that `Shape` and `Shape₀` coincide.
    elabCommand (← `(def $(ctx.ShapeP):ident $[$pExp]* (p : $(ctx.Ixp)) : Type _ :=
      match p with | $iPat:term => $ShapeI))
    if let some pinfo := ctx.param then
      elabCommand (← `(def $(ctx.Shape₀P):ident $[$pExp₀]* (p : $(ctx.Ixp)) : Type _ :=
        match p with | $iPat:term => $Shape₀I))
      let PIs ← appT ctx.Pp (ctx.iArgs ++ #[← `(s)])
      let (J, _) ← ctx.psigJ
      let pidx ← if pinfo.J.isSome then
          `(fun {p} {s} q => match p, s, q with | $iPat:term, s, q => $(ctx.pidxId) q)
        else `(fun _ => ())
      elabCommand (← `(abbrev $(ctx.psig):ident $[$pExp₀]* : Codata.PSignature where
        I := $(ctx.Ixp)
        J := $J
        Shape₀ := $Shape₀Pp
        P := fun {p} s => match p, s with | $iPat:term, s => $PIs
        pidx := $pidx
        B := fun p s => match p, s with | $iPat:term, s => $BIs
        idx := fun {p} {s} b => match p, s, b with | $iPat:term, s, b => $(ctx.idxId) b))
      let (S, e) ← ctx.sigSE
      elabCommand (← `(abbrev $(ctx.sig):ident $[$pExp]* : Codata.Signature :=
        Codata.PSignature.sig $(ctx.psigp) (X := $(← famX pinfo)) $S $e))
    else
      elabCommand (← `(abbrev $(ctx.sig):ident $[$pExp]* : Codata.Signature where
        I := $(ctx.Ixp)
        Shape := $(ctx.ShapePp)
        Shape₀ := $(ctx.ShapePp)
        sh₀ := fun s => s
        B := fun p s => match p, s with | $iPat:term, s => $BIs
        idx := fun {p} {s} b => match p, s, b with | $iPat:term, s, b => $(ctx.idxId) b))
  else if let some pinfo := ctx.param then
    let (J, pidx) ← ctx.psigJ
    elabCommand (← `(abbrev $(ctx.psig):ident $[$pExp₀]* : Codata.PSignature where
      I := $(ctx.Ixp)
      J := $J
      Shape₀ := $Shape₀p
      P := fun s => $(ctx.Pp) _ s
      pidx := $pidx
      B := $(ctx.Bp)
      idx := fun b => $(ctx.idxId) b))
    let (S, e) ← ctx.sigSE
    elabCommand (← `(abbrev $(ctx.sig):ident $[$pExp]* : Codata.Signature :=
      Codata.PSignature.sig $(ctx.psigp) (X := $(← famX pinfo)) $S $e))
  else
    elabCommand (← `(abbrev $(ctx.sig):ident $[$pExp]* : Codata.Signature where
      I := $(ctx.Ixp)
      Shape := $(ctx.Shapep)
      Shape₀ := $(ctx.Shapep)
      sh₀ := fun s => s
      B := $(ctx.Bp)
      idx := fun b => $(ctx.idxId) b))

/-! ### The container instance, with a container parameter -/

/-- For every type of the declaration, its shapes `T.Sh` (the erased trees), its positions
`T.Pos` (a path to a node and a parameter position of its erased shape) and the instance
`Container (fun α => T params α idx) T.Sh T.Pos`, from the generic `PSignature.container`
(`cocontainer` for `codata`). -/
def genContainer (ctx : Ctx) : CommandElabM Unit := do
  let some pinfo := ctx.param | return
  let a := pinfo.a
  let aTy := pinfo.aTy
  let pExp₀ := ctx.pExp₀
  let pTerms₀ := ctx.pTerms₀
  let ixBExp ← ctx.uIxBExp
  let uIArgs := ctx.uIArgs
  let (S, e) ← ctx.sigSE
  let fam := ctx.sigId (if ctx.co then `Cotype else `Intype)
  for m in [0:ctx.types.size] do
    let pI ← ctx.pack (ctx.fullArgs m)
    let Sh := ctx.tyId m "Sh"
    let Pos := ctx.tyId m "Pos"
    elabCommand (← `(abbrev $Sh:ident $[$pExp₀]* $[$ixBExp]* : Type _ :=
      $fam (Codata.PSignature.sig₀ $(ctx.psigp)) $pI))
    let Shp ← appT (← mkAppT Sh pTerms₀) uIArgs
    elabCommand (← `(abbrev $Pos:ident $[$pExp₀]* $[$ixBExp]* (sh : $Shp) : Type _ :=
      Codata.PSignature.Pos $(ctx.psigp) sh.1))
    let Posp ← appT (← mkAppT Pos pTerms₀) uIArgs
    let Tm ← ctx.tyAtU m
    if let some J := pinfo.J then
      let PosIdx := ctx.tyId m "posIdx"
      elabCommand (← `(abbrev $PosIdx:ident $[$pExp₀]* $[$ixBExp]* (sh : $Shp) (x : $Posp sh) :
        $J := Codata.PSignature.Pos.idx x))
      let PosIdxp ← appT (← mkAppT PosIdx pTerms₀) uIArgs
      let cont := ctx.topId (if ctx.co then `PSignature.icocontainer else `PSignature.icontainer)
      elabCommand (← `(instance $[$pExp₀]* $[$ixBExp]* :
          Codata.IContainer (fun ($a:ident : $aTy) => $Tm) $Shp $Posp $PosIdxp :=
        $cont (ψ := $(ctx.psigp)) (fun ($a:ident : $aTy) => $S) (fun ($a:ident : $aTy) => $e) $pI))
    else
      let cont := ctx.topId (if ctx.co then `PSignature.cocontainer else `PSignature.container)
      elabCommand (← `(instance $[$pExp₀]* $[$ixBExp]* :
          Codata.Container (fun ($a:ident : $aTy) => $Tm) $Shp $Posp :=
        $cont (ψ := $(ctx.psigp)) (fun ($a:ident : $aTy) => $S) (fun ($a:ident : $aTy) => $e) $pI))

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
    -- The layers `Container.toC x` of the nested arguments are bound by a lambda, so that the
    -- inner `match` is parametric in them and `toC_ofC` can rewrite them.
    let zs : Array Ident ← c.nested.mapM fun n => freshId s!"z_{n.x.getId.toString}"
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
      | .nest .. =>
        for x in g.ids do
          let z := zs[k]!
          k := k + 1
          alts := alts.push (← `(matchAltExpr| | $(ctx.bCtor c x):ident q => $z:ident.2 q))
    let child ← if alts.isEmpty then `(fun b => nomatch b)
      else `(fun b => match b with $alts:matchAlt*)
    let layer ← `(⟨$shape, $child⟩)
    let rhs ← if zs.isEmpty then pure layer else do
      let toCs ← c.nested.mapM fun n =>
        `($(contId n.fam.isSome `toC) (G := $(ctx.nestG c n.G true)) $(n.x):ident)
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
        | .nest G _ _ fam _ =>
          let xs := nestShapeId x
          args := args.push (← `($(contId fam.isSome `ofC) (G := $(ctx.nestG c G true))
            ⟨$xs, fun q => ch ($(ctx.bCtor c x) q)⟩))
    let rhs ← ctx.fApp c (← `(_)) args
    let pat ← if c.hasRec then `(⟨$shape, ch⟩) else `(⟨$shape, _⟩)
    ctx.alt c #[pat] rhs
  let discrsZ := ctx.discrs (← `(z))
  elabCommand (← `(def $(ctx.ofC):ident $[$pImp]* $[$famBX]* $[$ib]* (z : $ObjX) : $FXi :=
    match $[$discrsZ:term],* with $ofCAlts:matchAlt*))
  -- With nested arguments the layers go through the container's isomorphism, and its laws
  -- finish what `rfl` no longer can.
  let nested := ctx.hasNest
  let seq (tacs : Array (TSyntax `tactic)) : CommandElabM (TSyntax ``Parser.Tactic.tacticSeq) :=
    `(tacticSeq| $[$tacs:tactic]*)
  let ofC_toC_pf ← seq (#[← `(tactic| cases a)] ++ (← if nested then
      return #[← `(tactic| all_goals first | rfl | simp only [$(ctx.toC):ident, $(ctx.ofC):ident, Codata.Container.ofC_toC', Codata.IContainer.ofC_toC'])]
    else return #[← `(tactic| all_goals rfl)]))
  elabCommand (← `(theorem $(ctx.ofC_toC):ident $[$pImp]* $[$famBX]* $[$ib]* (a : $FXi) :
      $(ctx.ofC) ($(ctx.toC) a) = a := by $ofC_toC_pf))
  let toC_ofC_pf ← seq (#[← `(tactic| obtain ⟨s, ch⟩ := z), ← `(tactic| cases s)] ++
    (← if nested then
      -- The container's shape is in a dependent position (the type of the children), which
      -- `simp` cannot rewrite; `rw` can, one nested argument at a time.
      return #[← `(tactic| all_goals try simp only [$(ctx.toC):ident, $(ctx.ofC):ident]),
        ← `(tactic| all_goals repeat rw [Codata.Container.toC_ofC]),
        ← `(tactic| all_goals repeat rw [Codata.IContainer.toC_ofC])]
    else return #[]) ++
    #[← `(tactic| all_goals refine congrArg (Codata.Signature.Obj.mk _) (funext fun b => ?_)),
      ← `(tactic| all_goals cases b), ← `(tactic| all_goals rfl)])
  elabCommand (← `(theorem $(ctx.toC_ofC):ident $[$pImp]* $[$famBX]* $[$ib]* (z : $ObjX) :
      $(ctx.toC) ($(ctx.ofC) z) = z := by $toC_ofC_pf))
  -- `f : ∀ q, X q → Y q` on the packed index, curried for `F.map`.
  let fTyP ← `(∀ q, X q → Y q)
  let fCur ← ctx.curryN (← `(f)) #[⟨(← `(x)).raw⟩]
  let ofC_map_pf ← seq (#[← `(tactic| obtain ⟨s, ch⟩ := z), ← `(tactic| cases s)] ++
    (← if nested then
      return #[← `(tactic| all_goals first | rfl | simp only [$(ctx.ofC):ident, $(ctx.Fmap):ident, Codata.Signature.Obj.map, Codata.Container.map_ofC, Codata.IContainer.map_ofC])]
    else return #[]) ++
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
              if kind.isNest then
                -- `rfl` must be the keyword pattern, not a hygienic name.
                let rflPat := mkIdent `rfl
                let relOfC := contId kind.isFam `rel_ofC
                steps := steps.push
                  (← `(tactic| obtain ⟨$rflPat:ident, $h:ident⟩ := $relOfC $h))
          let all := steps ++ tail
          `(tactic| · $[$all:tactic]*)
        seq (common ++ bullets)
      else
        seq (common ++ #[← `(tactic| all_goals refine ⟨_, _, _, rfl, rfl, fun b => ?_⟩),
          ← `(tactic| all_goals cases b), ← `(tactic| all_goals solve_by_elim)])
    elabCommand (← `(theorem $(ctx.rel_ofC):ident $[$pImp]* $[$famB]* (R : $relTyP) $[$ib]*
        (z : $ObjX) (z' : $ObjY) (h : $(ctx.Rel) $RCur ($(ctx.ofC) z) ($(ctx.ofC) z')) :
        $(ctx.sigId `Obj.Rel) R z z' := by $rel_ofC_pf))

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
    let Tc ← ctx.tyAt c
    let FTc ← appT (← `($(ctx.Fp) $(ctx.Tp))) c.idx
    elabCommand (← `(def $cId:ident $[$pImp]* $[$bs]* : $Tc := $(ctx.ctor) $fapp))
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "dtor_" ""):ident $[$pImp]* $[$bs]* :
        $(ctx.dtor) ($capp : $Tc) = $fapp := $(ctx.dtor_ctor) $fapp))
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "ctor_" ""):ident $[$pImp]* $[$bs]* :
        $(ctx.ctor) ($fapp : $FTc) = $capp := rfl))
  for c in ctx.ctors do
    if c.args.isEmpty || c.hasImplicit || c.dependent || c.idxDependent then continue
    let bs ← binders c
    let bs' ← binders' c
    let Tc ← ctx.tyAt c
    let capp ← mkAppT (ctx.tCtor c) (c.args.map idT)
    let capp' ← mkAppT (ctx.tCtor c) ((c.args.map prime).map idT)
    let eqs ← (c.args.zip (c.args.map prime)).mapM fun (x, x') => `($x:ident = $x':ident)
    let conj ← eqs.foldrM (init := eqs.back!) (start := eqs.size - 1) fun e acc => `($e ∧ $acc)
    let injEq := mkIdent (ctx.F.getId ++ c.fname.getId ++ `injEq)
    let fapp ← mkAppT (ctx.fCtor c) (c.args.map idT)
    let fapp' ← mkAppT (ctx.fCtor c) ((c.args.map prime).map idT)
    let args := c.args.map idT ++ (c.args.map prime).map idT
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "" "_inj"):ident $[$pImp]* $[$bs]*
        $[$bs']* : ($capp : $Tc) = $capp' ↔ $conj :=
      Codata.inj_of $(ctx.ctor) $(ctx.ctor_injective) $fapp $fapp' ($injEq $args:term*)))
  for c in ctx.ctors do
    for c' in ctx.ctors do
      if c.name.getId == c'.name.getId || c.owner != c'.owner then continue
      unless idxEq c.idx c'.idx && !c.idxDependent && !c'.idxDependent do continue
      let bs ← binders c
      let bs' ← binders' c'
      let Tc ← ctx.tyAt c
      let capp ← mkAppT (ctx.tCtor c) (c.args.map idT)
      let capp' ← mkAppT (ctx.tCtor c') ((c'.args.map prime).map idT)
      let name := mkIdent (ctx.tyName c.owner ++
        Name.mkSimple (c.name.getId.toString ++ "_ne_" ++ c'.name.getId.toString))
      let dtorC ← mkAppT (ctx.tName' c "dtor_" "") (c.args.map idT)
      let dtorC' ← mkAppT (ctx.tName' c' "dtor_" "") ((c'.args.map prime).map idT)
      elabCommand (← `(@[simp] theorem $name:ident $[$pImp]* $[$bs]* $[$bs']* :
          ($capp : $Tc) ≠ $capp' :=
        Codata.ne_of $(ctx.dtor) $dtorC $dtorC' fun h => nomatch h))

/-- Case analysis, per type of the block: `t = ctor (dtor t)`, and `dtor t` is an inductive
value whose possible constructors are those of the type. -/
def genCases (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let pTerms := ctx.pTerms
  let ib ← ctx.uIxB
  let jB ← ctx.uJB
  let iArg := ctx.uIArgs
  let motive := ctx.motiveId
  for m in [0:ctx.types.size] do
    let ctors := ctx.ctors.filter (·.owner == m)
    let Tm ← ctx.tyP m
    let mTy ← if ctx.uIdxed then `(∀ $[$jB]*, $(← appT Tm ctx.uJArgs) → Sort _)
      else `($Tm → Sort _)
    let mI ← appT (idT motive) iArg
    let Ti ← ctx.tyAtU m
    let FTi ← appT (← `($(ctx.Fp) $(ctx.Tp))) (ctx.fullArgs m)
    let casesOnAux := ctx.tyId m "casesOnAux"
    let casesOnId := ctx.tyId m "casesOn"
    let casesOn_ctor := ctx.tyId m "casesOn_ctor"
    let minors ← ctors.mapM fun c => do
      let bs ← binders c
      let capp ← ctx.tApp c
      let mc ← appT (idT motive) (ctx.uIdxOf c)
      let ty ← if c.groups.isEmpty then `($mc $capp) else `(∀ $[$bs]*, $mc $capp)
      `(bracketedBinderF| ($(c.name) : $ty))
    let auxAlts : Array (TSyntax ``matchAlt) ← ctors.mapM fun c => do
      ctx.uAlt c #[← ctx.fPat c] (← mkAppT c.name ((ctx.valArgs c).map idT))
    let discrsY := ctx.uDiscrs (← `(y))
    elabCommand (← `(def $casesOnAux:ident $[$pImp]* {$motive : $mTy} $[$ib]* (y : $FTi)
        $[$minors]* : $mI ($(ctx.ctor) y) := match $[$discrsY:term],* with $auxAlts:matchAlt*))
    let minorIds := ctors.map fun c => idT c.name
    elabCommand (← `(@[elab_as_elim, cases_eliminator]
      def $casesOnId:ident $[$pImp]* {$motive : $mTy} $[$ib]* (t : $Ti) $[$minors]* :
          $mI t :=
        (congrArg $mI ($(ctx.ctor_dtor) t)).mp ($casesOnAux ($(ctx.dtor) t) $minorIds:term*)))
    -- Its computation rules: the cast disappears once `dtor (ctor y) = y` is substituted.
    elabCommand (← `(theorem $casesOn_ctor:ident $[$pImp]* {$motive : $mTy} $[$ib]*
        (y : $FTi) $[$minors]* :
        @$casesOnId $pTerms:term* $motive $iArg:term* ($(ctx.ctor) y) $minorIds:term* =
          $casesOnAux y $minorIds:term* :=
      Codata.cast_ctor_dtor $(ctx.ctor) $(ctx.dtor) $(ctx.ctor_dtor) $(ctx.dtor_ctor)
        (fun y => $casesOnAux y $minorIds:term*) y))
    for c in ctors do
      let bs ← binders c
      let capp ← ctx.tApp c
      let fapp ← ctx.fApp c ctx.Tp (c.allIds.map idT)
      let rhs ← mkAppT c.name (c.args.map idT)
      let cidx := ctx.uIdxOf c
      elabCommand (← `(@[simp] theorem $(ctx.tName' c "casesOn_" ""):ident $[$pImp]*
          {$motive : $mTy} $[$bs]* $[$minors]* :
          @$casesOnId $pTerms:term* $motive $cidx:term* $capp $minorIds:term* = $rhs :=
        $casesOn_ctor $fapp $minorIds:term*))

/-! ### Mutual blocks: the user-facing types and aliases -/

/-- In a mutual block, the user-facing types: `Tₘ params i… := Blk params .Tₘ i…`. Defined
after the family and before anything that mentions the types in a binder. -/
def genTypes (ctx : Ctx) : CommandElabM Unit := do
  unless ctx.isMutual do return
  let pExp := ctx.pExp
  let ixBExp ← ctx.uIxBExp
  for m in [0:ctx.types.size] do
    let body ← appT ctx.Tp (ctx.fullArgs m)
    elabCommand (← `(def $(ctx.types[m]!):ident $[$pExp]* $[$ixBExp]* : Type _ := $body))

/-- In a mutual `codata` block, the block-level `corec` and `bisim` restricted to each type.
`dtor` and `ctor` are not aliased: dot notation `t.dtor` resolves to the block-level `dtor`
through the definition of the type, and an alias at the head of a lemma would not be seen
through by `rw`. -/
def genAliases (ctx : Ctx) : CommandElabM Unit := do
  unless ctx.isMutual do return
  let pImp := ctx.pImp
  let xTy ← ctx.famTy
  let ixBExp ← ctx.ixBExp
  let iArgs := ctx.iArgs
  let S := ctx.Sid
  let cTy ← ctx.famFn (idT S) (← `($(ctx.Fp) $S))
  let RTy ← ctx.famRel ctx.Tp ctx.Tp
  let Rixy ← appT (← `(R)) (iArgs ++ #[← `(x), ← `(y)])
  let HTy ← `(∀ $[$ixBExp]* x y, $Rixy → $(ctx.Rel) R ($(ctx.dtor) x) ($(ctx.dtor) y))
  let ib ← ctx.uIxB
  for m in [0:ctx.types.size] do
    let Ti ← ctx.tyAtU m
    let Si ← appT (idT S) (ctx.fullArgs m)
    let Rm ← appT (← `(R)) (ctx.fullArgs m ++ #[← `(x), ← `(y)])
    elabCommand (← `(abbrev $(ctx.tyId m "corec"):ident $[$pImp]* {$S : $xTy} (c : $cTy) $[$ib]*
        (s : $Si) : $Ti := $(ctx.corec) c s))
    elabCommand (← `(theorem $(ctx.tyId m "bisim"):ident $[$pImp]* (R : $RTy) (H : $HTy) $[$ib]*
        {x y : $Ti} (h : $Rm) : x = y := $(ctx.bisim) R H h))

/-! ### The command -/

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
  let mut ctors : Array CtorInfo := #[]
  for m in [0:rawCtors.size] do
    for (name, raw, resTy, c) in rawCtors[m]! do
      let mut groups : Array Group := #[]
      -- The scope of a binder's type: the parameters and the earlier non-recursive binders
      -- (the container of a nested argument may mention them).
      let mut scope := pExp
      for (ids, ty, implicit) in raw do
        let kind ← classify tNames tName pids scope pre ty
        if kind.isData then scope := scope.push (← mkBinder implicit ids ty)
        let mut pk := PKind.none
        if let some pinfo := paramCand then
          match kind with
          | .data =>
            match ← classifyParam pinfo.a pinfo.J.isSome pExp ty with
            | some k => pk := k
            | none => pOk := false
          | .pos idx => if idx.any mentionsA then pOk := false
          | .fn tele idx =>
            if idx.any mentionsA || tele.any (fun (_, d) => mentionsA d) then pOk := false
          | .nest G _ _ _ idx => if mentionsA G || idx.any mentionsA then pOk := false
        groups := groups.push { ids, ty, kind, implicit, pk }
      for g in groups do
        if g.implicit && !g.kind.isData then
          throwErrorAt g.ty "implicit binders must not be recursive"
        unless g.kind.isData || g.kind.idx.size == nIdx do
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
  let n (s : String) : Ident := mkIdent (.str tName s)
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

/-- The generators of `codata`, in order. The encoding decides equality of shapes classically:
the type's corecursor and constructors are noncomputable. -/
def codataPipeline (ctx : Ctx) : CommandElabM Unit := do
  genFunctor ctx
  genSignature ctx
  genIso ctx
  elabCommand (← `(noncomputable section))
  genContract ctx
  genTypes ctx
  genDerived ctx
  genCtors ctx
  genCases ctx
  genAliases ctx
  genContainer ctx
  elabCommand (← `(end))

@[command_elab codataCmd] def elabCodata : CommandElab := fun stx => do
  let `(codata $T:ident $paramsStx:bracketedBinder* $[: $sortStx]? $ctorsStx:codataCtor*) := stx
    | throwUnsupportedSyntax
  codataPipeline (← mkCtx true T paramsStx sortStx #[(T, ctorsStx)] none)

end Codata
