import Colean.Gen.Occ

/-!
# Generators on `Expr`: the context

*Spec.* The context `Ctx` is what the analysis of a declaration (`Gen/Front.lean`) gives every
generator: the parameters, the types being defined, the index binders, the constructors with
their arguments classified (`ArgKind`: data, plain recursive, recursive under a telescope,
nested with its occurrence structure), and the names of the generated declarations.

*Free variables.* A context lives inside one `TermElabM` run, in the continuation of
`Gen.withCtx`: the parameters, the index binders and the arguments of every constructor are free
variables of the local context, and every `Expr` of the context is over them. A generator builds
types and values with these variables directly (`mkAppN F (params ++ …)`) and closes a
declaration once, with `mkForallFVars`/`mkLambdaFVars`, choosing binder infos per declaration
(`withBinderInfo`): parameters are explicit in the generated types and implicit in lemmas. The
arguments of different constructors coexist in the local context; they are never elaborated
against, so their names do not capture anything. The section variables the declaration uses are
the first parameters (`nVars` of them), as with `inductive`; they keep their own binder infos in
the generated types, where the declared parameters (`declParams`) are explicit.

*Occurrences.* During the analysis the types being defined are local variables
`T : ∀ params idx, Type uT` (as in Lean's `inductive`), at a placeholder universe `uT` that is a
universe parameter of no declaration. The argument types keep these variables. A generator
replaces the occurrences `T params idx` by what it needs (`replaceOcc`: `X idx` for `T.F`) and
`uT` by the universe of the replacement, which also re-instantiates the universes of the leaves
(`List.{uT} (T α)` becomes `List.{u_1} (X)`). The constructors may fix the universe instead, by
nesting through a type constructor at one universe (`E Nat T` with `E : Type → Type → Type`):
then `fixedLvl?` is that universe, every replacement lives in it (`holeLevel`), and the generated
declarations have no universe of their own for it.

*Blocks.* A mutual block is one family over `Blk.Ix`, as `MutualCmd.lean` describes: `types`
has one entry per type, `ixCtors` the constructors of `Blk.Ix` applied to the parameters, the
occurrences of a type are at the block index `wrap m idx`, and a constructor records its type
(`owner`) and its name in the block-level inductives (`fname`). Single declarations have one type
and no `ixCtors`. The per-type declarations use the types `Tₘ` (`tyAt`, `withArgsAtU`), the
block-level ones the family.

*Mixed blocks.* A run of a `mixed_mutual` block is analysed as a type or a block whose last
parameters stand for the outer types it needs (`MixCtx`); in the outermost run, once its types
exist, the statements are written with the closed types of the runs inside (`closed`,
`foldClosed`): `Tₘ.Open params (fams)` at the closed families is `Tₘ params`, and membership in it
`x ∈ c` (`MemRule`).

*Universes.* A generated declaration has the user's universes that occur in it, in the order
declared, then universes of its own named `u_1`, `u_2`, … (`freshLevels`), as Lean names them;
`constWith` uses a generated constant at given universes for its own ones.
-/

open Lean Meta Elab Term

namespace Codata.Gen

/-- The occurrence structure of a nested argument. -/
structure Nest where
  /-- `Occ Sh Pos G`, or in a family `IOcc Sh Pos pidx G` over the packed index `Ctx.J`, at the
  placeholder universe `uT`: `G` is the argument type as a function of the occurrences. -/
  occ : Expr
  sh : Expr
  pos : Expr
  /-- In a family, the index of a position. -/
  pidx? : Option Expr
  deriving Inhabited

/-- How a constructor argument mentions the types being defined. -/
inductive ArgKind where
  /-- Not at all. -/
  | data
  /-- A plain recursive argument `T params idx`, with the family-level index arguments. -/
  | plain (idx : Array Expr)
  /-- A recursive argument under a telescope, `(y₁ : B₁) → … → (yₙ : Bₙ) → T params idx`, where
  `idx` may mention the `yⱼ`: its arity `n`; the telescope is reopened from the type
  (`Ctx.openFn`). -/
  | fn (arity : Nat)
  /-- Any other type mentioning the types being defined, with its occurrence structure. -/
  | nest (n : Nest)
  deriving Inhabited

def ArgKind.isData : ArgKind → Bool
  | .data => true
  | _ => false

def ArgKind.isNest : ArgKind → Bool
  | .nest _ => true
  | _ => false

/-- A constructor argument. -/
structure ArgInfo where
  /-- The argument, a local variable of the analysis. -/
  fvar : Expr
  name : Name
  bi : BinderInfo
  /-- Its elaborated type: over the parameters and the earlier arguments, with the types being
  defined as local variables. -/
  type : Expr
  kind : ArgKind
  /-- The syntax it comes from, for errors. -/
  ref : Syntax
  deriving Inhabited

/-- A constructor. -/
structure Ctor where
  /-- Its name as written, `cons`. -/
  name : Name
  /-- Its name in the block-level inductives `F`, `Shape`, `B`: the name itself, or `T_name` when
  another type of a block has a constructor of the same name. -/
  fname : Name
  /-- The position of its type in the block. -/
  owner : Nat
  args : Array ArgInfo
  /-- The family-level index arguments of its result type, over its arguments. -/
  idx : Array Expr
  /-- The index arguments as written; outside blocks, `idx`. -/
  uidx : Array Expr
  ref : Syntax
  /-- Its name as written, for the info tree. -/
  nameRef : Syntax
  deriving Inhabited

def Ctor.fvars (c : Ctor) : Array Expr := c.args.map (·.fvar)

def Ctor.hasNest (c : Ctor) : Bool := c.args.any (·.kind.isNest)

/-- A binder name users may refer to: `n` itself, unless a name of the declaration, `used`, is
`n`; then an inaccessible one, so that the declaration's own `n` is not shadowed. -/
def plainOr (used : Array Name) (n : Name) : CoreM Name :=
  if used.contains n then mkFreshUserName n else pure n

/-- A type being defined. -/
structure TypeInfo where
  /-- Its full name. -/
  name : Name
  /-- The local variable standing for it during the analysis, `∀ params idx, Type uT`. -/
  fvar : Expr
  /-- Its index binders, with the user's names (`iₖ` for unnamed ones). -/
  idx : Array Expr
  /-- Its declaration, for the ranges of the per-type declarations. -/
  ref : Syntax
  /-- Its name as written, for the info tree. -/
  nameRef : Syntax
  deriving Inhabited

/-- The types being defined, as the analysis and the generators see their occurrences. -/
structure Block where
  params : Array Expr
  types : Array TypeInfo
  /-- In a block, `@Blk.Ix.Tₘ params`, one per type; empty otherwise. -/
  ixCtors : Array Expr
  /-- The placeholder universe of the types being defined. -/
  uT : Name
  /-- The universe of the types being defined, when the constructors fix it. -/
  fixedLvl? : Option Level := none
  deriving Inhabited

namespace Block

variable (b : Block)

/-- The universe of the occurrences in the analysis: the placeholder, or the fixed one. -/
def lvl : Level := b.fixedLvl?.getD (.param b.uT)

/-- The universe of a replacement meant to be at `w`: `w`, or the fixed universe. -/
def holeLevel (w : Level) : Level := b.fixedLvl?.getD w

/-- The family-level index arguments of the `m`-th type at its index arguments `idx`. -/
def wrap (m : Nat) (idx : Array Expr) : Array Expr :=
  if b.ixCtors.isEmpty then idx else #[mkAppN b.ixCtors[m]! idx]

/-- The type being defined that `e` is an application of. -/
def typeOf? (e : Expr) : Option Nat :=
  let f := e.getAppFn
  if f.isFVar then b.types.findIdx? (·.fvar == f) else none

/-- Is `e` an application of a type being defined? -/
def isTypeApp (e : Expr) : Bool := (b.typeOf? e).isSome

/-- If `e` is an occurrence `Tₘ params idx`: the type's position and its index arguments. -/
def occ? (e : Expr) : Option (Nat × Array Expr) := do
  let m ← b.typeOf? e
  let args := e.getAppArgs
  let np := b.params.size
  guard (args.size == np + b.types[m]!.idx.size && args.extract 0 np == b.params)
  return (m, args.extract np args.size)

/-- If `e` is an occurrence: its family-level index arguments. -/
def holeOf? (e : Expr) : Option (Array Expr) := (b.occ? e).map fun (m, idx) => b.wrap m idx

def mentions (e : Expr) : Bool := e.hasAnyFVar fun x => b.types.any (·.fvar.fvarId! == x)

/-- The holes of the occurrence structures: the occurrences of the types being defined. -/
def holes (fam? : Option FamIdx) : Holes where
  holeOf? := b.holeOf?
  isTypeApp := b.isTypeApp
  mentions := b.mentions
  lvl := b.lvl
  fam?

/-- `e` with every occurrence `Tₘ params idx` replaced by `rep m idx`, and the placeholder
universe by `lvl`, the universe of the replacement. A family of occurrences
`fun p => T params p` becomes `rep` eta-reduced (`Both X` for `Both (fun c => T c)`). -/
def replaceOccU (e : Expr) (rep : Nat → Array Expr → Expr) (lvl : Level) : Expr :=
  substLevel b.uT lvl (go e)
where
  go (e : Expr) : Expr :=
    match b.occ? e with
    | some (m, idx) => rep m idx
    | none => match e with
      | .app f a => .app (go f) (go a)
      | .lam n d body bi =>
        let e' := Expr.lam n (go d) (go body) bi
        if (b.occ? body).isSome then e'.eta else e'
      | .forallE n d body bi => .forallE n (go d) (go body) bi
      | .letE n t v body nd => .letE n (go t) (go v) (go body) nd
      | .mdata m x => .mdata m (go x)
      | .proj s i x => .proj s i (go x)
      | e => e

/-- `e` with every occurrence replaced by `rep` at its family-level index arguments, and the
placeholder universe by `lvl` (`replaceOccU`). -/
def replaceOcc (e : Expr) (rep : Array Expr → Expr) (lvl : Level) : Expr :=
  b.replaceOccU e (fun m idx => rep (b.wrap m idx)) lvl

end Block

/-! ### Mixed blocks -/

/-- A run of a `mixed_mutual` block (`MutualCmd.lean`): adjacent declarations of the same kind,
with the names of what it declares. -/
structure MixRun where
  co : Bool
  /-- The positions of its declarations in the block. -/
  decls : Array Nat
  /-- The names of its types: `Tₘ.Open` in an open run, `Tₘ` in the outermost one. -/
  names : Array Name
  /-- The name of its family: its type, or its block (`Blk.Open` in an open run). -/
  fam : Name
  /-- In a block, its index `Blk.Ix`, on the parameters without the extra ones, declared before
  the runs. -/
  ix? : Option Name
  /-- The names of the closed types, and of the closed family. -/
  closedNames : Array Name
  closedFam : Name
  /-- The runs outside it whose types it takes as parameters, outermost first. -/
  need : Array Nat := #[]
  /-- The runs outside it that nest through it, directly or through a run between. -/
  nestedBy : Array Nat := #[]
  deriving Inhabited

/-- A run of a `mixed_mutual` block, as its context records it. -/
structure MixCtx where
  /-- Its position in the block. -/
  r : Nat
  /-- The extra parameters, one per outer run in `need`. -/
  xs : Array Expr
  need : Array Nat
  /-- Their universes, which the generated declarations of the run take after the user's. -/
  xLevels : Array Name
  /-- The closed types of the run, and for each extra parameter the first type of its run, for
  messages. -/
  closedNames : Array Name
  outerNames : Array Name
  /-- For each extra parameter, whether its run nests through this one: then the open types must
  have instances in it (step 5). -/
  required : Array Bool
  deriving Inhabited

/-- A declaration of an open run of a `mixed_mutual` block and its closed counterpart:
`openN params Xs rest`, with the closed families `args params` for the extra parameters `Xs`, is
`closedN params rest`. -/
structure FoldRule where
  openN : Name
  closedN : Name
  /-- The number of parameters before the extra ones. -/
  np : Nat
  /-- The closed families, each a function of the parameters. -/
  args : Array Expr
  /-- The positions, among the universes of `openN`, of those of the extra parameters. -/
  dropLvls : Array Nat
  deriving Inhabited

/-- Membership in a closed type of a mixed block: `PolyIso.Mem (fn params) x c`, for members of
the type `elem params` of an outer run, is `x ∈ c`, the instance's `mem params c x`. -/
structure MemRule where
  np : Nat
  /-- The number of indices of the closed type. -/
  nIdx : Nat := 0
  /-- The members' type, its head constant, and the closed type. -/
  elemN : Name
  contN : Name
  /-- Functions of the parameters (and of the indices of the closed type `C`, for `fn`, `mem`
  and `unfolded`): the functor, the members' type, and `@Membership.mem elem C inst`. -/
  fn : Expr
  elem : Expr
  mem : Expr
  /-- `fun c x => PolyIso.Mem (fn params) x c`, as a function of the parameters: what `mem`
  unfolds to. -/
  unfolded : Expr
  deriving Inhabited

/-- The closed declarations of a mixed block, with which statements are written (`foldClosed`). -/
structure Closed where
  rules : NameMap FoldRule := {}
  mems : Array MemRule := #[]
  deriving Inhabited

/-- `e` and `e'` are the same term but for their universes and eta. -/
def sameUpToLevels (e e' : Expr) : Bool :=
  let erase (e : Expr) := (mapLevels (fun _ => .zero) e).eta
  erase e == erase e'

/-- `e` with every application of a declaration of an open run at the closed families written
with its closed counterpart (`FoldRule`), the declaration on its own too when it takes no
arguments there, and membership in a closed type by its instance
(`MemRule`), the arguments first, so that a closed type is recognised inside the arguments of
another. -/
partial def foldClosed (c : Closed) (e : Expr) : Expr :=
  if c.rules.isEmpty then e else go e
where
  go (e : Expr) : Expr :=
    match e with
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs.map go
      let dflt := mkAppN (if f.isConst then f else go f) args
      match f with
      | .const n us => Id.run do
        if n == ``Codata.PolyIso.Mem && args.size == 7 then
          let elem := args[4]!
          let F := args[0]!
          for r in c.mems do
            unless elem.isAppOfArity r.elemN r.np do continue
            let ps := elem.getAppArgs
            -- The indices of the closed type, at the end of the functor's body.
            let idx := if r.nIdx == 0 then #[] else match F with
              | .lam _ _ b _ => b.getAppArgs.extract (b.getAppNumArgs - r.nIdx) b.getAppNumArgs
              | _ => #[]
            unless idx.size == r.nIdx && !idx.any (·.hasLooseBVars) do continue
            if sameUpToLevels (r.fn.beta (ps ++ idx)) F && sameUpToLevels (r.elem.beta ps) elem then
              return mkApp2 (r.mem.beta (ps ++ idx)) args[6]! args[5]!
          return dflt
        let some r := c.rules.find? n | return dflt
        let nx := r.args.size
        unless args.size ≥ r.np + nx do return dflt
        let ps := args.extract 0 r.np
        unless args.extract r.np (r.np + nx) == r.args.map (·.beta ps) do return dflt
        let us' := us.zipIdx.filterMap fun (u, i) => if r.dropLvls.contains i then none else some u
        return mkAppN (.const r.closedN us') (ps ++ args.extract (r.np + nx) args.size)
      | _ => dflt
    -- Without parameters and extra arguments, the open declaration on its own.
    | .const n us => match c.rules.find? n with
      | some r =>
        if r.np == 0 && r.args.isEmpty then
          .const r.closedN (us.zipIdx.filterMap fun (u, i) =>
            if r.dropLvls.contains i then none else some u)
        else e
      | none => e
    | .lam n d b bi => .lam n (go d) (go b) bi
    | .forallE n d b bi => .forallE n (go d) (go b) bi
    | .letE n t v b nd => .letE n (go t) (go v) (go b) nd
    | .mdata m b => .mdata m (go b)
    | .proj s i b => .proj s i (go b)
    | e => e

/-- A declared sort with a universe written: the types' universe must be that one. -/
structure WrittenSort where
  /-- The position of the declaration in the block (of the whole `mixed_mutual` block in a run of
  one), and the name of its type as written. -/
  decl : Nat
  T : Name
  /-- The sort as written, and as elaborated: `∀ idx, Sort lvl`, without `_` in `lvl`. -/
  stx : Syntax
  sort : Expr
  lvl : Level
  deriving Inhabited

/-- Everything the generators need: see the header. -/
structure Ctx extends Block where
  /-- `codata` (`true`) or `data`. -/
  co : Bool
  /-- The family being defined: the type, or the block. -/
  name : Name
  /-- The declaration, for errors and declaration ranges. -/
  ref : Syntax
  /-- The user's universes, in the order declared. -/
  userLevels : List Name
  /-- How many of the parameters, at the front, are section variables. -/
  nVars : Nat := 0
  /-- The index binders of the family: the type's, or in a block the one index `Blk.Ix params`. -/
  idx : Array Expr
  /-- The packed index type: `(i₁ : I₁) ×' I₂ …` for several indices, the index type itself for
  one, `Unit` for none. -/
  J : Expr
  /-- `J : Type Jlvl`. -/
  Jlvl : Level
  ctors : Array Ctor
  /-- The declared sorts with a universe written, checked against the types' universe before
  anything is declared (`checkSorts`); in a run of a `mixed_mutual` block, those of the block. -/
  written : Array WrittenSort := #[]
  /-- In a `mixed_mutual` block, the run. -/
  mix? : Option MixCtx := none
  /-- In the outermost run of a `mixed_mutual` block, once its types exist: the closed types of
  the runs inside, with which the statements are written (`foldTy`). -/
  closed : Closed := {}
  deriving Inhabited

namespace Ctx

variable (ctx : Ctx)

/-- Is this an open run of a `mixed_mutual` block, declared with the outer types as parameters? -/
def isOpen : Bool := ctx.mix?.any (·.r > 0)

/-- `e` written with the closed types of a mixed block (`foldClosed`). -/
def foldTy (e : Expr) : Expr := foldClosed ctx.closed e

/-- The parameters declared with the type: those that are explicit in the generated types. The
section variables before them keep their own binder infos there, as with `inductive`. -/
def declParams : Array Expr := ctx.params.extract ctx.nVars ctx.params.size

/-- Is this a mutual block, one family over `Blk.Ix`? -/
def isBlock : Bool := !ctx.ixCtors.isEmpty

/-! ### Indices -/

/-- The number of indices of the family. -/
def k : Nat := ctx.idx.size

def idxed : Bool := ctx.k > 0

/-- Pack index arguments into one term of `J`: `⟨a₁, a₂⟩`, `a₁`, or `()`. -/
def pack (args : Array Expr) : MetaM Expr := do
  if ctx.k == 0 then return mkConst ``Unit.unit
  let mut acc := ctx.idx.back!
  for m' in [0:ctx.k - 1] do
    let m := ctx.k - 2 - m'
    let i := ctx.idx[m]!
    -- An explicit binder, whatever the binder info of `i` in the current declaration.
    let β ← withNewBinderInfos #[(i.fvarId!, .default)] do mkLambdaFVars #[i] (← inferType acc)
    acc ← mkAppOptM ``PSigma.mk #[← inferType i, β, i, acc]
  return acc.replaceFVars ctx.idx args

/-- The components of a term `p` of `J`: `p.1, p.2.1, p.2.2`, or `p`. -/
def projs (p : Expr) : MetaM (Array Expr) := do
  if ctx.k ≤ 1 then return if ctx.k == 0 then #[] else #[p]
  let mut out := #[]
  let mut cur := p
  for _ in [0:ctx.k - 1] do
    out := out.push (← mkAppM ``PSigma.fst #[cur])
    cur ← mkAppM ``PSigma.snd #[cur]
  return out.push cur

def famIdx? : Option FamIdx :=
  if ctx.idxed then some { J := ctx.J, lvl := ctx.Jlvl, pack := ctx.pack } else none

/-- The names `j₁, j₂, …` of a second copy of the index binders. -/
def jNames : Array Name :=
  (Array.range ctx.k).map fun m => Name.mkSimple s!"j{Nat.toSubscriptString (m + 1)}"

/-- Run `k` on a copy `j₁ j₂ …` of the index binders. -/
def withJs (k : Array Expr → TermElabM α) : TermElabM α :=
  withCopies ctx.idx ctx.jNames .default k

/-- The sort of a family variable at universe `lvl`: `Type lvl`, or `∀ j₁ j₂, Type lvl`. -/
def famType (lvl : Level) : TermElabM Expr :=
  ctx.withJs fun js => mkForallFVars js (mkSort lvl.succ)

/-- `X → Y`, or `∀ j₁ j₂, X j₁ j₂ → Y j₁ j₂`. -/
def famFn (X Y : Expr) : TermElabM Expr :=
  ctx.withJs fun js => do mkForallFVars js (← mkArrow (mkAppN X js) (mkAppN Y js))

/-! ### Constructors at a replacement of the occurrences -/

/-- Run `k` on new local variables for the arguments of `c`, the occurrences `Tₘ params idx` in
their types replaced by `rep m idx` at universe `lvl`: the constructor's arguments as those of
`T.F` at a family `X` (`withArgsAt`, `rep idx := X idx` at the family-level index), say. `k`
receives the new variables and the substitution of the old by the new, for the expressions of
the analysis (index arguments, occurrence structures). The new variables are named `rename x`,
and their types are passed through `post`.
-/
def withArgsAtU (c : Ctor) (rep : Nat → Array Expr → Expr) (lvl : Level)
    (k : Array Expr → (Expr → Expr) → TermElabM α) (rename : Name → Name := id)
    (post : Expr → Expr := id) : TermElabM α := do
  let rec go (i : Nat) (ys : Array Expr) : TermElabM α := do
    if h : i < c.args.size then
      let a := c.args[i]
      let ty := post (ctx.replaceOccU (a.type.replaceFVars (c.fvars.extract 0 i) ys) rep lvl)
      withLocalDecl (rename a.name) a.bi ty fun y => go (i + 1) (ys.push y)
    else k ys fun e => e.replaceFVars c.fvars ys
  go 0 #[]

/-- `withArgsAtU` for a replacement at the family-level index arguments: `rep idx`. -/
def withArgsAt (c : Ctor) (rep : Array Expr → Expr) (lvl : Level)
    (k : Array Expr → (Expr → Expr) → TermElabM α) (rename : Name → Name := id) :
    TermElabM α :=
  ctx.withArgsAtU c (fun m idx => rep (ctx.wrap m idx)) lvl k rename

/-- Open the telescope of an argument of kind `.fn n`, at the type `ty` it has after a
replacement by a family `X`: `k ys idx` with the bound variables and the family-level index
arguments of the result `X idx` (for the occurrences `Tₘ params idx`, `Ctx.openTFn`). -/
def openFn (n : Nat) (ty : Expr) (k : Array Expr → Array Expr → TermElabM α) : TermElabM α :=
  withReducible <| forallBoundedTelescope ty n fun ys body => do
    k ys (← whnfOcc body).getAppArgs

/-- The occurrence structure of a nested argument, at universe `lvl`, under the substitution
`σ` of a `withArgsAt`. -/
def nestAt (n : Nest) (lvl : Level) (σ : Expr → Expr) : Expr :=
  substLevel ctx.uT lvl (σ n.occ)

/-! ### Names -/

/-- The generated declaration `T.s`. Inside its own namespace `T.T` would shadow the type `T`,
so a generated name equal to the type's name is primed (`B.B'` for `codata B`). -/
def gen (s : String) : Name :=
  let last := match ctx.name with
    | .str _ s' => s'
    | _ => ""
  .str ctx.name (if last == s then s ++ "'" else s)

/-- `T.F`, the functor. -/
def F : Name := ctx.gen "F"

/-- `T.F.s`. -/
def nF (s : String) : Name := .str ctx.F s

/-- `T.F.c`, the constructor of `F` for `c`. -/
def fCtor (c : Ctor) : Name := ctx.F ++ c.fname

def Fmap : Name := ctx.nF "map"
def FmapCtor (c : Ctor) : Name := ctx.nF ("map_" ++ c.fname.toString)
def Fmap_id : Name := ctx.nF "map_id"
def Fmap_comp : Name := ctx.nF "map_comp"
def Rel : Name := ctx.nF "Rel"
def Frel_map : Name := ctx.nF "rel_map"
/-- `T.F.Rel.c`. -/
def relCtor (c : Ctor) : Name := ctx.Rel ++ c.fname

/-- The signature: `T.Shape`, `T.B`, `T.Ix`, `T.idx`, `T.ShapeP`, `T.sig`. -/
def Shape : Name := ctx.gen "Shape"
def B : Name := ctx.gen "B"
def Ix : Name := ctx.gen "Ix"
def idxN : Name := ctx.gen "idx"
def ShapeP : Name := ctx.gen "ShapeP"
def sig : Name := ctx.gen "sig"
/-- `T.Shape.c`. -/
def shapeCtor (c : Ctor) : Name := ctx.Shape ++ c.fname
/-- `T.B.c_x`, the positions of the argument `x` of `c`. -/
def bCtor (c : Ctor) (a : ArgInfo) : Name :=
  ctx.B ++ Name.mkSimple (c.fname.toString ++ "_" ++ a.name.toString)

/-- The isomorphism and the model. -/
def toC : Name := ctx.gen "toC"
def ofC : Name := ctx.gen "ofC"
def ofC_toC : Name := ctx.gen "ofC_toC"
def toC_ofC : Name := ctx.gen "toC_ofC"
def ofC_map : Name := ctx.gen "ofC_map"
def rel_ofC : Name := ctx.gen "rel_ofC"
def dtor : Name := ctx.gen "dtor"
def corec : Name := ctx.gen "corec"
def dtor_corec : Name := ctx.gen "dtor_corec"
def bisim : Name := ctx.gen "bisim"
def contract : Name := ctx.gen "contract"
def ctor : Name := ctx.gen "ctor"
def fold : Name := ctx.gen "fold"
def fold_ctor : Name := ctx.gen "fold_ctor"
def recAux : Name := ctx.gen "recAux"
def recPos : Name := ctx.gen "recPos"
def recPos_ctor : Name := ctx.gen "recPos_ctor"
def recN : Name := ctx.gen "rec"

/-- The framework. -/
def dtor_ctor : Name := ctx.gen "dtor_ctor"
def ctor_dtor : Name := ctx.gen "ctor_dtor"
def ctor_injective : Name := ctx.gen "ctor_injective"
def corec_eq : Name := ctx.gen "corec_eq"
def corec_unique : Name := ctx.gen "corec_unique"
def fold_eq : Name := ctx.gen "fold_eq"
def fold_unique : Name := ctx.gen "fold_unique"

/-- The surface: per-type names, for the type of `c`. In a block the types `Tₘ` are
declarations of their own (`Tₘ params idx := Blk params (.Tₘ idx)`); otherwise the type is the
family. -/
def tyName (m : Nat) : Name := ctx.types[m]!.name
/-- The last component of the name the user wrote for the `m`-th type (`Forest`, also for
`Forest.Open`). -/
def shortName (m : Nat) : String := ctx.types[m]!.nameRef.getId.lastComponentAsString
def tCtor (c : Ctor) : Name := ctx.tyName c.owner ++ c.name
def tName' (c : Ctor) (pre post : String) : Name :=
  ctx.tyName c.owner ++ Name.mkSimple (pre ++ c.name.toString ++ post)
def tyGen (m : Nat) (s : String) : Name := .str (ctx.tyName m) s

/-- A binder name users may refer to (`motive := …`, `S := …`): plain, unless the declaration
uses it (`plainOr`). -/
def userName (n : Name) : TermElabM Name := do
  let used := ctx.params.map (·.fvarId!) ++ ctx.idx.map (·.fvarId!) ++
    ctx.ctors.flatMap (·.fvars.map (·.fvarId!))
  plainOr ((← used.mapM (·.getUserName)) ++ ctx.ctors.map (·.name)) n

/-! ### Universes -/

/-- `n` universe names for a declaration, besides the user's. -/
def freshLevels (n : Nat) : List Name := freshLevelNames n ctx.userLevels

/-- The universe parameters of a declaration made of `es`, with the added universes `fresh`. -/
def levelParamsOf (fresh : List Name) (es : Array Expr) : MetaM (List Name) :=
  Gen.levelParamsOf ctx.userLevels fresh es

/-- The universes at which to use the generated constant `n`: the user's as they are, the
universes it added (`u_1`, …) given by `fresh`, in order. -/
def levelsWith (n : Name) (fresh : List Level) : MetaM (List Level) := do
  let ci ← getConstInfo n
  let (us, _) := ci.levelParams.foldl (init := (#[], fresh)) fun (us, fresh) p =>
    if ctx.userLevels.contains p then (us.push (.param p), fresh)
    else match fresh with
      | l :: rest => (us.push l, rest)
      | [] => (us.push (.param p), [])
  return us.toList

/-- The generated constant `n` at the user's universes and the added universes `fresh`. -/
def constWith (n : Name) (fresh : List Level) : MetaM Expr :=
  return .const n (← ctx.levelsWith n fresh)

/-- The generated constant `n` at the added universes `fresh`, applied to the parameters and
`args`. -/
def genAt (n : Name) (fresh : List Level) (args : Array Expr) : MetaM Expr :=
  return mkAppN (← ctx.constWith n fresh) (ctx.params ++ args)

/-- The `m`-th type at its index arguments: `Tₘ params idx`. -/
def tyAt (m : Nat) (idx : Array Expr) : MetaM Expr := ctx.genAt (ctx.tyName m) [] idx

/-- The family-level index arguments of an occurrence `Tₘ params idx` of one of the types,
written with the per-type constant (as `withTArgs` gives them), or of `X idx` for a family `X`
applied to the parameters too. -/
def famIdxOf (e : Expr) : Array Expr :=
  let args := e.getAppArgs
  let idx := args.extract ctx.params.size args.size
  match ctx.types.findIdx? (e.getAppFn.isConstOf ·.name) with
  | some m => ctx.wrap m idx
  | none => idx

end Ctx

end Codata.Gen
