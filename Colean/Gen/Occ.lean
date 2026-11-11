import Colean.Model.Occ
import Colean.Gen.Decl

/-!
# Generators on `Expr`: occurrence structures

*Spec.* Input: the elaborated type of a constructor argument and a description of the *holes*,
the occurrences of the types being defined (`Holes`). Output: its occurrence structure, a term
of `Codata.Occ` (or `Codata.IOcc` for a family) built from the combinators of `Model/Occ.lean`,
whose functor is the argument type as a function of the holes. The structure is built by
recursion on the type in `whnfOcc` form (`whnfR`, and `id` unfolded), so that the spellings
`A × B` and `Prod A B`, `id A`, or a reducible abbreviation, are one: products, sums, functions
and dependent pairs over constant types are recognised by their head, and any other application
with occurrences in its arguments is a *leaf*, a named type constructor whose structure comes
from its `PolyIso` (`IPolyIso` for a functor of families) instance, which needs a `PolyMap`
(`IPolyMap`) instance as well. Instance search happens at leaves only. The universe of the holes
is a parameter (`Holes.lvl`): the leaves' universes follow it.

A leaf is a functor of one argument: a partial application when the occurrences are in its last
argument (`List T`), the whole type as a function of the occurrence otherwise (`wholeLeaf`): when
several arguments have occurrences (`E T (List T)`, `fun X => E X (List X)`), and when the
argument with them is not the last (`Vec (List T) n`, `fun X => Vec (List X) n`;
`E (T × Nat) Nat`), if instance search finds an instance for it, so that the structure is the
instance that instance search finds for that functor, which the composite of `fun X => Vec X n`
and `List` is not.

The holes are a parameter so that the same recursion can serve other analyses: the parameter
positions of `deriveInstances` (`Gen/Derive.lean`), where the holes are parameters of the type
and the structure put at each is that of its premise (`Holes.atHole?`); a leaf with occurrences of
several parameters is then the instance at the premises, `fun X => E (H₁ X) (H₂ X)`.
-/

open Lean Meta Elab Term

namespace Codata.Gen

/-- The head normal form in which occurrences are recognised: `whnfR`, and `id` unfolded, so
that reducible abbreviations and `id A` are seen through. -/
partial def whnfOcc (e : Expr) : MetaM Expr := do
  let e ← whnfR e
  if e.isAppOfArity ``id 2 then whnfOcc e.appArg! else return e

/-- A family's packed index: the type `J : Type lvl` and the packing of the index arguments of
an occurrence into one term of `J`. -/
structure FamIdx where
  J : Expr
  lvl : Level
  pack : Array Expr → MetaM Expr

/-- The occurrences an occurrence structure is about. -/
structure Holes where
  /-- The index arguments of `e` if it is an occurrence (at the family level). -/
  holeOf? : Expr → Option (Array Expr)
  /-- Is `e` an application of a type being defined, occurrence or not? -/
  isTypeApp : Expr → Bool
  /-- Does `e` mention a type being defined? -/
  mentions : Expr → Bool
  /-- The universe of the occurrences: `T params idx : Type lvl`. -/
  lvl : Level
  /-- For a family, its packed index: the structure is then an `IOcc` over it. -/
  fam? : Option FamIdx
  /-- The structure to put at an occurrence instead of `Occ.hole`, as a function of the
  occurrence, with the universe of its argument: a premise `Occ.ofIso H` per parameter
  (`Gen/Derive.lean`). Without indices only. -/
  atHole? : Option ((Expr → Expr) × Level) := none

def badOcc : MessageData :=
  "recursive occurrence not recognised: a type being defined must be applied to its parameters \
  (and indices)"

def badDomain : MessageData :=
  "the types being defined may not occur in the domain of a function"

namespace Holes

variable (h : Holes)

/-- The combinator `n` of `Occ`, or of `IOcc` for a family, with its explicit arguments. -/
def comb (n : Name) (args : Array Expr) : MetaM Expr :=
  mkAppM ((if h.fam?.isSome then ``Codata.IOcc else ``Codata.Occ) ++ n) args

/-- The universe of the argument of the structure: that of the occurrences, or of the
structure put at them. -/
def argLvl : Level := (h.atHole?.map (·.2)).getD h.lvl

/-- The structure of a constant `A`: no positions. -/
def const (A : Expr) : MetaM Expr := do
  let v ← typeLevel A
  match h.fam? with
  | none => return mkApp (← constAt ``Codata.Occ.const [(`u, h.argLvl), (`v, v)]) A
  | some fam =>
    return mkApp2 (← constAt ``Codata.IOcc.const [(`v, v), (`j, fam.lvl), (`u_1, h.lvl)]) fam.J A

/-- The structure of the occurrence `e`, at the index arguments `idx`. -/
def hole (e : Expr) (idx : Array Expr) : MetaM Expr := do
  if let some (o, _) := h.atHole? then return o e
  match h.fam? with
  | none => constAt ``Codata.Occ.hole [(`u, h.lvl)]
  | some fam =>
    return mkApp2 (← constAt ``Codata.IOcc.hole [(`u, h.lvl), (`j, fam.lvl)]) fam.J
      (← fam.pack idx)

/-- The structure `oG` of a leaf applied to the occurrence `e`: itself, or composed with the
structure put at `e`. -/
def atLeaf (oG e : Expr) : MetaM Expr := do
  match h.atHole? with
  | some (o, _) => mkAppM ``Codata.Occ.comp #[oG, o e]
  | none => return oG

/-- The occurrences in `e`, with their index arguments. -/
partial def holesIn (e : Expr) : Array (Expr × Array Expr) :=
  match h.holeOf? e with
  | some idx => #[(e, idx)]
  | none => match e with
    | .app f a => holesIn f ++ holesIn a
    | .lam _ d b _ | .forallE _ d b _ => holesIn d ++ holesIn b
    | .letE _ t v b _ => holesIn t ++ holesIn v ++ holesIn b
    | .mdata _ b | .proj _ _ b => holesIn b
    | _ => #[]

end Holes

/-- The constant `n` applied to its arguments, `args` given by position and the instance
arguments found by instance search, the others determined by unification; `none` if the
arguments do not fit or no instance is found. Other errors of the search, a timeout say, are
thrown. The search may assign universe metavariables of the arguments: an instance at one
universe only (`PolyIso MonoBox.{0}`) fixes it. -/
def appWithInstances (n : Name) (args : Array (Nat × Expr)) : MetaM (Option Expr) := do
  let f ← mkConstWithFreshMVarLevels n
  let (xs, bis, _) ← forallMetaTelescope (← inferType f)
  for (i, a) in args do
    unless ← isDefEq xs[i]! a do return none
  for x in xs, bi in bis do
    if bi.isInstImplicit then
      let some v ← synthInstance? (← instantiateMVars (← inferType x)) | return none
      unless ← isDefEq x v do return none
  return some (← instantiateMVars (mkAppN f xs))

/-- The structure of a leaf `G`, a named type constructor (as a function of its argument with
occurrences), from its `PolyIso` instance; `fam` for a functor of families, from `IPolyIso`.
The `PolyMap` instance is not used by the generated declarations: it is required because it is
what makes the map they use the intended one (`Occ.map_ofIso`). -/
def leafOcc (G : Expr) (fam : Bool) : MetaM Expr := do
  let (iso, map) := if fam then ("IPolyIso", "IPolyMap") else ("PolyIso", "PolyMap")
  let o? ← if fam then appWithInstances ``Codata.IOcc.ofIso #[(1, G)]
    else appWithInstances ``Codata.Occ.ofIso #[(0, G)]
  let some o := o? | throwError "no `Codata.{iso}` instance for `{G}`; to nest through a type \
    constructor, give it `Codata.{iso}` and `Codata.{map}` instances (`Colean/PolyIso.lean`); \
    products, sums, functions and dependent pairs over constant types need none"
  let G ← instantiateMVars G
  let cls? ← if fam then appWithInstances ``Codata.IPolyMap #[(1, G), (2, G)]
    else appWithInstances ``Codata.PolyMap #[(0, G), (1, G)]
  let hasMap ← match cls? with
    | some cls => pure (← synthInstance? cls).isSome
    | none => pure false
  unless hasMap do
    throwError "no `Codata.{map}` instance for `{G}`: the `Codata.{iso}` instance needs the \
      intended action on functions, and its naturality"
  return o

/-- The structure of the application `e` of a named type constructor as a whole: a leaf, the
functor of its occurrences found by instance search, at one index; for occurrences of several
parameters each with its structure (`Holes.atHole?`), at the functors of these structures,
`fun X => E (H₁ X) (H₂ X)`. With `strict`, a failure is an error; otherwise it gives `none`, and
leaves the state as it was. -/
def wholeLeaf (h : Holes) (e : Expr) (strict : Bool) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let found := h.holesIn e
    let some (e₀, idx) := found[0]? | throwError badOcc
    unless found.all (·.2 == idx) do
      throwError "the types being defined occur at different indices in several arguments of \
        `{e.getAppFn}`, which is supported only for products, sums, functions and dependent pairs"
    if idx.any (·.hasLooseBVars) then throwError badOcc
    if let some (o, lvl) := h.atHole? then
      unless found.all (·.1 == e₀) do
        let fns ← found.mapM fun (s, _) => do
          return (s, (← whnfR (← inferType (o s))).appArg!)
        let G ← withLocalDeclD `X (mkSort lvl.succ) fun X => do
          let body := e.replace fun s =>
            (fns.find? (·.1 == s)).map fun (_, H) => (mkApp H X).headBeta
          if h.mentions body then throwError badOcc
          mkLambdaFVars #[X] body
        return some (← leafOcc G false)
    -- The universe of the occurrences: of the parameter, with several.
    let xl ← if h.atHole?.isSome then typeLevel e₀ else pure h.lvl
    let G ← withLocalDeclD `X (mkSort xl.succ) fun X => do
      let body := e.replace fun s => (h.holeOf? s).map fun _ => X
      if h.mentions body then throwError badOcc
      mkLambdaFVars #[X] body
    let oG ← leafOcc G false
    match h.fam? with
      | none => some <$> h.atLeaf oG e₀
      | some fam => do some <$> mkAppM ``Codata.IOcc.ofOcc #[oG, ← fam.pack idx]
  catch ex =>
    if strict then throw ex
    s.restore
    return none

/-- The occurrence structure of the type `ty`. -/
partial def occOf (h : Holes) (ty : Expr) : MetaM Expr := do
  let ty ← instantiateMVars ty
  unless h.mentions ty do return ← h.const ty
  let e ← whnfOcc ty
  if let some idx := h.holeOf? e then return ← h.hole e idx
  if h.isTypeApp e then throwError badOcc
  match e with
  | .forallE n A B bi =>
    if h.mentions A then throwError badDomain
    let isP ← isProp A
    withLocalDecl n bi A fun a => do
      let o ← occOf h (B.instantiate1 a)
      h.comb (if isP then `piP else `pi) #[A, ← mkLambdaFVars #[a] o]
  | _ =>
  let f := e.getAppFn
  let args := e.getAppArgs
  if e.isAppOfArity ``Prod 2 then
    return ← h.comb `prod #[← occOf h args[0]!, ← occOf h args[1]!]
  if e.isAppOfArity ``Sum 2 then
    return ← h.comb `sum #[← occOf h args[0]!, ← occOf h args[1]!]
  if e.isAppOfArity ``Sigma 2 then
    let A := args[0]!
    let B := args[1]!
    if h.mentions A then throwError badDomain
    let n := if B.isLambda then B.bindingName! else `x
    return ← withLocalDeclD n A fun a => do
      let o ← occOf h (mkApp B a).headBeta
      h.comb `sigma #[A, ← mkLambdaFVars #[a] o]
  unless f.isConst || f.isFVar do
    throwError "recursive occurrence not recognised: expected a type being defined applied to its \
      parameters (and indices), possibly under arrows, products, sums, dependent pairs or type \
      constructors with an occurrence structure"
  let ks := (List.range args.size).filter fun k => h.mentions args[k]!
  -- Several arguments with occurrences: the whole type as a functor of the occurrence, at one
  -- index.
  if ks.length ≥ 2 then
    let some o ← wholeLeaf h e true | throwError badOcc
    return o
  let k := ks[0]!
  let arg := args[k]!
  -- The leaf as a function of its argument: a partial application when the argument is last, a
  -- lambda otherwise.
  let G ← if k + 1 == args.size then pure (mkAppN f (args.extract 0 k))
    else withLocalDeclD `X (← instantiateMVars (← inferType arg)) fun X =>
      mkLambdaFVars #[X] (mkAppN f (args.set! k X))
  if arg.isLambda then
    -- A functor of families applied to `fun p => body`.
    let oG ← leafOcc G true
    lambdaBoundedTelescope arg 1 fun ps body => do
      let p := ps[0]!
      if let some idx := h.holeOf? (← whnfOcc body) then
        if h.atHole?.isSome then throwError badOcc
        match h.fam? with
        | none => mkAppM ``Codata.Occ.ofI #[oG]
        | some fam =>
          let pk ← fam.pack idx
          -- The family at its own index: the leaf itself.
          if pk == p then pure oG else mkAppM ``Codata.IOcc.reidx #[oG, ← mkLambdaFVars #[p] pk]
      else
        let inner ← occOf h body
        h.comb `compI #[oG, ← mkLambdaFVars #[p] inner]
  else
    let oG ← leafOcc G false
    let arg' ← whnfOcc arg
    if let some idx := h.holeOf? arg' then
      match h.fam? with
      | none => h.atLeaf oG arg'
      | some fam => mkAppM ``Codata.IOcc.ofOcc #[oG, ← fam.pack idx]
    else
      -- An expression with occurrences in an argument that is not the last one: the whole type,
      -- if instance search finds an instance for it, which is then the one a user's
      -- `PolyIso.Mem` finds (`fun X => Vec (List X) n`, by `Vec`'s instance at `List`;
      -- `fun X => E (X × Nat) Nat`, by `E`'s at the product); the composite otherwise. `simp`
      -- computes the map at the premise of the instance, a leaf (`Occ.map_list`, the rules of a
      -- declared type) or a built-in form (`Occ.ofIso_prod`, …).
      if k + 1 != args.size then
        if let some o ← wholeLeaf h e false then return o
      let inner ← occOf h arg
      mkAppM (if h.fam?.isSome then ``Codata.IOcc.compC else ``Codata.Occ.comp) #[oG, inner]

end Codata.Gen
