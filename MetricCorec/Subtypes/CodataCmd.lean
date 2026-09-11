import MetricCorec.Subtypes.Codata

/-!
# The `codata` command

Current scope: parameters, a single type, no indices. Constructor binders may be explicit or
implicit; recursive arguments may be plain (`t : T params`) or under a function type
(`f : I → T params`), where `I` may depend on the constructor's own data.

```
codata ITree (E : Type → Type) (R : Type)
  | Ret (r : R)
  | Tau (t : ITree E R)
  | Vis {X : Type} (e : E X) (k : X → ITree E R)
```

The command generates, with the parameters as arguments of every declaration (explicit for the
types `T`, `T.F`, `T.Shape`, `T.B`, `T.sig`, implicit elsewhere):

* `T.F (params) (X : Type _)`: the constructor list with `T params` replaced by `X`, as an
  inductive type; `T.F.map` and `T.F.Rel`, its action on functions and its lifting to relations,
  with the laws `T.F.map_id`, `T.F.map_comp`, `T.F.rel_map`, and the simp lemmas `T.F.map_ctorᵢ`;
* the signature: `T.Shape` (the constructors with their non-recursive data only) and
  `T.B : T.Shape → Type`, the positions for recursive arguments, one nullary constructor `ctorᵢ_t`
  per plain argument `t` and one unary constructor `ctorᵢ_f (i : I)` per function argument
  `f : I → T`; bundled as `T.sig`;
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

Only the six lemmas about the generated inductive `T.F` (`map_id`, `map_comp`, `rel_map`,
`ofC_toC`, `ofC_map`, `rel_ofC`) are proved by tactic scripts, and those are `cases` followed by
`rfl` or `solve_by_elim`; everything else instantiates a theorem of `Codata.lean`. The
declarations from `T` on are generated in a `noncomputable section`, since the encoding decides
equality of shapes classically.
-/

open Lean Elab Command Lean.Parser.Term

namespace Codata

/-- A constructor of a `codata` declaration: a name and binders `(x y : A)` or `{x y : A}`. -/
syntax codataCtor := "| " ident (ppSpace bracketedBinder)*

/-- `codata T (params) | ctor₁ … | ctor₂ …` declares a coinductive type as a subtype of `Raw`. -/
syntax (name := codataCmd) "codata " ident (ppSpace bracketedBinder)* codataCtor* : command

/-- The kind of a constructor argument: non-recursive data, a plain recursive argument, or a
recursive argument under a function type with the given domain. -/
inductive Kind where
  | data
  | pos
  | fn (dom : Term)

/-- A binder group of a constructor. -/
structure Group where
  ids : Array Ident
  ty : Term
  kind : Kind
  implicit : Bool

/-- A constructor, analysed. -/
structure CtorInfo where
  name : Ident
  groups : Array Group

private def idT (x : Ident) : Term := ⟨x.raw⟩

def Kind.isData : Kind → Bool
  | .data => true
  | _ => false

/-- The identifiers of the explicit arguments, in order: what the constructor is applied to. -/
def CtorInfo.args (c : CtorInfo) : Array Ident :=
  c.groups.foldl (fun acc g => if g.implicit then acc else acc ++ g.ids) #[]

/-- The identifiers of the explicit non-recursive arguments: what the shape is applied to. -/
def CtorInfo.dataArgs (c : CtorInfo) : Array Ident :=
  c.groups.foldl (fun acc g => if g.implicit || !g.kind.isData then acc else acc ++ g.ids) #[]

def CtorInfo.hasRec (c : CtorInfo) : Bool := c.groups.any fun g => !g.kind.isData

def CtorInfo.hasImplicit (c : CtorInfo) : Bool := c.groups.any (·.implicit)

/-- `f` applied to `args`, or just `f` when there are none. -/
private def mkAppT (f : Ident) (args : Array Term) : CommandElabM Term :=
  if args.isEmpty then pure (idT f) else `($f:ident $args:term*)

/-- Is `ty` the type `T p₁ … pₙ` being defined, applied to exactly its parameters? -/
private def isRecTy (tName : Name) (params : Array Ident) (ty : Term) : Bool :=
  match ty with
  | `($f:ident $as:term*) =>
    f.getId == tName && as.size == params.size &&
      (as.zip params).all fun (a, p) => a.raw.isIdent && a.raw.getId == p.getId
  | `($f:ident) => params.isEmpty && f.getId == tName
  | _ => false

/-- Classify the type of a constructor argument. -/
private def classify (tName : Name) (params : Array Ident) (ty : Term) : Kind :=
  if isRecTy tName params ty then .pos
  else match ty with
    | `($dom → $cod) => if isRecTy tName params cod then .fn dom else .data
    | _ => .data

/-- A binder group as a `bracketedBinder`, explicit or implicit as declared. -/
private def mkBinder (implicit : Bool) (ids : Array Ident) (ty : Term) :
    CommandElabM (TSyntax ``bracketedBinderF) :=
  if implicit then `(bracketedBinderF| {$ids* : $ty}) else `(bracketedBinderF| ($ids* : $ty))

/-- Everything the generators need: the analysed declaration, and the names of the generated
declarations and the types applied to the parameters. -/
structure Ctx where
  T : Ident
  tName : Name
  pids : Array Ident
  pExp : Array (TSyntax ``bracketedBinderF)
  pImp : Array (TSyntax ``bracketedBinderF)
  pTerms : Array Term
  ctors : Array CtorInfo
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

/-- The binders of a constructor of `F`: recursive types replaced by `X`. -/
def fBinders (c : CtorInfo) : CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  c.groups.mapM fun g => do
    let ty ← match g.kind with
      | .data => pure g.ty
      | .pos => `(X)
      | .fn dom => `($dom → X)
    mkBinder g.implicit g.ids ty

/-- The data binders of a constructor, all implicit (for the constructors of `D`, where the
data is determined by the index). -/
def dataBindersImplicit (c : CtorInfo) : CommandElabM (Array (TSyntax ``bracketedBinderF)) :=
  (c.groups.filter (·.kind.isData)).mapM fun g => mkBinder true g.ids g.ty

/-- The explicit arguments of a constructor of `F` after `map f`. -/
def mappedArgs (c : CtorInfo) : CommandElabM (Array Term) := do
  let args ← c.groups.mapM fun g => do
    if g.implicit then return #[]
    g.ids.mapM fun (x : Ident) => match g.kind with
      | .data => pure (idT x)
      | .pos => `(f $x:ident)
      | .fn _ => `(fun i => f ($x:ident i))
  return args.foldl (· ++ ·) #[]

namespace Ctx

variable (ctx : Ctx)

def fCtor (c : CtorInfo) : Ident := mkIdent (ctx.F.getId ++ c.name.getId)
def shapeCtor (c : CtorInfo) : Ident := mkIdent (ctx.Shape.getId ++ c.name.getId)
def bCtor (c : CtorInfo) (x : Ident) : Ident := mkIdent (ctx.B.getId ++ (posCtorName c x).getId)
def tCtor (c : CtorInfo) : Ident := mkIdent (ctx.tName ++ c.name.getId)
def tName' (c : CtorInfo) (pre post : String) : Ident :=
  mkIdent (ctx.tName ++ Name.mkSimple (pre ++ c.name.getId.toString ++ post))
def nF (s : String) : Ident := mkIdent (.str (.str ctx.tName "F") s)

end Ctx

open Ctx

/-! ### The functor `F` and its laws -/

def genFunctor (ctx : Ctx) : CommandElabM Unit := do
  let pExp := ctx.pExp
  let pImp := ctx.pImp
  let fCtors ← ctx.ctors.mapM fun c => do
    let bs ← fBinders c
    `(Parser.Command.ctor| | $(c.name):ident $[$bs]*)
  elabCommand (← `(inductive $(ctx.F):ident $[$pExp]* (X : Type _) where $[$fCtors:ctor]*))
  -- `F.map`, and its computation on constructors.
  let mapAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.mapM fun c => do
    let lhs ← mkAppT (ctx.fCtor c) (c.args.map idT)
    let rhs ← mkAppT (ctx.fCtor c) (← mappedArgs c)
    `(matchAltExpr| | $lhs:term => $rhs:term)
  elabCommand (← `(def $(ctx.Fmap):ident $[$pImp]* {X Y : Type _} (f : X → Y)
      (a : $(ctx.Fp) X) : $(ctx.Fp) Y := match a with $mapAlts:matchAlt*))
  for c in ctx.ctors do
    let bs ← fBinders c
    let lhs ← mkAppT (ctx.fCtor c) (c.args.map idT)
    let rhs ← mkAppT (ctx.fCtor c) (← mappedArgs c)
    elabCommand (← `(@[simp] theorem $(ctx.nF ("map_" ++ c.name.getId.toString)):ident
        $[$pImp]* {X Y : Type _} (f : X → Y) $[$bs]* :
        $(ctx.Fmap) f ($lhs : $(ctx.Fp) X) = $rhs := rfl))
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
        unless g.implicit do
          xs := xs ++ g.ids.map idT
          ys := ys ++ g.ids.map idT
      | .pos =>
        for t in g.ids do
          let t' := prime t
          bs := bs.push (← `(bracketedBinderF| ($t : X)))
          bs := bs.push (← `(bracketedBinderF| ($t' : Y)))
          hyps := hyps.push (← `(bracketedBinderF| (_ : R $t $t')))
          xs := xs.push (idT t)
          ys := ys.push (idT t')
      | .fn dom =>
        for t in g.ids do
          let t' := prime t
          bs := bs.push (← `(bracketedBinderF| ($t : $dom → X)))
          bs := bs.push (← `(bracketedBinderF| ($t' : $dom → Y)))
          hyps := hyps.push (← `(bracketedBinderF| (_ : ∀ i, R ($t i) ($t' i))))
          xs := xs.push (idT t)
          ys := ys.push (idT t')
    let lhs ← mkAppT (ctx.fCtor c) xs
    let rhs ← mkAppT (ctx.fCtor c) ys
    `(Parser.Command.ctor| | $(c.name):ident $[$bs]* $[$hyps]* : $(ctx.Rel) R $lhs $rhs)
  elabCommand (← `(inductive $(ctx.Rel):ident $[$pImp]* {X Y : Type _} (R : X → Y → Prop) :
      $(ctx.Fp) X → $(ctx.Fp) Y → Prop where
    $[$relCtors:ctor]*))
  -- The functor laws.
  elabCommand (← `(theorem $(ctx.Fmap_id):ident $[$pImp]* {X : Type _} (a : $(ctx.Fp) X) :
      $(ctx.Fmap) id a = a := by
    cases a
    all_goals rfl))
  elabCommand (← `(theorem $(ctx.Fmap_comp):ident $[$pImp]* {X Y Z : Type _} (g : Y → Z)
      (f : X → Y) (a : $(ctx.Fp) X) : $(ctx.Fmap) (g ∘ f) a = $(ctx.Fmap) g ($(ctx.Fmap) f a) := by
    cases a
    all_goals rfl))
  elabCommand (← `(theorem $(ctx.Frel_map):ident $[$pImp]* {X Y Z : Type _}
      (R : Y → Z → Prop) (f : X → Y) (g : X → Z) (a : $(ctx.Fp) X) (h : ∀ x, R (f x) (g x)) :
      $(ctx.Rel) R ($(ctx.Fmap) f a) ($(ctx.Fmap) g a) := by
    cases a
    all_goals simp only [$(ctx.Fmap):ident]
    all_goals constructor
    all_goals intros
    all_goals apply h))

/-! ### The signature: shapes and positions -/

def genSignature (ctx : Ctx) : CommandElabM Unit := do
  let pExp := ctx.pExp
  let shapeCtors ← ctx.ctors.mapM fun c => do
    let bs ← (c.groups.filter (·.kind.isData)).mapM fun g => mkBinder g.implicit g.ids g.ty
    `(Parser.Command.ctor| | $(c.name):ident $[$bs]*)
  elabCommand (← `(inductive $(ctx.Shape):ident $[$pExp]* where $[$shapeCtors:ctor]*))
  let mut bCtors : Array (TSyntax ``Parser.Command.ctor) := #[]
  for c in ctx.ctors do
    let dbs ← dataBindersImplicit c
    let shape ← mkAppT (ctx.shapeCtor c) (c.dataArgs.map idT)
    for g in c.groups do
      match g.kind with
      | .data => pure ()
      | .pos =>
        for x in g.ids do
          bCtors := bCtors.push
            (← `(Parser.Command.ctor| | $(posCtorName c x):ident $[$dbs]* : $(ctx.Bp) $shape))
      | .fn dom =>
        for x in g.ids do
          bCtors := bCtors.push (← `(Parser.Command.ctor|
            | $(posCtorName c x):ident $[$dbs]* (i : $dom) : $(ctx.Bp) $shape))
  elabCommand (← `(inductive $(ctx.B):ident $[$pExp]* : $(ctx.Shapep) → Type _ where
    $[$bCtors:ctor]*))
  elabCommand (← `(def $(ctx.sig):ident $[$pExp]* : Signature where
    Shape := $(ctx.Shapep)
    B := $(ctx.Bp)))

/-! ### The isomorphism `F X ≃ σ.Obj X` and its three laws -/

def genIso (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let toCAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.mapM fun c => do
    let lhs ← mkAppT (ctx.fCtor c) (c.args.map idT)
    let shape ← mkAppT (ctx.shapeCtor c) (c.dataArgs.map idT)
    let mut alts : Array (TSyntax ``matchAlt) := #[]
    for g in c.groups do
      match g.kind with
      | .data => pure ()
      | .pos =>
        for x in g.ids do
          alts := alts.push (← `(matchAltExpr| | $(ctx.bCtor c x):ident => $x:ident))
      | .fn _ =>
        for x in g.ids do
          alts := alts.push (← `(matchAltExpr| | $(ctx.bCtor c x):ident i => $x:ident i))
    let child ← if alts.isEmpty then `(fun p => nomatch p) else
      `(fun p => match p with $alts:matchAlt*)
    `(matchAltExpr| | $lhs:term => ⟨$shape, $child⟩)
  elabCommand (← `(def $(ctx.toC):ident $[$pImp]* {X : Type _} (a : $(ctx.Fp) X) :
      Signature.Obj $(ctx.sigp) X := match a with $toCAlts:matchAlt*))
  let ofCAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.mapM fun c => do
    let shape ← mkAppT (ctx.shapeCtor c) (c.dataArgs.map idT)
    let mut args : Array Term := #[]
    for g in c.groups do
      if g.implicit then continue
      for x in g.ids do
        match g.kind with
        | .data => args := args.push (idT x)
        | .pos => args := args.push (← `(ch $(ctx.bCtor c x)))
        | .fn _ => args := args.push (← `(fun i => ch ($(ctx.bCtor c x) i)))
    let rhs ← mkAppT (ctx.fCtor c) args
    let pat ← if c.hasRec then `(⟨$shape, ch⟩) else `(⟨$shape, _⟩)
    `(matchAltExpr| | $pat:term => $rhs:term)
  elabCommand (← `(def $(ctx.ofC):ident $[$pImp]* {X : Type _}
      (z : Signature.Obj $(ctx.sigp) X) : $(ctx.Fp) X := match z with $ofCAlts:matchAlt*))
  elabCommand (← `(theorem $(ctx.ofC_toC):ident $[$pImp]* {X : Type _} (a : $(ctx.Fp) X) :
      $(ctx.ofC) ($(ctx.toC) a) = a := by
    cases a
    all_goals rfl))
  elabCommand (← `(theorem $(ctx.ofC_map):ident $[$pImp]* {X Y : Type _} (f : X → Y)
      (z : Signature.Obj $(ctx.sigp) X) :
      $(ctx.ofC) (Signature.Obj.map f z) = $(ctx.Fmap) f ($(ctx.ofC) z) := by
    obtain ⟨s, ch⟩ := z
    cases s
    all_goals rfl))
  elabCommand (← `(theorem $(ctx.rel_ofC):ident $[$pImp]* {X Y : Type _} (R : X → Y → Prop)
      (z : Signature.Obj $(ctx.sigp) X) (z' : Signature.Obj $(ctx.sigp) Y)
      (h : $(ctx.Rel) R ($(ctx.ofC) z) ($(ctx.ofC) z')) : Signature.Obj.Rel R z z' := by
    obtain ⟨s, ch⟩ := z
    obtain ⟨s', ch'⟩ := z'
    cases s
    all_goals cases s'
    all_goals try simp only [$(ctx.ofC):ident] at h
    all_goals cases h
    all_goals refine ⟨_, _, _, rfl, rfl, fun p => ?_⟩
    all_goals cases p
    all_goals solve_by_elim))

/-! ### The contract, and what is derived from it -/

def genContract (ctx : Ctx) : CommandElabM Unit := do
  let pExp := ctx.pExp
  let pImp := ctx.pImp
  elabCommand (← `(def $(ctx.T):ident $[$pExp]* := Signature.Cotype $(ctx.sigp)))
  elabCommand (← `(def $(ctx.dtor):ident $[$pImp]* (t : $(ctx.Tp)) : $(ctx.Fp) $(ctx.Tp) :=
    $(ctx.ofC) (Signature.dtorC t)))
  elabCommand (← `(def $(ctx.corec):ident $[$pImp]* {S : Type _} (c : S → $(ctx.Fp) S)
      (s : S) : $(ctx.Tp) := Signature.corecC (fun s => $(ctx.toC) (c s)) s))
  elabCommand (← `(theorem $(ctx.dtor_corec):ident $[$pImp]* {S : Type _}
      (c : S → $(ctx.Fp) S) (s : S) :
      $(ctx.dtor) ($(ctx.corec) c s) = $(ctx.Fmap) ($(ctx.corec) c) (c s) :=
    Signature.dtor_corec_of $(ctx.toC) $(ctx.ofC) $(ctx.ofC) $(ctx.Fmap) $(ctx.ofC_toC)
      $(ctx.ofC_map) c s))
  elabCommand (← `(theorem $(ctx.bisim):ident $[$pImp]* (R : $(ctx.Tp) → $(ctx.Tp) → Prop)
      (H : ∀ x y, R x y → $(ctx.Rel) R ($(ctx.dtor) x) ($(ctx.dtor) y)) {x y : $(ctx.Tp)}
      (h : R x y) : x = y :=
    Signature.bisim_of $(ctx.ofC) $(ctx.Rel) $(ctx.rel_ofC) R H h))

def genDerived (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  elabCommand (← `(def $(ctx.contract):ident $[$pImp]* :
      Codata.Contract $(ctx.Tp) $(ctx.Fp) where
    map := $(ctx.Fmap)
    Rel := $(ctx.Rel)
    map_id := $(ctx.Fmap_id)
    map_comp := $(ctx.Fmap_comp)
    rel_map := $(ctx.Frel_map)
    dtor := $(ctx.dtor)
    corec := $(ctx.corec)
    dtor_corec := $(ctx.dtor_corec)
    bisim := $(ctx.bisim)))
  elabCommand (← `(def $(ctx.ctor):ident $[$pImp]* : $(ctx.Fp) $(ctx.Tp) → $(ctx.Tp) :=
    Codata.Contract.ctor $(ctx.contract)))
  elabCommand (← `(theorem $(ctx.dtor_ctor):ident $[$pImp]* (y : $(ctx.Fp) $(ctx.Tp)) :
      $(ctx.dtor) ($(ctx.ctor) y) = y := Codata.Contract.dtor_ctor $(ctx.contract) y))
  elabCommand (← `(theorem $(ctx.ctor_dtor):ident $[$pImp]* (t : $(ctx.Tp)) :
      $(ctx.ctor) ($(ctx.dtor) t) = t := Codata.Contract.ctor_dtor $(ctx.contract) t))
  elabCommand (← `(theorem $(ctx.ctor_injective):ident $[$pImp]* :
      Function.Injective ($(ctx.ctor) : $(ctx.Fp) $(ctx.Tp) → $(ctx.Tp)) :=
    Codata.Contract.ctor_injective $(ctx.contract)))
  -- `corec_eq` and `corec_unique`, for states in any universe.
  elabCommand (← `(theorem $(ctx.corec_eq):ident $[$pImp]* {S : Type _}
      (c : S → $(ctx.Fp) S) (s : S) :
      $(ctx.corec) c s = $(ctx.ctor) ($(ctx.Fmap) ($(ctx.corec) c) (c s)) :=
    Codata.corec_eq_of $(ctx.dtor) $(ctx.ctor) $(ctx.corec) $(ctx.Fmap) $(ctx.dtor_corec)
      $(ctx.ctor_dtor) c s))
  elabCommand (← `(theorem $(ctx.corec_unique):ident $[$pImp]* {S : Type _}
      (c : S → $(ctx.Fp) S) (h : S → $(ctx.Tp)) (hh : ∀ s, $(ctx.dtor) (h s) = $(ctx.Fmap) h (c s))
      (s : S) : h s = $(ctx.corec) c s :=
    Codata.corec_unique_of $(ctx.dtor) $(ctx.corec) $(ctx.Fmap) $(ctx.Rel) $(ctx.bisim)
      $(ctx.dtor_corec) $(ctx.Frel_map) c h hh s))

/-- The individual constructors, with their destructor equations, the `ctor` equations,
injectivity and disjointness. -/
def genCtors (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  for c in ctx.ctors do
    let cId := ctx.tCtor c
    let bs ← binders c
    let args := c.args.map idT
    let fapp ← mkAppT (ctx.fCtor c) args
    let capp ← mkAppT cId args
    elabCommand (← `(def $cId:ident $[$pImp]* $[$bs]* : $(ctx.Tp) := $(ctx.ctor) $fapp))
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "dtor_" ""):ident $[$pImp]* $[$bs]* :
        $(ctx.dtor) ($capp : $(ctx.Tp)) = $fapp := $(ctx.dtor_ctor) $fapp))
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "ctor_" ""):ident $[$pImp]* $[$bs]* :
        $(ctx.ctor) ($fapp : $(ctx.Fp) $(ctx.Tp)) = $capp := rfl))
  for c in ctx.ctors do
    if c.args.isEmpty || c.hasImplicit then continue
    let bs ← binders c
    let bs' ← binders' c
    let capp ← mkAppT (ctx.tCtor c) (c.args.map idT)
    let capp' ← mkAppT (ctx.tCtor c) ((c.args.map prime).map idT)
    let eqs ← (c.args.zip (c.args.map prime)).mapM fun (x, x') => `($x:ident = $x':ident)
    let conj ← eqs.foldrM (init := eqs.back!) (start := eqs.size - 1) fun e acc => `($e ∧ $acc)
    let injEq := mkIdent (ctx.F.getId ++ c.name.getId ++ `injEq)
    let fapp ← mkAppT (ctx.fCtor c) (c.args.map idT)
    let fapp' ← mkAppT (ctx.fCtor c) ((c.args.map prime).map idT)
    let args := c.args.map idT ++ (c.args.map prime).map idT
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "" "_inj"):ident $[$pImp]* $[$bs]*
        $[$bs']* : ($capp : $(ctx.Tp)) = $capp' ↔ $conj :=
      Codata.inj_of $(ctx.ctor) $(ctx.ctor_injective) $fapp $fapp' ($injEq $args:term*)))
  for c in ctx.ctors do
    for c' in ctx.ctors do
      if c.name.getId == c'.name.getId then continue
      let bs ← binders c
      let bs' ← binders' c'
      let capp ← mkAppT (ctx.tCtor c) (c.args.map idT)
      let capp' ← mkAppT (ctx.tCtor c') ((c'.args.map prime).map idT)
      let name := mkIdent (ctx.tName ++
        Name.mkSimple (c.name.getId.toString ++ "_ne_" ++ c'.name.getId.toString))
      let dtorC ← mkAppT (ctx.tName' c "dtor_" "") (c.args.map idT)
      let dtorC' ← mkAppT (ctx.tName' c' "dtor_" "") ((c'.args.map prime).map idT)
      elabCommand (← `(@[simp] theorem $name:ident $[$pImp]* $[$bs]* $[$bs']* :
          ($capp : $(ctx.Tp)) ≠ $capp' :=
        Codata.ne_of $(ctx.dtor) $dtorC $dtorC' fun h => nomatch h))

/-- Case analysis: `t = ctor (dtor t)`, and `dtor t` is an inductive value. -/
def genCases (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let pTerms := ctx.pTerms
  let minors ← ctx.ctors.mapM fun c => do
    let bs ← binders c
    let capp ← mkAppT (ctx.tCtor c) (c.args.map idT)
    let ty ← if c.groups.isEmpty then `(motive $capp) else `(∀ $[$bs]*, motive $capp)
    `(bracketedBinderF| ($(c.name) : $ty))
  let auxAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.mapM fun c => do
    let args := c.args.map idT
    let pat ← mkAppT (ctx.fCtor c) args
    let rhs ← mkAppT c.name args
    `(matchAltExpr| | $pat:term => $rhs:term)
  elabCommand (← `(def $(ctx.casesOnAux):ident $[$pImp]* {motive : $(ctx.Tp) → Sort _}
      (y : $(ctx.Fp) $(ctx.Tp)) $[$minors]* : motive ($(ctx.ctor) y) :=
    match y with $auxAlts:matchAlt*))
  let minorIds := ctx.ctors.map fun c => idT c.name
  elabCommand (← `(@[elab_as_elim, cases_eliminator]
    def $(ctx.casesOnId):ident $[$pImp]* {motive : $(ctx.Tp) → Sort _} (t : $(ctx.Tp))
        $[$minors]* : motive t :=
      (congrArg motive ($(ctx.ctor_dtor) t)).mp
        ($(ctx.casesOnAux) ($(ctx.dtor) t) $minorIds:term*)))
  -- Its computation rules: the cast disappears once `dtor (ctor y) = y` is substituted.
  elabCommand (← `(theorem $(ctx.casesOn_ctor):ident $[$pImp]* {motive : $(ctx.Tp) → Sort _}
      (y : $(ctx.Fp) $(ctx.Tp)) $[$minors]* :
      @$(ctx.casesOnId) $pTerms:term* motive ($(ctx.ctor) y) $minorIds:term* =
        $(ctx.casesOnAux) y $minorIds:term* :=
    Codata.cast_ctor_dtor $(ctx.ctor) $(ctx.dtor) $(ctx.ctor_dtor) $(ctx.dtor_ctor)
      (fun y => $(ctx.casesOnAux) y $minorIds:term*) y))
  for c in ctx.ctors do
    let bs ← binders c
    let args := c.args.map idT
    let capp ← mkAppT (ctx.tCtor c) args
    let fapp ← mkAppT (ctx.fCtor c) args
    let rhs ← mkAppT c.name args
    elabCommand (← `(@[simp] theorem $(ctx.tName' c "casesOn_" ""):ident $[$pImp]*
        {motive : $(ctx.Tp) → Sort _} $[$bs]* $[$minors]* :
        @$(ctx.casesOnId) $pTerms:term* motive $capp $minorIds:term* = $rhs :=
      $(ctx.casesOn_ctor) $fapp $minorIds:term*))

/-! ### The command -/

@[command_elab codataCmd] def elabCodata : CommandElab := fun stx => do
  let `(codata $T:ident $paramsStx:bracketedBinder* $ctorsStx:codataCtor*) := stx
    | throwUnsupportedSyntax
  let tName := T.getId
  let toIdents (b : Syntax) (ids : TSyntaxArray [`ident, ``Parser.Term.hole]) :
      CommandElabM (Array Ident) := do
    unless ids.all (·.raw.isIdent) do throwErrorAt b "binders must be named"
    return ids.map fun x => ⟨x.raw⟩
  let readBinder (b : TSyntax ``bracketedBinder) : CommandElabM (Array Ident × Term × Bool) := do
    match b with
    | `(bracketedBinderF| ($ids* : $ty)) => return (← toIdents b ids, ty, false)
    | `(bracketedBinderF| {$ids* : $ty}) => return (← toIdents b ids, ty, true)
    | _ => throwErrorAt b "unsupported binder: expected an explicit or implicit binder with a type"
  let params ← paramsStx.mapM fun b => do
    let (ids, ty, _) ← readBinder b
    return (ids, ty)
  let pids : Array Ident := params.foldl (fun acc (ids, _) => acc ++ ids) #[]
  let pExp ← params.mapM fun (ids, ty) => `(bracketedBinderF| ($ids* : $ty))
  let pImp ← params.mapM fun (ids, ty) => `(bracketedBinderF| {$ids* : $ty})
  let ctors : Array CtorInfo ← ctorsStx.mapM fun c => do
    let `(codataCtor| | $name:ident $bs:bracketedBinder*) := c | throwUnsupportedSyntax
    let raw ← bs.mapM readBinder
    let groups := raw.map fun (ids, ty, implicit) =>
      { ids, ty, kind := classify tName pids ty, implicit : Group }
    for g in groups do
      if g.implicit && !g.kind.isData then
        throwErrorAt g.ty "implicit binders must not be recursive"
    return { name, groups }
  let n (s : String) : Ident := mkIdent (.str tName s)
  let nF (s : String) : Ident := mkIdent (.str (.str tName "F") s)
  let pTerms := pids.map idT
  let ctx : Ctx := {
    T, tName, pids, pExp, pImp, pTerms, ctors
    F := n "F", Shape := n "Shape", B := n "B", sig := n "sig"
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
