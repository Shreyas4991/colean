import Colean.MutualCmd

/-!
# A tour of nested types

What the `data` and `codata` commands accept as a nested argument today, and what they do not.
Read it top to bottom. Part I (sections 1 to 8) is what works, Part II (sections 9 to 14) what does
not work yet but could, and Part III failures that look like bugs of the commands rather than
limits; there are none at the moment.

How the file is checked:

* an example without an error on it works;
* the failures of Parts II and III are left as they are, so they show as errors in the infoview;
* in Part II a failed `data`/`codata` declares nothing, so the names of failed types do not
  exist; a failed instance generation is only a warning, and the type itself is declared;
* the absence of an instance is shown by a failing `#synth`.

A word used throughout. A *leaf* is a named type constructor applied in a nested argument, such
as `List` in `List T`. The command looks for instances at leaves only; everything else it reads
off the elaborated type of the argument (`occOf` in `Colean/Gen/Occ.lean`).
-/

universe u v

namespace NestingTour

open Codata

noncomputable section

/-! ## Part I: what works -/

/-! ### 1. Built-in forms, no instance needed

Products, sums, functions and dependent pairs are recognised by their head once elaborated, so
they need no instance and may be combined at any depth. The domain of a function and the first
component of a dependent pair must be constant. They have instances all the same, built from
those of their parts (`PolyIso.lean`): the induction hypotheses are stated with them
(section 8), and a leaf with several holes can take them (`EProdBoth`, section 5). -/

-- `T × T`: two recursive occurrences in one argument.
data BinT
  | leaf
  | node (c : BinT × BinT)

-- `T ⊕ A`: an occurrence on one side of a sum.
data Tm (α : Type u)
  | var (a : α)
  | app (f : Tm α ⊕ α) (arg : Tm α)

-- `A → T`: infinitely branching, a recursive argument under an arrow.
data Omega
  | leaf
  | node (k : Nat → Omega)

-- `A → List T`: a function into a leaf.
codata Proc (α : Type u)
  | act (k : α → List (Proc α))
  | stop

-- `(n : Nat) × (Fin n → T)`: the second component depends on the first.
data SizedRose
  | node (c : (n : Nat) × (Fin n → SizedRose))

-- A function from a proposition: `k` gives children only when `0 < n`, and `n` is an earlier field.
data Guarded
  | mk (n : Nat) (k : 0 < n → List Guarded)

-- All of them at once: the depth does not matter.
codata Deep (α : Type u)
  | mk (a : α) (c : (n : Nat) × (Fin n → List (Deep α × (Nat ⊕ Deep α))))

-- The same in a `data`, with a proposition and a dependent function on the way.
data DeepFin
  | leaf
  | mk (c : (n : Nat) → n = 0 → (Fin n → DeepFin) × Option (DeepFin ⊕ Nat))

/-! ### 2. Library leaves

`List`, `Option` and `Array` have instances in `Colean/PolyIso.lean`. Leaves compose with each
other and with the forms of section 1. -/

-- The rose tree, with `List`.
codata ListRose (α : Type u)
  | node (a : α) (cs : List (ListRose α))

-- A possibly ending stream, with `Option`.
codata OptStream (α : Type u)
  | cons (a : α) (tail : Option (OptStream α))

-- With `Array`.
data ArrRose
  | node (cs : Array ArrRose)

-- `List (Option T)`, a composite of two leaves.
data OptRose (α : Type u)
  | node (a : α) (cs : List (Option (OptRose α)))

-- A leaf outside a built-in form, and a built-in form outside a leaf.
data Mixed
  | leaf
  | node (c : Option (Mixed × Mixed)) (d : Nat → Array (List Mixed))

/-! ### 3. A user's functor, with hand-written instances

Two instances make a type constructor a leaf: `PolyIso` presents it as a polynomial functor,
`PolyMap` gives the intended map across two universes, and its naturality. -/

structure Box (X : Type u) where
  val : X

instance : PolyIso Box.{u} Unit (fun _ => Unit) where
  equiv := ⟨fun b => ⟨(), fun _ => b.val⟩, fun z => ⟨z.2 ()⟩, fun _ => rfl, fun _ => rfl⟩

instance : PolyMap Box.{u} Box.{v} where
  map f b := ⟨f b.val⟩
  equiv_map _ _ := rfl

-- Through `Box`, in both kinds.
codata BoxStream (α : Type u)
  | cons (a : α) (tail : Box (BoxStream α))

data BoxList (α : Type u)
  | nil
  | cons (a : α) (tail : Box (BoxList α))

-- The instances compose with everything above.
codata BoxTree
  | node (children : List (Box BoxTree × Option (Box BoxTree)))

/-- The state of `corec` may live in any universe: that is what `PolyMap Box.{u} Box.{v}` buys. -/
example : ∀ {α : Type u} {S : Type v}, (S → BoxStream.F α S) → S → BoxStream α := BoxStream.corec

/-! A leaf with a constant argument takes an instance for the partial application, one for each
constant, or for all of them at once. -/

structure Labelled (A : Type) (X : Type u) where
  label : A
  val : X

instance (A : Type) : PolyIso (Labelled.{u} A) A (fun _ => Unit) where
  equiv := ⟨fun b => ⟨b.label, fun _ => b.val⟩, fun z => ⟨z.1, z.2 ()⟩, fun _ => rfl, fun _ => rfl⟩

instance (A : Type) : PolyMap (Labelled.{u} A) (Labelled.{v} A) where
  map f b := ⟨b.label, f b.val⟩
  equiv_map _ _ := rfl

data LabelledList
  | nil
  | cons (tail : Labelled Nat LabelledList)

/-! The command checks `PolyMap G G` at one universe only, so an instance between two copies of
one universe passes. The type is then complete, but `corec` has lost its freedom: the state must
live in that universe. -/

structure MonoBox (X : Type u) where
  val : X

instance : PolyIso MonoBox.{0} Unit (fun _ => Unit) where
  equiv := ⟨fun b => ⟨(), fun _ => b.val⟩, fun z => ⟨z.2 ()⟩, fun _ => rfl, fun _ => rfl⟩

instance : PolyMap MonoBox.{0} MonoBox.{0} where
  map f b := ⟨f b.val⟩
  equiv_map _ _ := rfl

codata MonoStream
  | cons (t : MonoBox MonoStream)

/-- info: @MonoStream.corec : {S : Type} → (S → MonoStream.F S) → S → MonoStream -/
#guard_msgs in
#check @MonoStream.corec

/-! A generic fixpoint of a functor with instances: the instances are parameters of the type. -/

data FixInst (G : Type → Type) (Sh : Type) (Pos : Sh → Type) [PolyIso G Sh Pos] [PolyMap G G]
  | mk (x : G (FixInst G Sh Pos))

/-! ### 4. Declared types, with generated instances

A `data` or `codata` gets `PolyIso` and `PolyMap` by itself, in a separate step after the
declaration (`Colean/Gen/Derive.lean`); families and the types of blocks too, at every index (the
end of section 6). Nothing is written by hand from here to the end of section 5. -/

data L (α : Type u)
  | nil
  | cons (a : α) (t : L α)

codata Str (α : Type u)
  | cons (a : α) (t : Str α)

/-- info: L.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso L.{0} _ _

/-- info: Str.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso Str.{0} _ _

/-- info: L.Poly.instPolyMapEta -/
#guard_msgs in
#synth PolyMap L.{0} L.{1}

-- `data` through `data`: finite trees with finitely many children.
data LRose
  | node (cs : L LRose)

-- `codata` through `data`: trees of any depth, each node with finitely many children.
codata LInf
  | node (cs : L LInf)

-- `data` through `codata`: a well-founded tree with a stream of children at each node. Lean's
-- `inductive` has no counterpart for this: it nests through inductive types only.
data Bush
  | leaf
  | node (c : Str Bush)

-- `codata` through `codata`.
codata CoBush
  | node (c : Str CoBush)

-- A composite: the generated instance takes an instance as a premise.
codata LList
  | node (c : L (List LList))

-- Three declared and library leaves in one argument, across kinds.
data Tower
  | leaf
  | node (c : L (Str (Option Tower)))

-- A declared type with a nested field is itself nested through: the instances chain.
data Rose₁ (α : Type u)
  | node (a : α) (cs : L (Rose₁ α))

data Rose₂
  | mk (r : Rose₁ Rose₂)

/-! ### 5. Several parameters

One generated instance covers `fun X => E (H₁ X) (H₂ X)` for `H₁`, `H₂` themselves instances,
constants and the identity among them. So every line below is the same instance. -/

data E (α β : Type u)
  | l (a : α)
  | r (b : β)

/-- info: E.Poly.instPolyIso -/
#guard_msgs in
#synth PolyIso (fun X : Type u => E X X) _ _

/-- info: E.Poly.instPolyIso -/
#guard_msgs in
#synth PolyIso (fun X : Type => E X Nat) _ _

/-- info: E.Poly.instPolyIsoEta ℕ -/
#guard_msgs in
#synth PolyIso (E Nat) _ _

/-- info: E.Poly.instPolyIso -/
#guard_msgs in
#synth PolyIso (fun X : Type u => E (List X) (Option X)) _ _

-- `E T T`.
data ETT
  | leaf
  | mk (p : E ETT ETT)

-- `E Nat T`.
codata ENT
  | mk (p : List (E Nat ENT))

-- `E T Nat`.
data ETN
  | leaf
  | mk (p : E ETN Nat)

-- `E (List T) (Option T)`.
data EComp
  | leaf
  | mk (p : E (List EComp) (Option EComp))

-- Declared leaves in both arguments, one inductive and one coinductive.
data EDecl
  | leaf
  | mk (p : E (L EDecl) (Str EDecl))

-- With one argument mentioning `T`, that argument may be anything: `×` is fine here, since the
-- leaf is `fun X => E X Nat` and the command goes on inside the argument.
data EProd
  | leaf
  | mk (p : E (EProd × Nat) Nat)

-- With `T` in both arguments, the leaf is the whole `fun X => E (X × Nat) X`, found by instance
-- search, which needs an instance at `fun X => X × Nat`: products, sums, functions and dependent
-- pairs of functors with instances have instances (`PolyIso.lean`).
data EProdBoth
  | leaf
  | mk (p : E (EProdBoth × Nat) EProdBoth)

/-- info: PolyIso.instProd -/
#guard_msgs in
#synth PolyIso (fun X : Type => X × Nat) _ _

/-! A parameter may vary when it sits in fields with an occurrence structure in it. All these
kinds of field count, and the parameters may live in different universes. -/

data Fields (α : Type u)
  | mk (x : Option (List α)) (y : Nat → α) (z : (n : Nat) × (Fin n → α)) (w : α ⊕ Nat)
       (s : L α) (e : E α (List α)) (t : Fields α)

/-- info: Fields.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso Fields.{0} _ _

data TwoUniv (α : Type u) (β : Type v)
  | l (a : α)
  | r (b : β)

data UseTwoUniv
  | leaf
  | mk (x : TwoUniv UseTwoUniv UseTwoUniv)

/-! A parameter that may not vary is constant, and the rest still works: `A` in `Fn` is a domain,
and `n` in `FinFn` is not a type. -/

data Fn (A : Type) (α : Type u)
  | leaf (a : α)
  | node (k : A → Fn A α)

data UseFn
  | mk (f : Fn Nat UseFn)

data FinFn (n : Nat) (α : Type u)
  | mk (v : Fin n → α)

data UseFinFn
  | leaf
  | mk (x : FinFn 3 UseFinFn)

/-! Degenerate cases are fine too: a parameter that is never used, and no constructors at all. -/

data Phantom (α : Type u)
  | mk (n : Nat)

data UsePhantom
  | mk (x : Phantom UsePhantom)

codata Void (α : Type u)

/-- info: Void.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso Void.{0} _ _

/-! ### 6. Indexed families and mutual blocks

Here leaves come from sections 2 and 3, or from section 4: the enclosing type may be a family or
a block. A family may have several indices, and so may the types of a block. At the end of the
section the leaf is itself a family or a type of a block, with generated instances. -/

-- A family through a plain leaf.
codata BoxVec (α : Type u) : Nat → Type u
  | nil : BoxVec α 0
  | cons {n : Nat} (a : α) (tail : Box (BoxVec α n)) : BoxVec α (n + 1)

-- The same with `List`, and with a generated leaf.
data LevelRose : Nat → Type
  | leaf : LevelRose 0
  | node {n : Nat} (cs : List (LevelRose n)) : LevelRose (n + 1)

data LevelL : Nat → Type
  | leaf : LevelL 0
  | node {n : Nat} (cs : L (LevelL n)) : LevelL (n + 1)

-- A mutual block, through a plain leaf and a generated one.
mutual
data Even
  | zero
  | succ (o : L Odd)
data Odd
  | succ (e : Box Even)
end

-- Occurrences at several indices, through built-in forms.
data Chain : Nat → Type
  | zero : Chain 0
  | link {n : Nat} (p : Chain n × Chain (n + 1)) : Chain (n + 2)

-- The index may depend on a variable bound on the way.
data ByIndex : Nat → Type
  | zero : ByIndex 0
  | mk {m : Nat} (c : (n : Nat) × (Fin n → ByIndex n)) : ByIndex (m + 1)

codata ByArg : Nat → Type
  | mk {m : Nat} (c : (k : Nat) → List (ByArg k)) : ByArg m

-- Several arguments of a leaf are fine at one index: `E` at `n` in both.
data OneIndex : Nat → Type
  | zero : OneIndex 0
  | mk {n : Nat} (p : E (List (OneIndex n)) (Option (OneIndex n))) : OneIndex (n + 2)

/-! A functor on families has `IPolyIso` and `IPolyMap` instances, where each position says at
which index its child lives. It takes a family `fun c => …`, and is what lets a single leaf hold
occurrences at several indices. -/

structure Both (X : Bool → Type u) where
  yes : X true
  no : X false

instance : IPolyIso Both.{u} Unit (fun _ => Bool) (fun _ b => b) where
  equiv :=
    { toFun := fun t => ⟨(), fun b => match b with | true => t.yes | false => t.no⟩
      invFun := fun z => ⟨z.2 true, z.2 false⟩
      left_inv := fun _ => rfl
      right_inv := fun ⟨_, c⟩ => congrArg (Sigma.mk ()) (funext fun b => by cases b <;> rfl) }

instance : IPolyMap Both.{u} Both.{v} where
  map f t := ⟨f _ t.yes, f _ t.no⟩
  equiv_map f t := congrArg (Sigma.mk ()) (funext fun b => by cases b <;> rfl)

-- The family at its own index.
codata Alt : Bool → Type
  | mk {b : Bool} (children : Both (fun c => Alt c)) : Alt b

-- Reindexed.
codata Flip : Bool → Type
  | mk {b : Bool} (children : Both (fun c => Flip (!c))) : Flip b

-- A plain leaf inside, and outside.
codata AltIn : Bool → Type
  | mk {b : Bool} (children : Both (fun c => List (AltIn c))) : AltIn b

codata AltOut : Bool → Type
  | mk {b : Bool} (children : List (Both (fun c => AltOut c))) : AltOut b

-- In a `data`, with a built-in form inside.
data AltFin : Bool → Type
  | leaf {b : Bool} : AltFin b
  | mk {b : Bool} (children : Option (Both (fun c => AltFin c × Nat))) : AltFin b

-- On a plain type too, the family ignoring its index, with a named binder or not.
codata AltPlain
  | mk (children : Both (fun _b => AltPlain))

codata AnonFamily
  | mk (children : Both (fun _ => AnonFamily))

/-! Several indices, through a plain leaf and through built-in forms, in both kinds. These failed
in the generated proofs until the commands moved to `Expr`. -/

codata TwoListCo : Nat → Nat → Type
  | mk {n m : Nat} (c : List (TwoListCo n m)) : TwoListCo (n + 1) m

codata TwoProdCo : Nat → Nat → Type
  | mk {n m : Nat} (c : Nat × TwoProdCo n m) : TwoProdCo (n + 1) m

data TwoFn : Nat → Nat → Type
  | nil : TwoFn 0 0
  | mk {n m : Nat} (c : Nat → TwoFn n m) : TwoFn (n + 1) m

data TwoProd : Nat → Nat → Type
  | nil : TwoProd 0 0
  | mk {n m : Nat} (c : Nat × TwoProd n m) : TwoProd (n + 1) m

/-! Families and the types of blocks are leaves too, with generated instances at every index:
`PolyIso (fun X => Vec (H X) n)` for each `n`, an argument of the instance, and for a type of a
block at its index of the block. -/

data Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (t : Vec α n) : Vec α (n + 1)

/-- info: Vec.Poly.instPolyIso 3 -/
#guard_msgs in
#synth PolyIso (fun X : Type => Vec X 3) _ _

-- At a fixed index.
data ThroughVec
  | leaf
  | mk (v : Vec ThroughVec 3)

-- A family through a family, at its own index.
data VTree : Nat → Type
  | leaf : VTree 0
  | node {n : Nat} (cs : Vec (VTree n) n) : VTree (n + 1)

-- The types of a block.
mutual
data Ping (α : Type u)
  | nil
  | cons (a : α) (b : Pong α)
data Pong (α : Type u)
  | cons (a : α) (b : Ping α)
end

/-- info: Ping.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso Ping.{0} _ _

data ThroughPing
  | leaf
  | mk (v : Ping ThroughPing)

-- The types of a block with indices, in `codata`.
mutual
codata Ev (α : Type u) : Nat → Type u
  | zero (a : α) : Ev α 0
  | succ {n : Nat} (o : Od α n) : Ev α (n + 1)
codata Od (α : Type u) : Nat → Type u
  | succ {n : Nat} (a : α) (e : Ev α n) : Od α (n + 1)
end

data ThroughOd
  | leaf
  | mk (o : Od ThroughOd 3)

/-! A hand-written instance still works, and is the one found, being declared after the generated
one: here a presentation simpler than the trees of shapes. First for a family at a fixed index,
whichever it is. -/

data Tagged (α : Type u) : Bool → Type u
  | mk {b : Bool} (a : α) : Tagged α b

def Tagged.val {α : Type u} {b : Bool} (t : Tagged α b) : α :=
  Tagged.casesOn (motive := fun _ _ => α) t id

@[simp] theorem Tagged.val_mk {α : Type u} {b : Bool} (a : α) :
    (Tagged.mk a : Tagged α b).val = a := by
  simp [Tagged.val]

instance (b : Bool) : PolyIso (fun X : Type u => Tagged X b) Unit (fun _ => Unit) where
  equiv :=
    { toFun := fun t => ⟨(), fun _ => t.val⟩
      invFun := fun z => .mk (z.2 ())
      left_inv := fun t => by cases t with | mk a => simp
      right_inv := fun _ => by simp }

instance (b : Bool) : PolyMap (fun X : Type u => Tagged X b) (fun X : Type v => Tagged X b) where
  map f t := .mk (f t.val)
  equiv_map f t := by simp [Equiv.coe_fn_mk, PolyIso.equiv, Poly.map]

data ThroughTagged
  | leaf
  | mk (v : Tagged ThroughTagged true)

/-! Then for a type of a block. -/

mutual
data Hand (α : Type u)
  | mk (a : α) (b : Stop α)
data Stop (α : Type u)
  | stop
end

def Hand.val {α : Type u} (t : Hand α) : α :=
  Hand.casesOn (motive := fun _ => α) t fun a _ => a

@[simp] theorem Hand.val_mk {α : Type u} (a : α) (b : Stop α) : (Hand.mk a b).val = a := by
  simp [Hand.val]

instance : PolyIso Hand.{u} Unit (fun _ => Unit) where
  equiv :=
    { toFun := fun t => ⟨(), fun _ => t.val⟩
      invFun := fun z => .mk (z.2 ()) .stop
      left_inv := fun t => by
        cases t with
        | mk a b => cases b with | stop => simp
      right_inv := fun _ => by simp }

instance : PolyMap Hand.{u} Hand.{v} where
  map f t := .mk (f t.val) .stop
  equiv_map f t := by simp [Equiv.coe_fn_mk, PolyIso.equiv, Poly.map]

data ThroughHand
  | leaf
  | mk (v : Hand ThroughHand)

/-! ### 7. Spellings

The analysis works on the elaborated type of an argument, so a type spelled differently is the
same type: prefix `Prod` and `Sum`, an abbreviation, `id`, `<|`, `Σ`, `∀`, an implicit binder.
These were refused while the analysis read the syntax. -/

data PrefixProd
  | leaf
  | mk (p : Prod PrefixProd PrefixProd)

data PrefixProd₂
  | leaf
  | mk (p : Prod Nat PrefixProd₂)

data PrefixSum
  | leaf
  | mk (p : Sum PrefixSum Nat)

abbrev Twice (X : Type u) := X × X

data ThroughAbbrev
  | leaf
  | mk (p : Twice ThroughAbbrev)

data ThroughId
  | leaf
  | mk (p : id ThroughId)

data ThroughPipe
  | leaf
  | mk (p : Option <| List ThroughPipe)

data ThroughSigma
  | leaf
  | mk (p : Σ n : Nat, Fin n → ThroughSigma)

data ThroughForall
  | leaf
  | mk (p : ∀ n : Nat, Fin n → ThroughForall)

-- An implicit binder in a nested argument stays implicit in `T.F` and in the constructor.
data ImplicitPi
  | leaf
  | mk (k : {n : Nat} → List ImplicitPi)

/-! ### 8. Using a nested type

`fold`, `corec` and the lemmas about them see the leaf: the argument of a nested constructor of
`T.F` has the leaf applied to the state. To compute through it, `Occ.map_list`, `Occ.map_prod`,
`Occ.map_ofIso` and friends turn the generated map into the map of the leaf. -/

data URose (α : Type u)
  | node (a : α) (cs : List (URose α))

/-- The number of nodes: the children arrive already folded. -/
def URose.size {α : Type u} (t : URose α) : Nat :=
  URose.fold (S := Nat) (fun | .node _ cs => cs.sum + 1) t

@[simp] theorem URose.size_node {α : Type u} (a : α) (cs : List (URose α)) :
    (URose.node a cs).size = (cs.map URose.size).sum + 1 := by
  rw [URose.size, URose.fold_node, Occ.map_list]
  rfl

theorem URose.size_pos {α : Type u} (t : URose α) : 0 < t.size := by
  cases t with
  | node a cs => simp

/-! The recursor states the induction hypothesis of a nested argument by membership, for the
functor of the argument's type: `∀ t, PolyIso.Mem (fun X => List X) t cs → motive t` here,
`PolyIso.Mem (fun X => X × Option X) t children` for `UTree` below, and by `IPolyIso.Mem` at an
index when the positions of a family's argument are at several indices. The `simp` lemmas of
`PolyIso.lean` turn membership into the container's own (`mem_list`, `mem_option`) or into
components (`mem_prod`, `mem_comp`, …), so a function by the recursor can use `List.attach`. -/

/--
info: @URose.rec : {α : Type u_1} →
  {motive : URose α → Sort u_2} →
    ((a : α) →
        (cs : List (URose α)) →
          ((t : URose α) → PolyIso.Mem (fun X => List X) t cs → motive t) → motive (URose.node a cs)) →
      (t : URose α) → motive t
-/
#guard_msgs in
#check @URose.rec

/-- The number of nodes again, by the recursor. -/
def URose.size' {α : Type u} : URose α → Nat :=
  URose.rec (motive := fun _ => Nat) fun _ cs ih =>
    (cs.attach.map fun x => ih x.1 ((PolyIso.mem_list _ _).mpr x.2)).sum + 1

/-- The rule `URose.rec_node` gives the hypothesis as `fun t _ => URose.rec … t`. -/
@[simp] theorem URose.size'_node {α : Type u} (a : α) (cs : List (URose α)) :
    (URose.node a cs).size' = (cs.map URose.size').sum + 1 := by
  simp [URose.size', List.map_attach_eq_pmap]

/-- Induction: the hypothesis at the members of the list. -/
theorem URose.size'_eq {α : Type u} (t : URose α) : t.size' = t.size := by
  induction t with
  | node a cs ih =>
    simp only [PolyIso.mem_list] at ih
    rw [URose.size'_node, URose.size_node, List.map_congr_left ih]

codata UTree (α : Type u)
  | node (a : α) (children : UTree α × Option (UTree α))

/-- The tree with `a` everywhere, as a `corec` with one state. -/
def UTree.const {α : Type u} (a : α) : UTree α :=
  UTree.corec (S := Unit) (fun _ => .node a ((), some ())) ()

@[simp] theorem UTree.dtor_const {α : Type u} (a : α) :
    (UTree.const a).dtor = .node a (UTree.const a, some (UTree.const a)) := by
  rw [UTree.const, UTree.dtor_corec]
  simp [UTree.F.map_node, Occ.map_prod, Occ.map_hole, Occ.map_option]

/-! Through a generated leaf the definitions are as easy, with the leaf's own `fold`, or its
constructors in a `corec`. The lemmas stop earlier: `Occ.map_ofIso` turns the generated map into
`PolyMap.map` of the leaf, and there are no lemmas for that map on constructors yet (plan,
section 4). So the theorem below stops at the generated map on `L.cons`. -/

/-- The number of nodes of an `LRose`: `L.fold` sums the folded children. -/
def LRose.size (t : LRose) : Nat :=
  LRose.fold (S := Nat)
    (fun | .node cs => L.fold (S := Nat) (fun | .nil => 0 | .cons a n => a + n) cs + 1) t

/-- A tree with one child at every node. -/
def LInf.spine : LInf :=
  LInf.corec (S := Unit) (fun _ => .node (L.cons () .nil)) ()

theorem LInf.dtor_spine :
    LInf.spine.dtor =
      .node (Occ.map (Occ.ofIso L) (Occ.ofIso L) (fun _ => LInf.spine) (L.cons () .nil)) := by
  rw [LInf.spine, LInf.dtor_corec, LInf.F.map_node]

/-! ## Part II: what does not work yet

Everything here could be supported. What should stay rejected is not listed: negative
occurrences, functors that are not polynomial such as `Finset`, parameters that later types depend
on, fields whose type depends on a recursive field, non-uniform parameters, and a `PolyIso` without
its `PolyMap`. The section on `mixed_mutual` is gone with the command, removed pending a
redesign. -/

/-! ### 9. Missing instances

A plain `structure` gets no instance: only `data` and `codata` generate them. Nothing in it stops
one from being generated when a declaration nests through it (`todo.md`). -/

structure NoIso (X : Type u) where
  val : X

codata NeedsIso
  | mk (x : NoIso NeedsIso)

/-! The same for functors on families. -/

structure NoFamIso (X : Bool → Type u) where
  yes : X true

codata NeedsFamIso : Bool → Type
  | mk {b : Bool} (children : NoFamIso (fun c => NeedsFamIso c)) : NeedsFamIso b

/-! ### 10. A parameter in the same field as a recursive occurrence

Such a parameter cannot vary yet, even though the field is positive in both. The field would
need positions of both kinds, and the generator takes a field as one or the other. So `Str` of
section 4 can be nested through, and the same stream as a pair cannot; neither can `Tm` of
section 1, because of `f : Tm α ⊕ α`. Splitting the field is the way out when the type allows
it. -/

codata PairStr (α : Type u)
  | mk (p : α × PairStr α)

#synth PolyIso PairStr.{0} _ _

#synth PolyIso Tm.{0} _ _

data ThroughPairStr
  | leaf
  | mk (x : PairStr ThroughPairStr)

/-! ### 11. A field mentioning two varying parameters

Here is what happens with `p : α × β`: both parameters count as constant, so nothing is
generated for them, silently, and neither `P2 T Nat` nor `P2 Nat T` can be nested through. The
reason is that a field is presented in one hole at a time. -/

data P2 (α β : Type u)
  | mk (p : α × β)

#synth PolyIso (fun X : Type => P2 X Nat) _ _

#synth PolyIso (P2 Nat) _ _

data ThroughP2
  | leaf
  | mk (p : P2 ThroughP2 Nat)

/-! Only the two mentioned parameters are lost: a third one in a field of its own still varies.
And the same data in two fields has no problem at all. -/

data P3 (α β γ : Type u)
  | mk (p : α × β) (c : γ)

data ThroughP3
  | leaf
  | mk (x : P3 Nat Nat ThroughP3)

data Split (α β : Type u)
  | mk (a : α) (b : β)

data ThroughSplit
  | leaf
  | mk (x : Split ThroughSplit Nat)

/-! ### 12. Holes at different indices in several arguments of a leaf

A leaf found by instance search is a functor of one variable, so all its holes must be one type.
`Pair (T i) (T j)` has two. The built-in forms do not have this limit. -/

data Pair (α β : Type u)
  | mk (a : α) (b : β)

data TwoIdx : Nat → Type
  | zero : TwoIdx 0
  | mk {n : Nat} (p : Pair (TwoIdx n) (TwoIdx (n + 1))) : TwoIdx (n + 2)

/-! In a mutual block every type is an index of the block, so two types of a block in one leaf
hit the same error, even though no index is written anywhere. -/

mutual
data PairA
  | nil
  | mk (p : Pair PairA PairB)
data PairB
  | mk (a : PairA)
end

-- With the built-in form the same data passes, for the family and for the block.
data TwoIdxProd : Nat → Type
  | zero : TwoIdxProd 0
  | mk {n : Nat} (p : TwoIdxProd n × TwoIdxProd (n + 1)) : TwoIdxProd (n + 2)

mutual
data ProdA
  | nil
  | mk (p : ProdB × ProdC)
data ProdB
  | mk (a : ProdA)
data ProdC
  | mk (a : ProdA)
end

/-! ### 13. A type of a block with a product in a nested argument

A type of a block gets its instances at its index of the block, presented over the block's index
without the parameters that vary. The index of a position of a nested argument must then be a
type of the block at variables: through a named type constructor at one type, or under binders, it
is (`Even` and `Odd` of section 6 with a parameter would be fine); through a product or a sum it
is only after cases on the position, and the generation fails with a warning. The types
themselves are declared, and a hand-written instance can still be given. -/

mutual
data PA (α : Type u)
  | nil
  | mk (a : α) (p : PA α × Nat)
data PB (α : Type u)
  | mk (a : PA α)
end

#synth PolyIso PA.{0} _ _

data ThroughPA
  | leaf
  | mk (p : PA ThroughPA)

/-! The same with two types of the block in one product: the positions of `p` are at `QA` and at
`QB`, and which one is known only after cases on the position. -/

mutual
data QA (α : Type u)
  | nil
  | mk (a : α) (p : QA α × QB α)
data QB (α : Type u)
  | mk (a : α) (q : QA α)
end

#synth PolyIso QB.{0} _ _

data ThroughQB
  | leaf
  | mk (q : QB ThroughQB)

/-! ### 14. Spellings that mean something else

`×'` is a named constructor, hence a leaf, and it has no instance. -/

data ThroughPProd
  | leaf
  | mk (p : ThroughPProd ×' ThroughPProd)

/-! A dependent pair whose second component does not depend on the first is a product. It is
refused, with a message about function domains that does not fit. -/

data ThroughDepPair
  | mk (f : (x : ThroughDepPair) × Nat)

/-! ## Part III: what looks like a bug

Nothing at the moment. The failures inside the generators that were here work now (sections 6
and 7). A field whose type depends on a recursive field, such as `(l : List T) (h : l ≠ [])`, was
accepted and then failed; it is refused now, with a clear message. -/

end

end NestingTour
