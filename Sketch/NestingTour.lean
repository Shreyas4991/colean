import Colean.MutualCmd

/-!
# A tour of nested types

What the `datatype` and `codatatype` commands accept as a nested argument today, and what they do
not. Read it top to bottom. Part I (sections 1 to 9) is what works, Part II (sections 10 to 13) what
does not work yet but could, and Part III failures that look like bugs of the commands rather than
limits; there are none at the moment.

How the file is checked:

* an example without an error on it works;
* the failures of Parts II and III are left as they are, so they show as errors in the infoview;
* in Part II a failed `datatype`/`codatatype` declares nothing, so the names of failed types do not
  exist; a failed instance generation is silent (a warning under
  `set_option codata.deriveDetails true`), and the type itself is declared;
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
datatype BinT
  | leaf
  | node (c : BinT × BinT)

-- `T ⊕ A`: an occurrence on one side of a sum.
datatype Tm (α : Type u)
  | var (a : α)
  | app (f : Tm α ⊕ α) (arg : Tm α)

-- `A → T`: infinitely branching, a recursive argument under an arrow.
datatype Omega
  | leaf
  | node (k : Nat → Omega)

-- `A → List T`: a function into a leaf.
codatatype Proc (α : Type u)
  | act (k : α → List (Proc α))
  | stop

-- `(n : Nat) × (Fin n → T)`: the second component depends on the first.
datatype SizedRose
  | node (c : (n : Nat) × (Fin n → SizedRose))

-- A function from a proposition: `k` gives children only when `0 < n`, and `n` is an earlier field.
datatype Guarded
  | mk (n : Nat) (k : 0 < n → List Guarded)

-- All of them at once: the depth does not matter.
codatatype Deep (α : Type u)
  | mk (a : α) (c : (n : Nat) × (Fin n → List (Deep α × (Nat ⊕ Deep α))))

-- The same in a `datatype`, with a proposition and a dependent function on the way.
datatype DeepFin
  | leaf
  | mk (c : (n : Nat) → n = 0 → (Fin n → DeepFin) × Option (DeepFin ⊕ Nat))

/-! ### 2. Library leaves

`List`, `Option` and `Array` have instances in `Colean/PolyIso.lean`. Leaves compose with each
other and with the forms of section 1. -/

-- The rose tree, with `List`.
codatatype ListRose (α : Type u)
  | node (a : α) (cs : List (ListRose α))

-- A possibly ending stream, with `Option`.
codatatype OptStream (α : Type u)
  | cons (a : α) (tail : Option (OptStream α))

-- With `Array`.
datatype ArrRose
  | node (cs : Array ArrRose)

-- `List (Option T)`, a composite of two leaves.
datatype OptRose (α : Type u)
  | node (a : α) (cs : List (Option (OptRose α)))

-- A leaf outside a built-in form, and a built-in form outside a leaf.
datatype Mixed
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
codatatype BoxStream (α : Type u)
  | cons (a : α) (tail : Box (BoxStream α))

datatype BoxList (α : Type u)
  | nil
  | cons (a : α) (tail : Box (BoxList α))

-- The instances compose with everything above.
codatatype BoxTree
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

datatype LabelledList
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

codatatype MonoStream
  | cons (t : MonoBox MonoStream)

/-- info: @MonoStream.corec : {S : Type} → (S → MonoStream.F S) → S → MonoStream -/
#guard_msgs in
#check @MonoStream.corec

/-! A generic fixpoint of a functor with instances: the instances are parameters of the type. -/

datatype FixInst (G : Type → Type) (Sh : Type) (Pos : Sh → Type) [PolyIso G Sh Pos] [PolyMap G G]
  | mk (x : G (FixInst G Sh Pos))

/-! ### 4. Declared types, with generated instances

A `datatype` or `codatatype` gets `PolyIso` and `PolyMap` by itself, in a separate step after the
declaration (`Colean/Gen/Derive.lean`); families and the types of blocks too, at every index (the
end of section 6). Nothing is written by hand from here to the end of section 5. -/

datatype L (α : Type u)
  | nil
  | cons (a : α) (t : L α)

codatatype Str (α : Type u)
  | cons (a : α) (t : Str α)

/-- info: L.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso L.{0} _ _

/-- info: Str.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso Str.{0} _ _

/-- info: L.Colean.Poly.instPolyMapEta -/
#guard_msgs in
#synth PolyMap L.{0} L.{1}

-- `datatype` through `datatype`: finite trees with finitely many children.
datatype LRose
  | node (cs : L LRose)

-- `codatatype` through `datatype`: trees of any depth, each node with finitely many children.
codatatype LInf
  | node (cs : L LInf)

-- `datatype` through `codatatype`: a well-founded tree with a stream of children at each node.
-- Lean's `inductive` has no counterpart for this: it nests through inductive types only.
datatype Bush
  | leaf
  | node (c : Str Bush)

-- `codatatype` through `codatatype`.
codatatype CoBush
  | node (c : Str CoBush)

-- A composite: the generated instance takes an instance as a premise.
codatatype LList
  | node (c : L (List LList))

-- Three declared and library leaves in one argument, across kinds.
datatype Tower
  | leaf
  | node (c : L (Str (Option Tower)))

-- A declared type with a nested field is itself nested through: the instances chain.
datatype Rose₁ (α : Type u)
  | node (a : α) (cs : L (Rose₁ α))

datatype Rose₂
  | mk (r : Rose₁ Rose₂)

/-! ### 5. Several parameters

One generated instance covers `fun X => E (H₁ X) (H₂ X)` for `H₁`, `H₂` themselves instances,
constants and the identity among them. So every line below is the same instance. -/

datatype E (α β : Type u)
  | l (a : α)
  | r (b : β)

/-- info: E.Colean.Poly.instPolyIso -/
#guard_msgs in
#synth PolyIso (fun X : Type u => E X X) _ _

/-- info: E.Colean.Poly.instPolyIso -/
#guard_msgs in
#synth PolyIso (fun X : Type => E X Nat) _ _

/-- info: E.Colean.Poly.instPolyIsoEta ℕ -/
#guard_msgs in
#synth PolyIso (E Nat) _ _

/-- info: E.Colean.Poly.instPolyIso -/
#guard_msgs in
#synth PolyIso (fun X : Type u => E (List X) (Option X)) _ _

/-! The `PolyMap` instance takes those of the premises, as the instances of the built-in forms
do: it maps between two instantiations of one functor, not between `E (List X) Nat` and
`E (Array X) Nat`, whose presentations are the same. -/

/--
error: failed to synthesize
  PolyMap (fun X => E (List X) ℕ) fun X => E (Array X) ℕ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth PolyMap (fun X : Type => E (List X) Nat) (fun X : Type => E (Array X) Nat)

-- `E T T`.
datatype ETT
  | leaf
  | mk (p : E ETT ETT)

-- `E Nat T`.
codatatype ENT
  | mk (p : List (E Nat ENT))

-- `E T Nat`.
datatype ETN
  | leaf
  | mk (p : E ETN Nat)

-- `E (List T) (Option T)`.
datatype EComp
  | leaf
  | mk (p : E (List EComp) (Option EComp))

-- Declared leaves in both arguments, one inductive and one coinductive.
datatype EDecl
  | leaf
  | mk (p : E (L EDecl) (Str EDecl))

-- With one argument mentioning `T`, other than the last, the leaf is the whole
-- `fun X => E (X × Nat) Nat`, found by instance search: `E`'s instance at the premise
-- `fun X => X × Nat` (section 8).
datatype EProd
  | leaf
  | mk (p : E (EProd × Nat) Nat)

-- With `T` in both arguments, the leaf is the whole `fun X => E (X × Nat) X`, found by instance
-- search, which needs an instance at `fun X => X × Nat`: products, sums, functions and dependent
-- pairs of functors with instances have instances (`PolyIso.lean`).
datatype EProdBoth
  | leaf
  | mk (p : E (EProdBoth × Nat) EProdBoth)

/-- info: PolyIso.instProd -/
#guard_msgs in
#synth PolyIso (fun X : Type => X × Nat) _ _

/-! A parameter may vary when it sits in fields with an occurrence structure in it. All these
kinds of field count, and the parameters may live in different universes. -/

datatype Fields (α : Type u)
  | mk (x : Option (List α)) (y : Nat → α) (z : (n : Nat) × (Fin n → α)) (w : α ⊕ Nat)
       (s : L α) (e : E α (List α)) (t : Fields α)

/-- info: Fields.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso Fields.{0} _ _

datatype TwoUniv (α : Type u) (β : Type v)
  | l (a : α)
  | r (b : β)

datatype UseTwoUniv
  | leaf
  | mk (x : TwoUniv UseTwoUniv UseTwoUniv)

/-! A parameter that may not vary is constant, and the rest still works: `A` in `Fn` is a domain,
and `n` in `FinFn` is not a type. -/

datatype Fn (A : Type) (α : Type u)
  | leaf (a : α)
  | node (k : A → Fn A α)

datatype UseFn
  | mk (f : Fn Nat UseFn)

datatype FinFn (n : Nat) (α : Type u)
  | mk (v : Fin n → α)

datatype UseFinFn
  | leaf
  | mk (x : FinFn 3 UseFinFn)

/-! A field may mention several parameters that vary: its structure is then in all of them, each
at its premise, `fun X => H₁ X × H₂ X` for `p : α × β`. A third parameter in a field of its own
varies as well. -/

datatype P2 (α β : Type u)
  | mk (p : α × β)

/-- info: P2.Colean.Poly.instPolyIso -/
#guard_msgs in
#synth PolyIso (fun X : Type => P2 X Nat) _ _

/-- info: P2.Colean.Poly.instPolyIsoEta ℕ -/
#guard_msgs in
#synth PolyIso (P2 Nat) _ _

datatype ThroughP2
  | leaf
  | mk (p : P2 ThroughP2 Nat)

datatype P3 (α β γ : Type u)
  | mk (p : α × β) (c : γ)

datatype ThroughP3
  | leaf
  | mk (x : P3 Nat Nat ThroughP3)

/-! When the parameters of a field cannot vary together, the first ones are kept constant until the
others can: `A` is a domain in `Fn`, so `FnBoth` varies in `β` only. -/

datatype FnBoth (α β : Type)
  | mk (x : Fn α β)

/-- info: FnBoth.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso (FnBoth Nat) _ _

/-! The fewest are kept constant, the first ones first: in `α → β → γ` the domains `α` and `β`
are, and `FnFn` varies in `γ`. -/

datatype FnFn (α β γ : Type)
  | mk (x : α → β → γ)

/-- info: FnFn.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso (FnFn Nat Nat) _ _

/-! Degenerate cases are fine too: a parameter that is never used, and no constructors at all. -/

datatype Phantom (α : Type u)
  | mk (n : Nat)

datatype UsePhantom
  | mk (x : Phantom UsePhantom)

codatatype Void (α : Type u)

/-- info: Void.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso Void.{0} _ _

/-! ### 6. Indexed families and mutual blocks

Here leaves come from sections 2 and 3, or from section 4: the enclosing type may be a family or
a block. A family may have several indices, and so may the types of a block. At the end of the
section the leaf is itself a family or a type of a block, with generated instances. -/

-- A family through a plain leaf.
codatatype BoxVec (α : Type u) : Nat → Type u
  | nil : BoxVec α 0
  | cons {n : Nat} (a : α) (tail : Box (BoxVec α n)) : BoxVec α (n + 1)

-- The same with `List`, and with a generated leaf.
datatype LevelRose : Nat → Type
  | leaf : LevelRose 0
  | node {n : Nat} (cs : List (LevelRose n)) : LevelRose (n + 1)

datatype LevelL : Nat → Type
  | leaf : LevelL 0
  | node {n : Nat} (cs : L (LevelL n)) : LevelL (n + 1)

-- A mutual block, through a plain leaf and a generated one.
mutual
datatype Even
  | zero
  | succ (o : L Odd)
datatype Odd
  | succ (e : Box Even)
end

-- Occurrences at several indices, through built-in forms.
datatype Chain : Nat → Type
  | zero : Chain 0
  | link {n : Nat} (p : Chain n × Chain (n + 1)) : Chain (n + 2)

-- The index may depend on a variable bound on the way.
datatype ByIndex : Nat → Type
  | zero : ByIndex 0
  | mk {m : Nat} (c : (n : Nat) × (Fin n → ByIndex n)) : ByIndex (m + 1)

codatatype ByArg : Nat → Type
  | mk {m : Nat} (c : (k : Nat) → List (ByArg k)) : ByArg m

-- Several arguments of a leaf are fine at one index: `E` at `n` in both.
datatype OneIndex : Nat → Type
  | zero : OneIndex 0
  | mk {n : Nat} (p : E (List (OneIndex n)) (Option (OneIndex n))) : OneIndex (n + 2)

-- At one index after cases through a sum, as through a product: the recursor's hypothesis is by
-- membership at that index (section 8).
datatype SumIndex : Nat → Type
  | zero : SumIndex 0
  | mk {n : Nat} (p : SumIndex n ⊕ SumIndex n) : SumIndex (n + 1)

example (P : ∀ n, SumIndex n → Prop) (h0 : P 0 .zero)
    (hm : ∀ n (p : SumIndex n ⊕ SumIndex n), (∀ t, PolyIso.Mem (fun X => X ⊕ X) t p → P n t) →
      P (n + 1) (.mk p))
    {n : Nat} (t : SumIndex n) : P n t := by
  induction t with
  | zero => exact h0
  | mk p ih => exact hm _ p ih

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
codatatype Alt : Bool → Type
  | mk {b : Bool} (children : Both (fun c => Alt c)) : Alt b

-- Reindexed.
codatatype Flip : Bool → Type
  | mk {b : Bool} (children : Both (fun c => Flip (!c))) : Flip b

-- A plain leaf inside, and outside.
codatatype AltIn : Bool → Type
  | mk {b : Bool} (children : Both (fun c => List (AltIn c))) : AltIn b

codatatype AltOut : Bool → Type
  | mk {b : Bool} (children : List (Both (fun c => AltOut c))) : AltOut b

-- In a `datatype`, with a built-in form inside.
datatype AltFin : Bool → Type
  | leaf {b : Bool} : AltFin b
  | mk {b : Bool} (children : Option (Both (fun c => AltFin c × Nat))) : AltFin b

-- On a plain type too, the family ignoring its index, with a named binder or not.
codatatype AltPlain
  | mk (children : Both (fun _b => AltPlain))

codatatype AnonFamily
  | mk (children : Both (fun _ => AnonFamily))

/-! With a `simp` lemma for the members of `Both`, `simp` computes the hypotheses of the recursors
through it, reindexed or at a constant family (`IPolyIso.mem_reidx`, `PolyIso.mem_ofI`,
`mem_compI`). -/

@[simp] theorem Both.mem {X : Bool → Type u} (j : Bool) (x : X j) (c : Both X) :
    IPolyIso.Mem Both j x c ↔
      (⟨true, c.yes⟩ : Σ b, X b) = ⟨j, x⟩ ∨ (⟨false, c.no⟩ : Σ b, X b) = ⟨j, x⟩ := by
  constructor
  · rintro ⟨b, e⟩
    cases b
    · exact .inr e
    · exact .inl e
  · rintro (e | e)
    · exact ⟨true, e⟩
    · exact ⟨false, e⟩

datatype FlipD : Bool → Type
  | leaf {b : Bool} : FlipD b
  | mk {b : Bool} (children : Both (fun c => FlipD (!c))) : FlipD b

theorem FlipD.ind (P : ∀ b, FlipD b → Prop) (h0 : ∀ b, P b .leaf)
    (hm : ∀ b (c : Both fun c => FlipD (!c)), P false c.yes → P true c.no → P b (.mk c))
    {b : Bool} (t : FlipD b) : P b t := by
  induction t with
  | leaf => exact h0 _
  | mk c ih =>
    simp at ih
    exact hm _ c ih.1 ih.2

/-! Several indices, through a plain leaf and through built-in forms, in both kinds. These failed
in the generated proofs until the commands moved to `Expr`. -/

codatatype TwoListCo : Nat → Nat → Type
  | mk {n m : Nat} (c : List (TwoListCo n m)) : TwoListCo (n + 1) m

codatatype TwoProdCo : Nat → Nat → Type
  | mk {n m : Nat} (c : Nat × TwoProdCo n m) : TwoProdCo (n + 1) m

datatype TwoFn : Nat → Nat → Type
  | nil : TwoFn 0 0
  | mk {n m : Nat} (c : Nat → TwoFn n m) : TwoFn (n + 1) m

datatype TwoProd : Nat → Nat → Type
  | nil : TwoProd 0 0
  | mk {n m : Nat} (c : Nat × TwoProd n m) : TwoProd (n + 1) m

/-! Families and the types of blocks are leaves too, with generated instances at every index:
`PolyIso (fun X => Vec (H X) n)` for each `n`, an argument of the instance, and for a type of a
block at its index of the block. -/

datatype Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (t : Vec α n) : Vec α (n + 1)

/-- info: Vec.Colean.Poly.instPolyIso 3 -/
#guard_msgs in
#synth PolyIso (fun X : Type => Vec X 3) _ _

-- At a fixed index.
datatype ThroughVec
  | leaf
  | mk (v : Vec ThroughVec 3)

-- A family through a family, at its own index.
datatype VTree : Nat → Type
  | leaf : VTree 0
  | node {n : Nat} (cs : Vec (VTree n) n) : VTree (n + 1)

-- The types of a block.
mutual
datatype Ping (α : Type u)
  | nil
  | cons (a : α) (b : Pong α)
datatype Pong (α : Type u)
  | cons (a : α) (b : Ping α)
end

/-- info: Ping.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso Ping.{0} _ _

datatype ThroughPing
  | leaf
  | mk (v : Ping ThroughPing)

-- The types of a block with indices, in `codatatype`.
mutual
codatatype Ev (α : Type u) : Nat → Type u
  | zero (a : α) : Ev α 0
  | succ {n : Nat} (o : Od α n) : Ev α (n + 1)
codatatype Od (α : Type u) : Nat → Type u
  | succ {n : Nat} (a : α) (e : Ev α n) : Od α (n + 1)
end

datatype ThroughOd
  | leaf
  | mk (o : Od ThroughOd 3)

/-! A hand-written instance still works, and is the one found, being declared after the generated
one: here a presentation simpler than the trees of shapes. First for a family at a fixed index,
whichever it is. -/

datatype Tagged (α : Type u) : Bool → Type u
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

datatype ThroughTagged
  | leaf
  | mk (v : Tagged ThroughTagged true)

/-! Then for a type of a block. -/

mutual
datatype Hand (α : Type u)
  | mk (a : α) (b : Stop α)
datatype Stop (α : Type u)
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

datatype ThroughHand
  | leaf
  | mk (v : Hand ThroughHand)

/-! In a block, a nested argument through a product or a sum has its positions at a type of the
block only after cases on them. For the presentation it is split into its components, so these
types are leaves too. -/

mutual
datatype PA (α : Type u)
  | nil
  | mk (a : α) (p : PA α × Nat)
datatype PB (α : Type u)
  | mk (a : PA α)
end

/-- info: PA.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso PA.{0} _ _

datatype ThroughPA
  | leaf
  | mk (p : PA ThroughPA)

-- Two types of the block in one product.
mutual
datatype QA (α : Type u)
  | nil
  | mk (a : α) (p : QA α × QB α)
datatype QB (α : Type u)
  | mk (a : α) (q : QA α)
end

/-- info: QB.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso QB.{0} _ _

datatype ThroughQB
  | leaf
  | mk (q : QB ThroughQB)

/-! Inside a named type constructor the split stops, and the positions of `p : List (RA α × Nat)`
are at `RA` only after cases on them. Such an argument has a structure in two variables over the
block's index (`IOcc₂`, `Colean/Model/IOcc2.lean`), here the plain one at the index of `RA`, so
`RA` is a leaf too, and its `simp` rules are those of a single type. -/

mutual
datatype RA (α : Type u)
  | nil
  | mk (a : α) (p : List (RA α × Nat))
datatype RB (α : Type u)
  | mk (a : RA α)
end

/-- info: RA.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso RA.{0} _ _

example (x a : Nat) (p : List (RA Nat × Nat)) :
    PolyIso.Mem RA x (RA.mk a p) ↔ x = a ∨ ∃ t, (∃ n, (t, n) ∈ p) ∧ PolyIso.Mem RA x t := by
  simp

datatype ThroughRA
  | leaf
  | mk (r : RA ThroughRA)

/-! ### 7. Spellings

The analysis works on the elaborated type of an argument, so a type spelled differently is the
same type: prefix `Prod` and `Sum`, an abbreviation, `id`, `<|`, `Σ`, `∀`, an implicit binder.
These were refused while the analysis read the syntax. -/

datatype PrefixProd
  | leaf
  | mk (p : Prod PrefixProd PrefixProd)

datatype PrefixProd₂
  | leaf
  | mk (p : Prod Nat PrefixProd₂)

datatype PrefixSum
  | leaf
  | mk (p : Sum PrefixSum Nat)

abbrev Twice (X : Type u) := X × X

datatype ThroughAbbrev
  | leaf
  | mk (p : Twice ThroughAbbrev)

datatype ThroughId
  | leaf
  | mk (p : id ThroughId)

datatype ThroughPipe
  | leaf
  | mk (p : Option <| List ThroughPipe)

datatype ThroughSigma
  | leaf
  | mk (p : Σ n : Nat, Fin n → ThroughSigma)

datatype ThroughForall
  | leaf
  | mk (p : ∀ n : Nat, Fin n → ThroughForall)

-- An implicit binder in a nested argument stays implicit in `T.F` and in the constructor.
datatype ImplicitPi
  | leaf
  | mk (k : {n : Nat} → List ImplicitPi)

/-! ### 8. Using a nested type

`fold`, `corec` and the lemmas about them see the leaf: the argument of a nested constructor of
`T.F` has the leaf applied to the state. To compute through it, `Occ.map_list`, `Occ.map_prod`,
`Occ.map_ofIso` and friends turn the generated map into the map of the leaf. -/

datatype URose (α : Type u)
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

/-! The recursor states the induction hypothesis of a nested argument by membership: through
`List`, `Option` and `Array` by their own, `∀ t, t ∈ cs → motive t` here, and otherwise for the
functor of the argument's type, `PolyIso.Mem (fun X => X × Option X) t children` for `UTree`
below, and by `IPolyIso.Mem` at an index when the positions of a family's argument are at
several indices (at one index, also through a product or a sum, `T n × T n`, `T n ⊕ T n`, it is
by `PolyIso.Mem` at that index). The `simp` lemmas of `PolyIso.lean` turn membership into the
container's own (`mem_list`, `mem_option`) or into components (`mem_prod`, `mem_sum`,
`mem_comp`, …), so a function by the recursor can use `List.attach`. -/

/--
info: @URose.rec : {α : Type u_2} →
  {motive : URose α → Sort u_1} →
    ((a : α) → (cs : List (URose α)) → ((t : URose α) → t ∈ cs → motive t) → motive (URose.node a cs)) →
      (t : URose α) → motive t
-/
#guard_msgs in
#check @URose.rec

/-- The number of nodes again, by the recursor. -/
def URose.size' {α : Type u} : URose α → Nat :=
  URose.rec (motive := fun _ => Nat) fun _ cs ih =>
    (cs.attach.map fun x => ih x.1 x.2).sum + 1

/-- The rule `URose.rec_node` gives the hypothesis as `fun t _ => URose.rec … t`. -/
@[simp] theorem URose.size'_node {α : Type u} (a : α) (cs : List (URose α)) :
    (URose.node a cs).size' = (cs.map URose.size').sum + 1 := by
  simp [URose.size', List.map_attach_eq_pmap]

/-- Induction: the hypothesis at the members of the list. -/
theorem URose.size'_eq {α : Type u} (t : URose α) : t.size' = t.size := by
  induction t with
  | node a cs ih =>
    rw [URose.size'_node, URose.size_node, List.map_congr_left ih]

codatatype UTree (α : Type u)
  | node (a : α) (children : UTree α × Option (UTree α))

/-- The tree with `a` everywhere, as a `corec` with one state. -/
def UTree.const {α : Type u} (a : α) : UTree α :=
  UTree.corec (S := Unit) (fun _ => .node a ((), some ())) ()

@[simp] theorem UTree.dtor_const {α : Type u} (a : α) :
    (UTree.const a).dtor = .node a (UTree.const a, some (UTree.const a)) := by
  rw [UTree.const, UTree.dtor_corec]
  simp [UTree.F.fmap_node, Occ.map_prod, Occ.map_hole, Occ.map_option]

/-! Through a generated leaf the definitions are as easy, with the leaf's own `fold`, or its
constructors in a `corec`, and so are the lemmas: the rules of the leaf's instances compute the
generated map on its constructors (`L.Colean.Poly.map_cons`), as `Occ.map_list` does for a list. -/

/-- The number of nodes of an `LRose`: `L.fold` sums the folded children. -/
def LRose.size (t : LRose) : Nat :=
  LRose.fold (S := Nat)
    (fun | .node cs => L.fold (S := Nat) (fun | .nil => 0 | .cons a n => a + n) cs + 1) t

/-- A tree with one child at every node. -/
def LInf.spine : LInf :=
  LInf.corec (S := Unit) (fun _ => .node (L.cons () .nil)) ()

theorem LInf.dtor_spine : LInf.spine.dtor = .node (L.cons LInf.spine .nil) := by
  rw [LInf.spine, LInf.dtor_corec, LInf.F.fmap_node]
  simp

/-! The hypothesis of a nested argument is stated with the instance that instance search finds
for its functor, so a hypothesis written by hand is the recursor's: through `Vec (List T) 2` it is
`Vec`'s instance at the premise `List`, not the composite of `Vec` and `List`, and through
`E (T × Nat) Nat` (section 5) `E`'s at the premise `fun X => X × Nat`. `simp` computes the map at
either premise, a leaf (`Occ.map_list`) or a built-in form (`Occ.ofIso_prod`). -/

datatype VRose
  | leaf
  | node (cs : Vec (List VRose) 2)

example (P : VRose → Prop) (hl : P .leaf)
    (hn : ∀ cs, (∀ t, PolyIso.Mem (fun X => Vec (List X) 2) t cs → P t) → P (.node cs))
    (t : VRose) : P t := by
  induction t with
  | leaf => exact hl
  | node cs ih => exact hn cs ih

example (P : EProd → Prop) (hl : P .leaf)
    (hn : ∀ p, (∀ t, PolyIso.Mem (fun X => E (X × Nat) Nat) t p → P t) → P (.mk p))
    (t : EProd) : P t := by
  induction t with
  | leaf => exact hl
  | mk p ih => exact hn p ih

/-- The number of nodes, by the folds of the two types. -/
def EProd.size : EProd → Nat :=
  EProd.fold (S := Nat) fun
    | .leaf => 1
    | .mk p => E.fold (S := Nat) (fun | .l q => q.1 + q.2 | .r n => n) p + 1

example : (EProd.mk (.l (.mk (.r 3), 2))).size = 7 := by
  simp [EProd.size]

/-! ### 9. A parameter in the same field as the type

A field with both a parameter and the type is split through its products and sums for the
presentation, into parts with positions of one kind each: `p : α × PairStr α` gives a parameter
position and a recursive one, `f : Tm α ⊕ α` one of them on each side. The `simp` rules are then
stated with the components (`PairStr.Colean.Poly.mem_mk` with `p.1` and `p.2`), and once for each
side of a sum (`Tm.Colean.Poly.map_app_inl`, `Tm.Colean.Poly.map_app_inr`). So the stream of
section 4 can be written with a pair, and `Tm` of section 1 is a leaf too. -/

codatatype PairStr (α : Type u)
  | mk (p : α × PairStr α)

/-- info: PairStr.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso PairStr.{0} _ _

/-- info: Tm.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso Tm.{0} _ _

datatype ThroughPairStr
  | leaf
  | mk (x : PairStr ThroughPairStr)

datatype ThroughTm
  | leaf
  | mk (t : Tm ThroughTm)

example (t a b : ThroughTm) : PolyIso.Mem Tm t (.app (.inl (.var a)) (.var b)) ↔ t = a ∨ t = b := by
  simp

/-! Under a named type constructor or a function the split stops: `p : List (α × LPair α)` and
`k : Nat → α × FPair α` have positions of both kinds in one argument. Such a field has an occurrence
structure in two variables (`Occ₂`, `Colean/Model/Occ2.lean`), the parameter at the premise of the
instance and the recursion, and the `simp` rules map it by `Occ₂.map` (`LPair.Colean.Poly.map_mk`),
which `simp` computes through its combinators, and state its members by the structures in each
variable alone (`LPair.Colean.Poly.mem_mk`). -/

datatype LPair (α : Type u)
  | nil
  | mk (p : List (α × LPair α))

/-- info: LPair.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso LPair.{0} _ _

datatype FPair (α : Type u)
  | leaf
  | mk (k : Nat → α × FPair α)

/-- info: FPair.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso FPair.{0} _ _

example (f : Nat → Nat) (a b : Nat) :
    (Occ.ofIso LPair).map (Occ.ofIso LPair) f (.mk [(a, .nil), (b, .mk [])]) =
      .mk [(f a, .nil), (f b, .mk [])] := by
  simp

example (x a b : Nat) (l : LPair Nat) :
    PolyIso.Mem LPair x (.mk [(a, l), (b, .nil)]) ↔ (x = a ∨ x = b) ∨ PolyIso.Mem LPair x l := by
  simp

datatype ThroughFPair
  | leaf
  | mk (x : FPair ThroughFPair)

example (t : ThroughFPair) : PolyIso.Mem FPair t (FPair.mk fun _ => (t, .leaf)) := by
  simp

/-! Across a sum inside the named type constructor, `p : List (α ⊕ LSum α)`, the structures in each
variable alone do not agree with the one in two variables (a shape of the sum is on one side), so
the rule of membership states the field by the members in each variable of that structure
(`Occ₂.MemX`, `Occ₂.MemY`), which `simp` computes through its combinators. -/

datatype LSum (α : Type u)
  | nil
  | mk (p : List (α ⊕ LSum α))

example (x : Nat) (p : List (Nat ⊕ LSum Nat)) :
    PolyIso.Mem LSum x (.mk p) ↔ Sum.inl x ∈ p ∨ ∃ t, Sum.inr t ∈ p ∧ PolyIso.Mem LSum x t := by
  simp

/-! In a family, the recursion's positions carry an index, and the field has a structure in two
variables over the family's index (`IOcc₂`): `p : List (α × LFam α n)` has its positions at `n`,
so its rules are those of a single type, at `LFam α n`. -/

datatype LFam (α : Type u) : Nat → Type u
  | nil {n : Nat} : LFam α n
  | mk {n : Nat} (p : List (α × LFam α n)) : LFam α (n + 1)

/-- info: LFam.Colean.Poly.instPolyIso 3 -/
#guard_msgs in
#synth PolyIso (fun X : Type => LFam X 3) _ _

example (f : Nat → Nat) (a : Nat) :
    (Occ.ofIso fun X => LFam X 1).map (Occ.ofIso fun X => LFam X 1) f (.mk [(a, .nil)]) =
      .mk [(f a, .nil)] := by
  simp

-- Across a sum too: the map of the family's structure is the plain one at that index through the
-- sum (`IOcc.map_flat_sum`).
datatype LFamSum (α : Type u) : Nat → Type u
  | nil {n : Nat} : LFamSum α n
  | mk {n : Nat} (p : List (α ⊕ LFamSum α n)) : LFamSum α (n + 1)

example (x a : Nat) (t : LFamSum Nat 0) :
    PolyIso.Mem (fun X => LFamSum X 1) x (.mk [.inl a, .inr t]) ↔
      x = a ∨ PolyIso.Mem (fun X => LFamSum X 0) x t := by
  simp

/-! ## Part II: what does not work yet

Everything here could be supported. What should stay rejected is not listed: negative
occurrences, functors that are not polynomial such as `Finset`, parameters that later types depend
on, fields whose type depends on a recursive field, non-uniform parameters, and a `PolyIso` without
its `PolyMap`. Blocks that mix `datatype` and `codatatype` (`mixed_mutual`) are in
`Sketch/MixedTour.lean`: their runs inside are declared open in the outer types and nested
through by the instances generated here, so the limits of sections 11 and 12 are theirs too
(Part II there). -/

/-! ### 10. Missing instances

A plain `structure` gets no instance: only `datatype` and `codatatype` generate them. Nothing in it
stops one from being generated when a declaration nests through it (`todo.md`). -/

structure NoIso (X : Type u) where
  val : X

codatatype NeedsIso
  | mk (x : NoIso NeedsIso)

/-! The same for functors on families. -/

structure NoFamIso (X : Bool → Type u) where
  yes : X true

codatatype NeedsFamIso : Bool → Type
  | mk {b : Bool} (children : NoFamIso (fun c => NeedsFamIso c)) : NeedsFamIso b

/-! ### 11. Holes at different indices in several arguments of a leaf

A leaf found by instance search is a functor of one variable, so all its holes must be one type.
`Pair (T i) (T j)` has two. It would need `Pair` as a functor on families,
`IPolyIso (fun X => Pair (X i) (X j))`, and step 5 generates no `IPolyIso` instances: their
varying parameter is a family, and `Model/Poly.lean` has the fixpoint for a parameter that is a
type only. The built-in forms do not have this limit. -/

datatype Pair (α β : Type u)
  | mk (a : α) (b : β)

datatype TwoIdx : Nat → Type
  | zero : TwoIdx 0
  | mk {n : Nat} (p : Pair (TwoIdx n) (TwoIdx (n + 1))) : TwoIdx (n + 2)

/-! In a mutual block every type is an index of the block, so two types of a block in one leaf
hit the same error, even though no index is written anywhere. -/

mutual
datatype PairA
  | nil
  | mk (p : Pair PairA PairB)
datatype PairB
  | mk (a : PairA)
end

-- With the built-in form the same data passes, for the family and for the block.
datatype TwoIdxProd : Nat → Type
  | zero : TwoIdxProd 0
  | mk {n : Nat} (p : TwoIdxProd n × TwoIdxProd (n + 1)) : TwoIdxProd (n + 2)

mutual
datatype ProdA
  | nil
  | mk (p : ProdB × ProdC)
datatype ProdB
  | mk (a : ProdA)
datatype ProdC
  | mk (a : ProdA)
end

/-! ### 12. Several types of a block inside a named type constructor

In a block, a nested argument with positions at several types of the block inside a named type
constructor, `p : List (SA α × SB α)`, has a structure in two variables over the block's index,
so the types get their instances. Its `simp` rules are not generated (silently, a warning under
`codata.deriveDetails`): they would
state the members by the type of each, at an index that is a variable, which the rules cannot
write in a form `simp` can use (the family of the block's types there is not reducible to them).
-/

mutual
datatype SA (α : Type u)
  | nil
  | mk (a : α) (p : List (SA α × SB α))
datatype SB (α : Type u)
  | mk (a : SA α)
end

#check @SA.Colean.Poly.mem_mk

/-! ### 13. Spellings that mean something else

`×'` is a named constructor, hence a leaf, and it has no instance. -/

datatype ThroughPProd
  | leaf
  | mk (p : ThroughPProd ×' ThroughPProd)

/-! A dependent pair whose second component does not depend on the first is a product. It is
refused, with a message about function domains that does not fit. -/

datatype ThroughDepPair
  | mk (f : (x : ThroughDepPair) × Nat)

/-! ## Part III: what looks like a bug

Nothing at the moment. The failures inside the generators that were here work now (sections 6
and 7). A field whose type depends on a recursive field, such as `(l : List T) (h : l ≠ [])`, was
accepted and then failed; it is refused now, with a clear message. -/

end

end NestingTour
