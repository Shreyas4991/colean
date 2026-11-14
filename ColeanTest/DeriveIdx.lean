import Colean.MutualCmd

/-! # Test: `PolyIso` instances of indexed families and of the types of blocks

The instances of a family are at each index, which is an argument of the instance; those of a
type of a block are at its index of the block. No instance is written by hand here. -/

universe u v

namespace DeriveIdxTest

open Codata

/-! ### A family, at a fixed and at a variable index -/

data Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (t : Vec α n) : Vec α (n + 1)

/-- info: Vec.Poly.instPolyIso 3 -/
#guard_msgs in
#synth PolyIso (fun X : Type => Vec X 3) _ _

section
variable (n : Nat)
#synth PolyIso (fun X : Type u => Vec (List X) n) _ _
#synth PolyMap (fun X : Type => Vec X n) (fun X : Type 1 => Vec X n)
end

-- At a fixed index.
data ThroughVec
  | leaf
  | mk (v : Vec ThroughVec 3)

-- A family through a family, at its own index.
data VTree : Nat → Type
  | leaf : VTree 0
  | node {n : Nat} (cs : Vec (VTree n) n) : VTree (n + 1)

/-! ### `codata` families, and a result index that is not a pattern -/

codata CoVec (α : Type u) : Nat → Type u
  | nil : CoVec α 0
  | cons {n : Nat} (a : α) (t : CoVec α n) : CoVec α (n + 1)

#synth PolyIso (fun X : Type => CoVec X 2) _ _

codata CoThrough
  | mk (v : CoVec CoThrough 2)

-- `data` through `codata`.
data FinThrough
  | leaf
  | mk (v : CoVec FinThrough 1)

data Dbl (α : Type u) : Nat → Type u
  | nil : Dbl α 0
  | mk (n : Nat) (a : α) (t : Dbl α n) : Dbl α (n * 2 + 1)

data ThroughDbl
  | leaf
  | mk (v : Dbl ThroughDbl 3)

/-! ### Several indices, and nested arguments inside the family -/

data Grid (α : Type u) : Nat → Nat → Type u
  | nil {m : Nat} : Grid α 0 m
  | cons {n m : Nat} (a : α) (t : Grid α n m) : Grid α (n + 1) m

codata CoGrid (α : Type u) : Nat → Nat → Type u
  | cons {n m : Nat} (a : α) (t : CoGrid α n (m + 1)) : CoGrid α (n + 1) m

#synth PolyIso (fun X : Type => Grid X 2 5) _ _

data ThroughGrid
  | leaf
  | mk (g : Grid ThroughGrid 2 5) (h : CoGrid ThroughGrid 1 0)

data LRose (α : Type u) : Nat → Type u
  | leaf (a : α) : LRose α 0
  | node {n : Nat} (cs : List (LRose α n)) : LRose α (n + 1)

codata ThroughLRose
  | mk (r : LRose ThroughLRose 2)

/-! ### Types of blocks

The presentation is per block (`Ping_Pong.Poly.*`, over the block's index without the
parameters that vary, `Ping_Pong.Poly.Ix`), the instances per type (`Ping.Poly.*`). -/

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
#synth PolyIso (fun X : Type => Pong (Option X)) _ _
#synth PolyMap Pong.{0} Pong.{1}

data ThroughPing
  | leaf
  | mk (p : Ping ThroughPing)

mutual
codata CPing (α : Type u)
  | nil
  | cons (a : α) (b : CPong α)
codata CPong (α : Type u)
  | cons (a : α) (b : CPing α)
end

codata ThroughCPong
  | mk (p : CPong ThroughCPong)

-- A block with indices.
mutual
data Ev (α : Type u) : Nat → Type u
  | zero (a : α) : Ev α 0
  | succ {n : Nat} (o : Od α n) : Ev α (n + 1)
data Od (α : Type u) : Nat → Type u
  | succ {n : Nat} (a : α) (e : Ev α n) : Od α (n + 1)
end

/-- info: Od.Poly.instPolyIso 3 -/
#guard_msgs in
#synth PolyIso (fun X : Type => Od X 3) _ _

data ThroughEv
  | leaf
  | mk (e : Ev ThroughEv 2)

-- A block nesting through a leaf.
mutual
data E1 (α : Type u)
  | nil
  | mk (a : α) (o : List (O1 α))
data O1 (α : Type u)
  | mk (e : E1 α)
end

codata ThroughE1
  | mk (e : E1 ThroughE1)

/-! ### Using the nesting types -/

noncomputable section

/-- The sum of a vector, by its `fold`. -/
def Vec.sum {n : Nat} (v : Vec Nat n) : Nat :=
  Vec.fold (S := fun _ => Nat) (fun _ y => Vec.F.casesOn y 0 fun a s => a + s) v

/-- The number of nodes of a tree, by its `fold`. -/
def ThroughVec.size (t : ThroughVec) : Nat :=
  ThroughVec.fold (fun y => ThroughVec.F.casesOn y 1 fun v => v.sum + 1) t

theorem ThroughVec.size_pos (t : ThroughVec) : 0 < t.size := by
  cases t with
  | leaf => simp [ThroughVec.size]
  | mk v => simp [ThroughVec.size]

/-- Whether a tree is a leaf, by the dependent recursor. -/
def ThroughPing.isLeaf : ThroughPing → Bool :=
  ThroughPing.rec (motive := fun _ => Bool) true fun _ _ => false

theorem ThroughPing.isLeaf_mk (p : Ping ThroughPing) : (ThroughPing.mk p).isLeaf = false := by
  rw [ThroughPing.isLeaf, ThroughPing.rec_mk]

/-- An infinite tree, by `corec`: every node has two children. -/
def CoThrough.full : CoThrough :=
  CoThrough.corec (S := Unit) (fun _ => .mk (.cons () (.cons () .nil))) ()

theorem CoThrough.dtor_full :
    CoThrough.full.dtor = .mk (Occ.map (Occ.ofIso (fun X => CoVec X 2))
      (Occ.ofIso (fun X => CoVec X 2)) (fun _ => CoThrough.full) (.cons () (.cons () .nil))) := by
  rw [CoThrough.full, CoThrough.dtor_corec, CoThrough.F.map_mk]

/-- A tree through a block, by `corec`. -/
def ThroughCPong.spine : ThroughCPong :=
  ThroughCPong.corec (S := Unit) (fun _ => .mk (.cons () .nil)) ()

/-! ### The map is the structural one, at every index -/

abbrev idH : Type → Type := fun X => X

example {X Y : Type} (f : X → Y) {n : Nat} (a : Vec X n) :
    Vec.Poly.toL idH (((Vec.Poly.fix idH X).map (Vec.Poly.fix idH Y) f a).dtor) =
      ⟨(Vec.Poly.toL idH a.dtor).1, fun q => f ((Vec.Poly.toL idH a.dtor).2.1 q),
        fun b => (Vec.Poly.fix idH X).map (Vec.Poly.fix idH Y) f
          ((Vec.Poly.toL idH a.dtor).2.2 b)⟩ :=
  (Vec.Poly.fix idH X).d_map (Vec.Poly.fix idH Y) f a

-- In a block, at the index of a type, with the block's `dtor` (`a.dtor` is `CPong.dtor`, into the
-- layer per type).
example {X Y : Type} (f : X → Y) (a : CPong X) :
    CPing_CPong.Poly.toL idH (i := .CPong) (CPing_CPong.dtor
      ((CPing_CPong.Poly.fix idH X).map (CPing_CPong.Poly.fix idH Y) f (i := .CPong) a)) =
      ⟨(CPing_CPong.Poly.toL idH (i := .CPong) (CPing_CPong.dtor a)).1,
        fun q => f ((CPing_CPong.Poly.toL idH (i := .CPong) (CPing_CPong.dtor a)).2.1 q),
        fun b => (CPing_CPong.Poly.fix idH X).map (CPing_CPong.Poly.fix idH Y) f
          ((CPing_CPong.Poly.toL idH (i := .CPong) (CPing_CPong.dtor a)).2.2 b)⟩ :=
  (CPing_CPong.Poly.fix idH X).d_map (CPing_CPong.Poly.fix idH Y) f (i := .CPong) a

-- The map of the instance is the one of the fixpoint.
example {X Y : Type} (f : X → Y) {n : Nat} (a : Vec X n) :
    (inferInstance : PolyMap (fun X : Type => Vec X n) (fun X : Type => Vec X n)).map f a =
      (Vec.Poly.fix idH X).map (Vec.Poly.fix idH Y) f a :=
  rfl

end

/-! ### Through a product in a block

In a block, the index of a position of a nested argument must be a type of the block at
variables. Through a product or a sum it is one only after cases on the position: the argument is
then split into its components for the presentation (`ColeanTest/NestGaps.lean`). -/

mutual
data QA (α : Type u)
  | nil
  | mk (a : α) (p : QA α × Nat)
data QB (α : Type u)
  | mk (a : QA α)
end

noncomputable example : QB Nat := .mk (.mk 0 (.nil, 1))

/-- info: QB.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso QB.{0} _ _

/-! ### What is not supported: a warning, and the types are untouched

Inside a named type constructor the argument does not split. With its positions at one type of
the block after cases on them (`List (RA α × Nat)`) it has a structure in two variables at that
type (`ColeanTest/NestGaps3.lean`); at several types, the instances are generated, but not the
`simp` lemmas, which state the members by the type of each. -/

/--
warning: no simp lemmas were generated for the instances of `RA`, `RB`; the instances are not affected.
the positions of the nested argument `p` are at several types of the block
-/
#guard_msgs in
mutual
data RA (α : Type u)
  | nil
  | mk (a : α) (p : List (RA α × RB α))
data RB (α : Type u)
  | mk (a : RA α)
end

noncomputable example : RB Nat := .mk (.mk 0 [])

/-- info: RA.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso RA.{0} _ _

end DeriveIdxTest
