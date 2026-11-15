import Colean.MutualCmd

/-! # Test: folding per type in a `datatype` block

Each type of a `mutual` block of `datatype` gets the interface of a single type, with the shape of
Lean's mutual recursors: a family, an algebra and a morphism per type, and nothing about the block's
index `Blk.Ix` (`dtor`, `ctor`, Lambek's lemma, `fold`, `fold_ctor`, `fold_eq`, `fold_unique`, the
rules `fold_cᵢ`, the laws of the layer). The layer of a type at a family per type is
`Tₘ.F params S₁ … Sₖ idx`, the block's functor at the families packed by cases on `Blk.Ix`
(`Blk.Colean.St`), with a constructor `Tₘ.F.c` per constructor of the type, the block functor's
under the type's own name (`Even.F.succ` for `Even_Odd.F.Even_succ`), for patterns and dot notation,
and shown so. The block-level `Blk.fold` takes one family and one algebra over `Blk.Ix`; its rules
are `Blk.fold_cᵢ`.
-/

universe u

open Codata

namespace MutualFoldTest

noncomputable section

/-! ### Trees and forests -/

mutual
datatype Tree (α : Type)
  | node (a : α) (children : Forest α)
datatype Forest (α : Type)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

/-- info: @Tree.fold : {α : Type} → {S₁ S₂ : Type u_1} → (Tree.F α S₁ S₂ → S₁) → (Forest.F α S₁ S₂ → S₂) → Tree α → S₁ -/
#guard_msgs in #check @Tree.fold

/--
info: @Tree.fold_node : ∀ {α : Type} {S₁ S₂ : Type u_1} (a₁ : Tree.F α S₁ S₂ → S₁) (a₂ : Forest.F α S₁ S₂ → S₂) (a : α)
  (children : Forest α), Tree.fold a₁ a₂ (Tree.node a children) = a₁ (Tree.F.node a (Forest.fold a₁ a₂ children))
-/
#guard_msgs in #check @Tree.fold_node

/--
info: @Forest.fold_cons : ∀ {α : Type} {S₁ S₂ : Type u_1} (a₁ : Tree.F α S₁ S₂ → S₁) (a₂ : Forest.F α S₁ S₂ → S₂) (t : Tree α)
  (f : Forest α), Forest.fold a₁ a₂ (Forest.cons t f) = a₂ (Forest.F.cons (Tree.fold a₁ a₂ t) (Forest.fold a₁ a₂ f))
-/
#guard_msgs in #check @Forest.fold_cons

/--
info: @Tree.fold_ctor : ∀ {α : Type} {S₁ S₂ : Type u_1} (a₁ : Tree.F α S₁ S₂ → S₁) (a₂ : Forest.F α S₁ S₂ → S₂)
  (y : Tree.F α (Tree α) (Forest α)),
  Tree.fold a₁ a₂ (Tree.ctor y) = a₁ (Tree.F.fmap (Tree.fold a₁ a₂) (Forest.fold a₁ a₂) y)
-/
#guard_msgs in #check @Tree.fold_ctor

/--
info: @Tree.fold_eq : ∀ {α : Type} {S₁ S₂ : Type u_1} (a₁ : Tree.F α S₁ S₂ → S₁) (a₂ : Forest.F α S₁ S₂ → S₂) (t : Tree α),
  Tree.fold a₁ a₂ t = a₁ (Tree.F.fmap (Tree.fold a₁ a₂) (Forest.fold a₁ a₂) t.dtor)
-/
#guard_msgs in #check @Tree.fold_eq

/--
info: @Tree.fold_unique : ∀ {α : Type} {S₁ S₂ : Type u_1} (a₁ : Tree.F α S₁ S₂ → S₁) (a₂ : Forest.F α S₁ S₂ → S₂)
  (h₁ : Tree α → S₁) (h₂ : Forest α → S₂),
  (∀ (y : Tree.F α (Tree α) (Forest α)), h₁ (Tree.ctor y) = a₁ (Tree.F.fmap h₁ h₂ y)) →
    (∀ (y : Forest.F α (Tree α) (Forest α)), h₂ (Forest.ctor y) = a₂ (Forest.F.fmap h₁ h₂ y)) →
      ∀ (t : Tree α), h₁ t = Tree.fold a₁ a₂ t
-/
#guard_msgs in #check @Tree.fold_unique

/-- info: @Tree.dtor : {α : Type} → Tree α → Tree.F α (Tree α) (Forest α) -/
#guard_msgs in #check @Tree.dtor

/-- info: @Tree.ctor : {α : Type} → Tree.F α (Tree α) (Forest α) → Tree α -/
#guard_msgs in #check @Tree.ctor

/-- info: @Forest.dtor_cons : ∀ {α : Type} (t : Tree α) (f : Forest α), (Forest.cons t f).dtor = Forest.F.cons t f -/
#guard_msgs in #check @Forest.dtor_cons

/-- info: @Forest.ctor_cons : ∀ {α : Type} (t : Tree α) (f : Forest α), Forest.ctor (Forest.F.cons t f) = Forest.cons t f -/
#guard_msgs in #check @Forest.ctor_cons

/--
info: @Tree.F.fmap_node : ∀ {α : Type} {X₁ X₂ : Type u_1} {Y₁ Y₂ : Type u_2} (f₁ : X₁ → Y₁) (f₂ : X₂ → Y₂) (a : α)
  (children : X₂), Tree.F.fmap f₁ f₂ (Tree.F.node a children) = Tree.F.node a (f₂ children)
-/
#guard_msgs in #check @Tree.F.fmap_node

-- The block-level fold and its rules.
/--
info: @Tree_Forest.fold_cons : ∀ {α : Type} {S : Tree_Forest.Ix α → Type u_1}
  (a : (j₁ : Tree_Forest.Ix α) → Tree_Forest.F α S j₁ → S j₁) (t : Tree α) (f : Forest α),
  Tree_Forest.fold a (Forest.cons t f) =
    a Tree_Forest.Ix.Forest (Tree_Forest.F.cons (Tree_Forest.fold a t) (Tree_Forest.fold a f))
-/
#guard_msgs in #check @Tree_Forest.fold_cons

-- Round trips through the destructor and the constructor per type.
example {α : Type} (t : Tree α) : Tree.ctor t.dtor = t := Tree.ctor_dtor t

example {α : Type} (y : Forest.F α (Tree α) (Forest α)) : (Forest.ctor y).dtor = y :=
  Forest.dtor_ctor y

example {α : Type} (a : α) (cs : Forest α) : (Tree.node a cs).dtor = .node a cs := by simp

example {α : Type} (t : Tree α) (f : Forest α) : Forest.ctor (.cons t f) = .cons t f := by simp

example {α : Type} (x y : Tree.F α (Tree α) (Forest α)) (h : Tree.ctor x = Tree.ctor y) : x = y :=
  Tree.ctor_injective h

-- A match on the destructor per type takes the block functor's constructors.
def Forest.head? {α : Type} (f : Forest α) : Option (Tree α) :=
  match f.dtor with
  | .nil => none
  | .cons t _ => some t

example {α : Type} (t : Tree α) (f : Forest α) : (Forest.cons t f).head? = some t := by
  simp [Forest.head?]

/-- The number of nodes, by the folds per type: an algebra per type. -/
def sizeTree {α : Type} : Tree.F α Nat Nat → Nat
  | .node _ n => n + 1

def sizeForest {α : Type} : Forest.F α Nat Nat → Nat
  | .nil => 0
  | .cons m n => m + n

def Tree.size {α : Type} (t : Tree α) : Nat := Tree.fold sizeTree sizeForest t

def Forest.size {α : Type} (f : Forest α) : Nat := Forest.fold sizeTree sizeForest f

-- `simp` computes it on a concrete tree, by the rules `Tree.fold_node`, `Forest.fold_cons`, …
example :
    (Tree.node 1 (.cons (.node 2 .nil) (.cons (.node 3 (.cons (.node 4 .nil) .nil)) .nil))).size =
      4 := by
  simp [Tree.size, sizeTree, sizeForest]

-- The same through `fold_eq`, `fold_ctor` and the destructor.
example {α : Type} (a : α) (cs : Forest α) : (Tree.node a cs).size = cs.size + 1 := by
  rw [Tree.size, Tree.fold_eq, Tree.dtor_node, Tree.F.fmap_node]
  rfl

/-- The number of nodes, by the recursors per type. -/
def Tree.size' {α : Type} (t : Tree α) : Nat :=
  Tree.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ _ n => n + 1) 0 (fun _ _ m n => m + n) t

def Forest.size' {α : Type} (f : Forest α) : Nat :=
  Forest.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ _ n => n + 1) 0 (fun _ _ m n => m + n) f

/-- Uniqueness of the fold: the sizes by the recursors satisfy the equations of the algebras, so
they are the folds. -/
theorem Tree.size'_eq {α : Type} (t : Tree α) : t.size' = t.size :=
  Tree.fold_unique sizeTree sizeForest Tree.size' Forest.size'
    (fun | .node a cs => by simp [Tree.size', Forest.size', sizeTree])
    (fun
      | .nil => by simp [Forest.size', sizeForest]
      | .cons t f => by simp [Tree.size', Forest.size', sizeForest]) t

-- The families may live in another universe, the same for all types.
example {α : Type} (t : Tree α) : ULift.{2} Nat :=
  Tree.fold (S₁ := ULift.{2} Nat) (S₂ := ULift.{2} Nat) (fun | .node _ n => ⟨n.down + 1⟩)
    (fun | .nil => ⟨0⟩ | .cons m n => ⟨m.down + n.down⟩) t

/-- Over the block: one algebra over `Ix`, and the block-level rules. -/
def sizeAlg {α : Type} : ∀ m, Tree_Forest.F α (fun _ => Nat) m → Nat
  | .Tree, .node _ n => n + 1
  | .Forest, .nil => 0
  | .Forest, .cons m n => m + n

example {α : Type} (t : Tree α) (f : Forest α) :
    Tree_Forest.fold sizeAlg (Forest.cons t f) =
      Tree_Forest.fold sizeAlg t + Tree_Forest.fold sizeAlg f := by
  simp [sizeAlg]

/-! ### Indices: even and odd naturals -/

mutual
datatype Even : Nat → Type
  | zero : Even 0
  | succ {n : Nat} (o : Odd n) : Even (n + 1)
datatype Odd : Nat → Type
  | succ {n : Nat} (e : Even n) : Odd (n + 1)
end

/--
info: @Even.fold : {S₁ S₂ : ℕ → Type u_1} →
  ((i₁ : ℕ) → Even.F S₁ S₂ i₁ → S₁ i₁) → ((i₁ : ℕ) → Odd.F S₁ S₂ i₁ → S₂ i₁) → {i₁ : ℕ} → Even i₁ → S₁ i₁
-/
#guard_msgs in #check @Even.fold

/--
info: @Even.fold_succ : ∀ {S₁ S₂ : ℕ → Type u_1} (a₁ : (i₁ : ℕ) → Even.F S₁ S₂ i₁ → S₁ i₁)
  (a₂ : (i₁ : ℕ) → Odd.F S₁ S₂ i₁ → S₂ i₁) {n : ℕ} (o : Odd n),
  Even.fold a₁ a₂ (Even.succ o) = a₁ (n + 1) (Even.F.succ (Odd.fold a₁ a₂ o))
-/
#guard_msgs in #check @Even.fold_succ

/--
info: @Odd.fold_unique : ∀ {S₁ S₂ : ℕ → Type u_1} (a₁ : (i₁ : ℕ) → Even.F S₁ S₂ i₁ → S₁ i₁)
  (a₂ : (i₁ : ℕ) → Odd.F S₁ S₂ i₁ → S₂ i₁) (h₁ : (i₁ : ℕ) → Even i₁ → S₁ i₁) (h₂ : (i₁ : ℕ) → Odd i₁ → S₂ i₁),
  (∀ (i₁ : ℕ) (y : Even.F Even Odd i₁), h₁ i₁ (Even.ctor y) = a₁ i₁ (Even.F.fmap h₁ h₂ y)) →
    (∀ (i₁ : ℕ) (y : Odd.F Even Odd i₁), h₂ i₁ (Odd.ctor y) = a₂ i₁ (Odd.F.fmap h₁ h₂ y)) →
      ∀ {i₁ : ℕ} (t : Odd i₁), h₂ i₁ t = Odd.fold a₁ a₂ t
-/
#guard_msgs in #check @Odd.fold_unique

/-- The number of `succ`s, by an algebra per type at the type's own index. The constructors of the
layer per type are those of the type (`Even.F.succ`), though the block's functor qualifies a name
that two types share (`Even_Odd.F.Even_succ`). -/
def evenAlg : ∀ n, Even.F (fun _ => Nat) (fun _ => Nat) n → Nat
  | _, .zero => 0
  | _, .succ k => k + 1

def oddAlg : ∀ n, Odd.F (fun _ => Nat) (fun _ => Nat) n → Nat
  | _, .succ k => k + 1

-- The block's names still work.
example : ∀ n, Odd.F (fun _ => Nat) (fun _ => Nat) n → Nat
  | _, .Odd_succ k => k + 1

def Even.toNat {n : Nat} (e : Even n) : Nat := Even.fold evenAlg oddAlg e

example : (Even.succ (Odd.succ Even.zero)).toNat = 2 := by
  simp [Even.toNat, evenAlg, oddAlg]

-- The fields are shown as the types they are by definition, at their indices.
/--
trace: case Even_succ
z : Even.F (fun x => ℕ) (fun x => ℕ) 3
o : Odd (0 + 2)
⊢ True
---
trace: case Even_succ.Even_succ
o✝ : Odd (0 + 2)
o : ℕ
⊢ True
-/
#guard_msgs in
example (y : Even.F Even Odd 3) (z : Even.F (fun _ => Nat) (fun _ => Nat) 3) : True := by
  cases y with
  | Even_succ o =>
    trace_state
    cases z with
    | Even_succ o =>
      trace_state
      trivial

/-- The number of `succ`s is the index, by uniqueness of the fold. -/
theorem Even.toNat_eq {n : Nat} (e : Even n) : e.toNat = n :=
  (Even.fold_unique (S₁ := fun _ => Nat) (S₂ := fun _ => Nat) evenAlg oddAlg (fun n _ => n)
    (fun n _ => n) (fun | _, .zero => rfl | _, .Even_succ _ => rfl)
    (fun | _, .Odd_succ _ => rfl) e).symm

/-! ### Three types -/

mutual
datatype A3
  | leaf
  | mk (b : B3)
datatype B3
  | mk (c : C3) (a : A3)
datatype C3
  | mk (a : A3)
end

/-- info: @A3.fold : {S₁ S₂ S₃ : Type u_1} → (A3.F S₁ S₂ S₃ → S₁) → (B3.F S₁ S₂ S₃ → S₂) → (C3.F S₁ S₂ S₃ → S₃) → A3 → S₁ -/
#guard_msgs in #check @A3.fold

/-- The number of constructors. -/
def A3.count (x : A3) : Nat :=
  A3.fold (S₁ := Nat) (S₂ := Nat) (S₃ := Nat) (fun | .leaf => 1 | .A3_mk n => n + 1)
    (fun | .B3_mk m n => m + n + 1) (fun | .C3_mk n => n + 1) x

example : (A3.mk (.mk (.mk .leaf) .leaf)).count = 5 := by
  simp [A3.count]

example (y : C3.F A3 B3 C3) : (C3.ctor y).dtor = y := C3.dtor_ctor y

/-! ### Nesting through a list

The rule of a nested argument maps it by the folds per type packed on the block's index, which
`simp` takes to the fold of the type at the index of the positions (`IOcc.map_ofOcc`). -/

mutual
datatype NRose (α : Type)
  | node (a : α) (cs : List (NRose α)) (b : NBush α)
datatype NBush (α : Type)
  | leaf
  | grow (r : NRose α) (b : NBush α)
end

def sizeNRose {α : Type} : NRose.F α Nat Nat → Nat
  | .node _ cs b => cs.sum + b + 1

def sizeNBush {α : Type} : NBush.F α Nat Nat → Nat
  | .leaf => 0
  | .grow r b => r + b

def NRose.size {α : Type} (t : NRose α) : Nat := NRose.fold sizeNRose sizeNBush t

example :
    (NRose.node 1 [.node 2 [] .leaf, .node 3 [] .leaf] (.grow (.node 4 [] .leaf) .leaf)).size =
      4 := by
  simp [NRose.size, sizeNRose, sizeNBush]

/-! ### A run of a `mixed_mutual` block that is a block: the closed types get the same
interface -/

mixed_mutual
codatatype T (α : Type)
  | node (a : α) (r : Rose α)
datatype Rose (α : Type)
  | node (t : T α) (f : Bush α)
datatype Bush (α : Type)
  | nil
  | cons (r : Rose α) (f : Bush α)
end

/-- info: @Rose.fold : {α : Type} → {S₁ S₂ : Type u_1} → (Rose.F α S₁ S₂ → S₁) → (Bush.F α S₁ S₂ → S₂) → Rose α → S₁ -/
#guard_msgs in #check @Rose.fold

def sizeRose {α : Type} : Rose.F α Nat Nat → Nat
  | .node _ n => n + 1

def sizeBush {α : Type} : Bush.F α Nat Nat → Nat
  | .nil => 0
  | .cons m n => m + n

example {α : Type} (t : T α) :
    Rose.fold sizeRose sizeBush (.node t (.cons (.node t .nil) .nil)) = 2 := by
  simp [sizeRose, sizeBush]

end

end MutualFoldTest
