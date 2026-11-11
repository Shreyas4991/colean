import Colean.MutualCmd

/-! # Test: fields in two variables across a sum, in families and in blocks

The generated API through the instances in the cases that `ColeanTest/NestGaps2.lean` left open:

* a parameter with the type across a sum inside a named type constructor (`List (α ⊕ T α)`), in a
  single type and in a mixed block (`List (Tree α ⊕ Forest α)`): the field's structure in two
  variables goes through the sum, and its membership is stated by `Occ₂.MemX` and `Occ₂.MemY`,
  which `simp` computes through the combinators;
* a parameter in the same field as the recursion of a family (`List (α × T n)`) and a type of a
  block reached through a container (`List (RA α × Nat)`): the field has an indexed structure in
  two variables (`IOcc₂`, `Model/IOcc2.lean`), here a plain one at one index (`IOcc₂.ofOcc₂`), so
  its rules are those of a single type, at the type of its members;
* a family with the positions of such a field at several indices (`List (α × T n × T (n + 1))`):
  the rules are stated by the indexed structure, a member in `Y` with its index;
* `forall_or_eq_imp` as a `simp` lemma: a hypothesis by membership in a pair of a container and an
  occurrence splits. -/

universe u

namespace NestGaps3Test

open Codata

noncomputable section

/-! ### A sum inside a named type constructor -/

data LS (α : Type u)
  | nil
  | mk (p : List (α ⊕ LS α))

/-- info: LS.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso LS.{0} _ _

/--
info: @LS.Poly.map_mk : ∀ {H : Type u_2 → Type u_1} {H' : Type u_3 → Type u_6} {S : Type u_4} {R : S → Type u_5}
  [inst : PolyIso H S R] [inst' : PolyIso H' S R] {X : Type u_2} {Y : Type u_3} (f : X → Y) (p : List (H X ⊕ LS (H X))),
  (Occ.ofIso fun X => LS (H X)).map (Occ.ofIso fun X => LS (H' X)) f (LS.mk p) =
    LS.mk
      ((Occ₂.comp (Occ.ofIso List) ((Occ₂.ofX (Occ.ofIso H)).sum (Occ₂.ofY Occ.hole))).map
        (Occ₂.comp (Occ.ofIso List) ((Occ₂.ofX (Occ.ofIso H')).sum (Occ₂.ofY Occ.hole))) f
        (fun t => (Occ.ofIso fun X => LS (H X)).map (Occ.ofIso fun X => LS (H' X)) f t) p)
-/
#guard_msgs(whitespace := lax) in
#check @LS.Poly.map_mk

/--
info: @LS.Poly.mem_mk : ∀ {H : Type u_2 → Type u_1} {S : Type u_3} {R : S → Type u_4} [inst : PolyIso H S R] {X : Type u_2}
  (x : X) (p : List (H X ⊕ LS (H X))),
  PolyIso.Mem (fun X => LS (H X)) x (LS.mk p) ↔
    (Occ₂.comp (Occ.ofIso List) ((Occ₂.ofX (Occ.ofIso H)).sum (Occ₂.ofY Occ.hole))).MemX x p ∨
      ∃ t,
        (Occ₂.comp (Occ.ofIso List) ((Occ₂.ofX (Occ.ofIso H)).sum (Occ₂.ofY Occ.hole))).MemY t p ∧
          PolyIso.Mem (fun X => LS (H X)) x t
-/
#guard_msgs(whitespace := lax) in
#check @LS.Poly.mem_mk

example (f : Nat → Nat) (a : Nat) (l : LS Nat) :
    (Occ.ofIso LS).map (Occ.ofIso LS) f (LS.mk [.inl a, .inr l]) =
      LS.mk [.inl (f a), .inr ((Occ.ofIso LS).map (Occ.ofIso LS) f l)] := by
  simp

example (x : Nat) (p : List (Nat ⊕ LS Nat)) :
    PolyIso.Mem LS x (LS.mk p) ↔ Sum.inl x ∈ p ∨ ∃ t, Sum.inr t ∈ p ∧ PolyIso.Mem LS x t := by
  simp

/-- Induction: `simp` makes the hypothesis by membership one on the right injections. -/
theorem LS.ind {α : Type u} (P : LS α → Prop) (h0 : P .nil)
    (hm : ∀ p, (∀ t, Sum.inr t ∈ p → P t) → P (.mk p)) (t : LS α) : P t := by
  induction t with
  | nil => exact h0
  | mk p ih =>
    simp at ih
    guard_hyp ih :ₛ ∀ (t : LS α), Sum.inr t ∈ p → P t
    exact hm p ih

/-- The sum of the left injections, by `fold`. -/
def LS.total : LS Nat → Nat :=
  LS.fold (S := Nat) fun
    | .nil => 0
    | .mk p => (p.map fun | .inl a => a | .inr n => n).sum

example : (LS.mk [.inl 2, .inr (.mk [.inl 3])]).total = 5 := by
  simp [LS.total]

-- Nesting through it.
data ThroughLS
  | leaf
  | mk (s : LS ThroughLS)

example (t : ThroughLS) : PolyIso.Mem LS t (LS.mk [.inl t]) := by
  simp

/-- The size of a tree nested through `LS`, by the folds of the two types. -/
def ThroughLS.size : ThroughLS → Nat :=
  ThroughLS.fold (S := Nat) fun
    | .leaf => 1
    | .mk s => LS.fold (S := Nat)
        (fun | .nil => 0 | .mk p => (p.map fun | .inl n => n | .inr n => n).sum) s + 1

example : (ThroughLS.mk (.mk [.inl .leaf, .inr (.mk [.inl .leaf])])).size = 3 := by
  simp [ThroughLS.size]

-- Several occurrences in one element: the members with a property are eliminated at each one
-- (`Occ₂.exists_memY_prod`, …).
data L2 (α : Type u)
  | nil
  | mk (p : List (α ⊕ L2 α × L2 α))

example (x : Nat) (p : List (Nat ⊕ L2 Nat × L2 Nat)) :
    PolyIso.Mem L2 x (L2.mk p) ↔
      Sum.inl x ∈ p ∨ ∃ a b, Sum.inr (a, b) ∈ p ∧ (PolyIso.Mem L2 x a ∨ PolyIso.Mem L2 x b) := by
  simp

/-! ### In a mixed block

`p : List (Tree α ⊕ Forest α)` becomes `p : List (X ⊕ Forest.Open α X)` in the open forests: the
parameter for the trees and the forests' own recursion on the two sides of a sum, inside `List`.
-/

namespace ListSum

mixed_mutual
codata Tree (α : Type u)
  | node (a : α) (children : Forest α)
data Forest (α : Type u)
  | nil
  | cons (p : List (Tree α ⊕ Forest α))
end

/--
info: @Forest.mem_cons : ∀ {α : Type u_1} (p : List (Tree α ⊕ Forest α)) (x : Tree α),
  x ∈ Forest.cons p ↔ Sum.inl x ∈ p ∨ ∃ b, Sum.inr b ∈ p ∧ x ∈ b
-/
#guard_msgs in
#check @Forest.mem_cons

/-- The tree with itself as its only child, by `corec`. -/
def Tree.loop {α : Type u} (a : α) : Tree α :=
  Tree.corec (S := Unit) (fun _ => .node a (.cons [.inl ()])) ()

theorem Tree.loop_eq {α : Type u} (a : α) : Tree.loop a = .node a (.cons [.inl (.loop a)]) := by
  conv_lhs => rw [← Tree.ctor_dtor (Tree.loop a), Tree.loop, Tree.dtor_corec]
  simp [Tree.loop]

example {α : Type u} (s t : Tree α) : t ∈ Forest.cons [.inl s, .inr (.cons [.inl t])] := by
  simp

end ListSum

/-! ### A parameter with the recursion of a family -/

data LF (α : Type u) : Nat → Type u
  | nil {n : Nat} : LF α n
  | mk {n : Nat} (p : List (α × LF α n)) : LF α (n + 1)

/-- info: LF.Poly.instPolyIso 3 -/
#guard_msgs in
#synth PolyIso (fun X : Type => LF X 3) _ _

/--
info: @LF.Poly.map_mk : ∀ {H : Type u_2 → Type u_1} {H' : Type u_3 → Type u_6} {S : Type u_4} {R : S → Type u_5}
  [inst : PolyIso H S R] [inst' : PolyIso H' S R] {X : Type u_2} {Y : Type u_3} (f : X → Y) {n : ℕ}
  (p : List (H X × LF (H X) n)),
  (Occ.ofIso fun X => LF (H X) (n + 1)).map (Occ.ofIso fun X => LF (H' X) (n + 1)) f (LF.mk p) =
    LF.mk
      ((Occ₂.comp (Occ.ofIso List) ((Occ₂.ofX (Occ.ofIso H)).prod (Occ₂.ofY Occ.hole))).map
        (Occ₂.comp (Occ.ofIso List) ((Occ₂.ofX (Occ.ofIso H')).prod (Occ₂.ofY Occ.hole))) f
        (fun t => (Occ.ofIso fun X => LF (H X) n).map (Occ.ofIso fun X => LF (H' X) n) f t) p)
-/
#guard_msgs(whitespace := lax) in
#check @LF.Poly.map_mk

/--
info: @LF.Poly.mem_mk : ∀ {H : Type u_2 → Type u_1} {S : Type u_3} {R : S → Type u_4} [inst : PolyIso H S R] {X : Type u_2}
  (x : X) {n : ℕ} (p : List (H X × LF (H X) n)),
  PolyIso.Mem (fun X => LF (H X) (n + 1)) x (LF.mk p) ↔
    PolyIso.Mem (fun X_1 => List (H X_1 × LF (H X) n)) x p ∨
      ∃ t, PolyIso.Mem (fun X_1 => List (H X × X_1)) t p ∧ PolyIso.Mem (fun X => LF (H X) n) x t
-/
#guard_msgs(whitespace := lax) in
#check @LF.Poly.mem_mk

example (f : Nat → Nat) (a b : Nat) :
    (Occ.ofIso fun X => LF X 1).map (Occ.ofIso fun X => LF X 1) f (LF.mk [(a, .nil), (b, .nil)]) =
      LF.mk [(f a, .nil), (f b, .nil)] := by
  simp

example (x : Nat) {n : Nat} (p : List (Nat × LF Nat n)) :
    PolyIso.Mem (fun X => LF X (n + 1)) x (LF.mk p) ↔
      (∃ t, (x, t) ∈ p) ∨ ∃ t, (∃ a, (a, t) ∈ p) ∧ PolyIso.Mem (fun X => LF X n) x t := by
  simp

/-- Induction: the hypothesis by membership is at the index of the members. -/
theorem LF.ind {α : Type u} (P : ∀ n, LF α n → Prop) (h0 : ∀ n, P n .nil)
    (hm : ∀ n (p : List (α × LF α n)), (∀ t a, (a, t) ∈ p → P n t) → P (n + 1) (.mk p))
    {n : Nat} (t : LF α n) : P n t := by
  induction t with
  | nil => exact h0 _
  | @mk n p ih =>
    simp at ih
    guard_hyp ih :ₛ ∀ (t : LF α n) (x : α), (x, t) ∈ p → P n t
    exact hm _ p ih

/-- The number of leaves, by `fold`. -/
def LF.leaves {α : Type u} {n : Nat} (t : LF α n) : Nat :=
  LF.fold (S := fun _ => Nat) (fun _ y => LF.F.casesOn y 1 fun p => (p.map (·.2)).sum) t

example : (LF.mk [((), LF.nil), ((), .nil)] : LF Unit 1).leaves = 2 := by
  simp [LF.leaves]

-- Nesting through it at an index.
data ThroughLF
  | leaf
  | mk (t : LF ThroughLF 2)

example (t : ThroughLF) : PolyIso.Mem (fun X => LF X 2) t (LF.mk [(t, .nil)]) := by
  simp

/-! ### A type of a block reached through a container -/

mutual
data RA (α : Type u)
  | nil
  | mk (a : α) (p : List (RA α × Nat))
data RB (α : Type u)
  | mk (a : RA α)
end

/-- info: RA.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso RA.{0} _ _

/--
info: @RA.Poly.map_mk : ∀ {H : Type u_2 → Type u_1} {H' : Type u_3 → Type u_6} {S : Type u_4} {R : S → Type u_5}
  [inst : PolyIso H S R] [inst' : PolyIso H' S R] {X : Type u_2} {Y : Type u_3} (f : X → Y) (a : H X)
  (p : List (RA (H X) × ℕ)),
  (Occ.ofIso fun X => RA (H X)).map (Occ.ofIso fun X => RA (H' X)) f (RA.mk a p) =
    RA.mk ((Occ.ofIso H).map (Occ.ofIso H') f a)
      ((Occ₂.ofY ((Occ.ofIso List).comp (Occ.hole.prod (Occ.const ℕ)))).map
        (Occ₂.ofY ((Occ.ofIso List).comp (Occ.hole.prod (Occ.const ℕ)))) f
        (fun t => (Occ.ofIso fun X => RA (H X)).map (Occ.ofIso fun X => RA (H' X)) f t) p)
-/
#guard_msgs(whitespace := lax) in
#check @RA.Poly.map_mk

example (f : Nat → Nat) (a b : Nat) :
    (Occ.ofIso RA).map (Occ.ofIso RA) f (RA.mk a [(.mk b [], 1)]) =
      RA.mk (f a) [(.mk (f b) [], 1)] := by
  simp

example (x a : Nat) (p : List (RA Nat × Nat)) :
    PolyIso.Mem RA x (RA.mk a p) ↔ x = a ∨ ∃ t, (∃ n, (t, n) ∈ p) ∧ PolyIso.Mem RA x t := by
  simp

/-- The number of nodes, by the recursor of the block, with its hypothesis by membership. -/
def RA.size {α : Type u} : RA α → Nat :=
  RA.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) 1
    (fun _ p ih => (p.attach.map fun q => ih q.1.1 (by simpa using ⟨q.1.2, q.2⟩)).sum + 1)
    (fun _ n => n)

example : (RA.mk 0 [(.mk 1 [], 2), (.nil, 3)]).size = 3 := by
  simp [RA.size, RA.rec_mk, RA.rec_nil]

-- Nesting through it.
data ThroughRA
  | leaf
  | mk (r : RA ThroughRA)

example (t : ThroughRA) : PolyIso.Mem RA t (RA.mk t []) := by
  simp

/-! ### A field of a family at several indices -/

data Ch (α : Type u) : Nat → Type u
  | leaf {n : Nat} : Ch α n
  | mk {n : Nat} (p : List (α × Ch α n × Ch α (n + 1))) : Ch α (n + 2)

/-- info: Ch.Poly.instPolyIso 3 -/
#guard_msgs in
#synth PolyIso (fun X : Type => Ch X 3) _ _

/--
info: @Ch.Poly.mem_mk : ∀ {H : Type u_2 → Type u_1} {S : Type u_3} {R : S → Type u_4} [inst : PolyIso H S R] {X : Type u_2}
  (x : X) {n : ℕ} (p : List (H X × Ch (H X) n × Ch (H X) (n + 1))),
  PolyIso.Mem (fun X => Ch (H X) (n + 2)) x (Ch.mk p) ↔
    (IOcc₂.comp (Occ.ofIso List)
            ((IOcc₂.ofX (Occ.ofIso H)).prod ((IOcc₂.ofY (IOcc.hole n)).prod (IOcc₂.ofY (IOcc.hole (n + 1)))))).MemX
        x p ∨
      ∃ t,
        (IOcc₂.comp (Occ.ofIso List)
                ((IOcc₂.ofX (Occ.ofIso H)).prod ((IOcc₂.ofY (IOcc.hole n)).prod (IOcc₂.ofY (IOcc.hole (n + 1)))))).MemY
            t p ∧
          PolyIso.Mem (fun X_1 => Ch (H X_1) t.fst) x t.snd
-/
#guard_msgs(whitespace := lax) in
#check @Ch.Poly.mem_mk

example (f : Nat → Nat) (a : Nat) :
    (Occ.ofIso fun X => Ch X 2).map (Occ.ofIso fun X => Ch X 2) f (Ch.mk [(a, .leaf, .leaf)]) =
      Ch.mk [(f a, .leaf, .leaf)] := by
  simp

/-- The members in `Y` with their indices: `simp` eliminates them at each occurrence. -/
example (x : Nat) {n : Nat} (p : List (Nat × Ch Nat n × Ch Nat (n + 1))) :
    PolyIso.Mem (fun X => Ch X (n + 2)) x (Ch.mk p) ↔
      (∃ a b, (x, a, b) ∈ p) ∨ ∃ a b c, (a, b, c) ∈ p ∧
        (PolyIso.Mem (fun X => Ch X n) x b ∨ PolyIso.Mem (fun X => Ch X (n + 1)) x c) := by
  simp

/-! ### A hypothesis by membership in a pair of a container and an occurrence -/

data LP
  | leaf
  | mk (p : List LP × LP)

/-- `simp` splits `∀ t, t ∈ p.1 ∨ t = p.2 → P t` (`forall_or_eq_imp`). -/
theorem LP.ind (P : LP → Prop) (h0 : P .leaf)
    (hm : ∀ l t, (∀ s ∈ l, P s) → P t → P (.mk (l, t))) (t : LP) : P t := by
  induction t with
  | leaf => exact h0
  | mk p ih =>
    simp at ih
    guard_hyp ih :ₛ (∀ (t : LP), t ∈ p.1 → P t) ∧ P p.2
    exact hm p.1 p.2 ih.1 ih.2

end

end NestGaps3Test
