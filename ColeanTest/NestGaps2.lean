import Colean.MutualCmd

/-! # Test: `simp` through families and built-in leaves, and fields in two variables

The generated API used through the instances in the cases that `ColeanTest/NestGaps.lean` left
open:

* the rules of a family whose nested argument has an indexed structure (`T n × T (n + 1)`):
  `simp` computes the map through `IOcc.prod` (`IOcc.map_prod`, `IOcc.map_hole`), and the
  hypothesis of the recursor by membership at the holes, one for each component
  (`IPolyIso.forall_eq_heq_or_imp`, `IPolyIso.forall_or_eq_heq_imp`,
  `IPolyIso.forall_eq_heq_imp`);
* the map at the identity's leaf as the function of another map (`List α`): `simp` makes it
  `List.map f` (`Occ.ofIso_id`, `Occ.map_hole_hole`);
* an expression with the type in an argument of a leaf other than its last (`E (T × Nat) Nat`):
  the recursor's hypothesis is the instance that instance search finds, and `simp` computes the
  map at its premise, a built-in form (`Occ.ofIso_prod`);
* a parameter in the same field as the type under a named type constructor or a function
  (`p : List (α × S α)`, `k : Nat → α × T α`), in a single type and in a mixed block
  (`List (Tree α × Forest α)`): the field has a structure in two variables (`Occ₂`), and the
  rules of the map and of membership go through it. -/

universe u

namespace NestGaps2Test

open Codata

noncomputable section

/-! ### A family with a product of occurrences at two indices -/

datatype Chain : Nat → Type
  | zero : Chain 0
  | one : Chain 1
  | link {n : Nat} (p : Chain n × Chain (n + 1)) : Chain (n + 2)

/-- The number of ends, by `fold`, whose rule maps through `IOcc.prod`. -/
def Chain.size {n : Nat} (t : Chain n) : Nat :=
  Chain.fold (S := fun _ => Nat) (fun _ y => Chain.F.casesOn y 1 1 fun p => p.1 + p.2) t

example : (Chain.link (.zero, .one)).size = 2 := by
  simp [Chain.size]

example : (Chain.link (.one, .link (.zero, .one))).size = 3 := by
  simp [Chain.size]

/-- Induction: `simp` makes the hypothesis by membership one for each component. -/
theorem Chain.ind (P : ∀ n, Chain n → Prop) (h0 : P 0 .zero) (h1 : P 1 .one)
    (hl : ∀ n (a : Chain n) (b : Chain (n + 1)), P n a → P (n + 1) b → P (n + 2) (.link (a, b)))
    (n : Nat) (t : Chain n) : P n t := by
  induction t with
  | zero => exact h0
  | one => exact h1
  | @link n p ih =>
    simp at ih
    guard_hyp ih :ₛ P n p.1 ∧ P (n + 1) p.2
    exact hl _ p.1 p.2 ih.1 ih.2

datatype Chain3 : Nat → Type
  | zero : Chain3 0
  | one : Chain3 1
  | two : Chain3 2
  | link {n : Nat} (p : Chain3 n × Chain3 (n + 1) × Chain3 (n + 2)) : Chain3 (n + 3)

/-- With three components, the last a single hole (`IPolyIso.forall_eq_heq_or_imp`, then
`IPolyIso.forall_eq_heq_imp`). -/
example (P : ∀ n, Chain3 n → Prop) (n : Nat) (p : Chain3 n × Chain3 (n + 1) × Chain3 (n + 2))
    (ih : ∀ j t, IPolyIso.Mem (fun X => X n × X (n + 1) × X (n + 2)) j t p → P j t) :
    P n p.1 ∧ P (n + 1) p.2.1 ∧ P (n + 2) p.2.2 := by
  simp at ih
  guard_hyp ih :ₛ P n p.1 ∧ P (n + 1) p.2.1 ∧ P (n + 2) p.2.2
  exact ih

datatype ChainL : Nat → Type
  | zero : ChainL 0
  | link {n : Nat} (p : List (ChainL n) × ChainL (n + 1)) : ChainL (n + 2)

/-- With the hole last after a list at another index (`IPolyIso.forall_or_eq_heq_imp`,
`IPolyIso.forall_forall_eq_heq_imp`). -/
theorem ChainL.ind (P : ∀ n, ChainL n → Prop) (h0 : P 0 .zero)
    (hl : ∀ n (l : List (ChainL n)) (b : ChainL (n + 1)), (∀ a ∈ l, P n a) → P (n + 1) b →
      P (n + 2) (.link (l, b)))
    (n : Nat) (t : ChainL n) : P n t := by
  induction t with
  | zero => exact h0
  | @link n p ih =>
    simp at ih
    guard_hyp ih :ₛ (∀ x ∈ p.1, P n x) ∧ P (n + 1) p.2
    exact hl _ p.1 p.2 ih.1 ih.2

/-! ### The map at a hole as the function of another map

`simp` makes the identity's leaf the hole (`Occ.ofIso_id`), and the map through a hole the
function also where it is not applied (`Occ.map_hole_hole`, `IOcc.map_hole_hole`): the map of a
list field is `List.map f`. -/

datatype PL (α : Type u)
  | mk (l : List α)

example (f : Nat → Nat) (l : List Nat) (x : PL Nat) (h : PL.mk (l.map f) = x) :
    (Occ.ofIso PL).map (Occ.ofIso PL) f (PL.mk l) = x := by
  simp
  guard_target =ₛ PL.mk (List.map f l) = x
  exact h

example {X Y : Nat → Type} (f : ∀ j, X j → Y j) (n : Nat) (l : List (X n)) (x : List (Y n))
    (h : l.map (f n) = x) :
    IOcc.map (IOcc.compC (Occ.ofIso List) (IOcc.hole n))
      (IOcc.compC (Occ.ofIso List) (IOcc.hole n)) f l = x := by
  simp
  guard_target =ₛ List.map (f n) l = x
  exact h

/-! ### A built-in form in an argument of a leaf other than its last -/

datatype E (α β : Type u)
  | l (a : α)
  | r (b : β)

datatype EProd
  | leaf
  | mk (p : E (EProd × Nat) Nat)

/--
info: @EProd.rec : {motive : EProd → Sort u_1} →
  motive EProd.leaf →
    ((p : E (EProd × ℕ) ℕ) → ((t : EProd) → PolyIso.Mem (fun X => E (X × ℕ) ℕ) t p → motive t) → motive (EProd.mk p)) →
      (t : EProd) → motive t
-/
#guard_msgs in
#check @EProd.rec

/-- A hypothesis written by hand with the instance that instance search finds is the recursor's.
-/
theorem EProd.ind (P : EProd → Prop) (hl : P .leaf)
    (hn : ∀ p, (∀ t, PolyIso.Mem (fun X => E (X × Nat) Nat) t p → P t) → P (.mk p))
    (t : EProd) : P t := by
  induction t with
  | leaf => exact hl
  | mk p ih => exact hn p ih

def EProd.size : EProd → Nat :=
  EProd.fold (S := Nat) fun
    | .leaf => 1
    | .mk p => E.fold (S := Nat) (fun | .l q => q.1 + q.2 | .r n => n) p + 1

example : (EProd.mk (.l (.mk (.r 3), 2))).size = 7 := by
  simp [EProd.size]

example (t a : EProd) (n : Nat) : PolyIso.Mem (fun X => E (X × Nat) Nat) t (.l (a, n)) ↔ t = a := by
  simp

-- With the type in both arguments, as before.
datatype EProdBoth
  | leaf
  | mk (p : E (EProdBoth × Nat) EProdBoth)

def EProdBoth.size : EProdBoth → Nat :=
  EProdBoth.fold (S := Nat) fun
    | .leaf => 1
    | .mk p => E.fold (S := Nat) (fun | .l q => q.1 + q.2 | .r n => n) p + 1

example : (EProdBoth.mk (.l (.mk (.r .leaf), 2))).size = 5 := by
  simp [EProdBoth.size]

/-! ### A parameter with the type under a named type constructor -/

codatatype S (α : Type u)
  | mk (p : List (α × S α))

/-- info: S.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso S.{0} _ _

/--
info: @S.Colean.Poly.map_mk : ∀ {H : Type u_2 → Type u_1} {H' : Type u_3 → Type u_6} {S : Type u_4} {R : S → Type u_5}
  [inst : PolyIso H S R] [inst' : PolyIso H' S R] {X : Type u_2} {Y : Type u_3} (f : X → Y)
  (p : List (H X × NestGaps2Test.S (H X))),
  (Occ.ofIso fun X => NestGaps2Test.S (H X)).map (Occ.ofIso fun X => NestGaps2Test.S (H' X)) f (NestGaps2Test.S.mk p) =
    NestGaps2Test.S.mk
      ((Occ₂.comp (Occ.ofIso List) ((Occ₂.ofX (Occ.ofIso H)).prod (Occ₂.ofY Occ.hole))).map
        (Occ₂.comp (Occ.ofIso List) ((Occ₂.ofX (Occ.ofIso H')).prod (Occ₂.ofY Occ.hole))) f
        (fun t => (Occ.ofIso fun X => NestGaps2Test.S (H X)).map (Occ.ofIso fun X => NestGaps2Test.S (H' X)) f t) p)
-/
#guard_msgs(whitespace := lax) in
#check @S.Colean.Poly.map_mk

/--
info: @S.Colean.Poly.mem_mk : ∀ {H : Type u_2 → Type u_1} {S : Type u_3} {R : S → Type u_4} [inst : PolyIso H S R] {X : Type u_2}
  (x : X) (p : List (H X × NestGaps2Test.S (H X))),
  PolyIso.Mem (fun X => NestGaps2Test.S (H X)) x (NestGaps2Test.S.mk p) ↔
    PolyIso.Mem (fun X_1 => List (H X_1 × NestGaps2Test.S (H X))) x p ∨
      ∃ t, PolyIso.Mem (fun X_1 => List (H X × X_1)) t p ∧ PolyIso.Mem (fun X => NestGaps2Test.S (H X)) x t
-/
#guard_msgs(whitespace := lax) in
#check @S.Colean.Poly.mem_mk

example (f : Nat → Nat) (a b : Nat) :
    (Occ.ofIso S).map (Occ.ofIso S) f (S.mk [(a, S.mk []), (b, S.mk [])]) =
      S.mk [(f a, S.mk []), (f b, S.mk [])] := by
  simp

example (x a b : Nat) (s : S Nat) :
    PolyIso.Mem S x (S.mk [(a, s), (b, S.mk [])]) ↔ (x = a ∨ x = b) ∨ PolyIso.Mem S x s := by
  simp

/-- The stream `a, a, …` along the first child, by `corec`. -/
def S.const {α : Type u} (a : α) : S α :=
  S.corec (S := Unit) (fun _ => .mk [(a, ())]) ()

theorem S.const_eq {α : Type u} (a : α) : S.const a = .mk [(a, .const a)] := by
  conv_lhs => rw [← S.ctor_dtor (S.const a), S.const, S.dtor_corec]
  simp [S.const]

example (x a : Nat) : PolyIso.Mem S x (S.const a) ↔ x = a ∨ PolyIso.Mem S x (S.const a) := by
  conv_lhs => rw [S.const_eq]
  simp

-- Nesting through it: the rules of the outer type map through `S`'s.
datatype ThroughS
  | leaf
  | mk (s : S ThroughS)

def ThroughS.size : ThroughS → Nat :=
  ThroughS.fold (S := Nat) fun
    | .leaf => 1
    | .mk s => s.casesOn (fun l => (l.map fun p => p.1).sum) + 1

example : (ThroughS.mk (.mk [(.leaf, .mk []), (.mk (.mk []), .mk [])])).size = 3 := by
  simp [ThroughS.size]

/-! ### A parameter with the type under a function -/

datatype FPair (α : Type u)
  | leaf
  | mk (k : Nat → α × FPair α)

/-- info: FPair.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso FPair.{0} _ _

example (f : Nat → Nat) :
    (Occ.ofIso FPair).map (Occ.ofIso FPair) f (FPair.mk fun n => (n, .leaf)) =
      FPair.mk fun n => (f n, .leaf) := by
  simp

example (x : Nat) : PolyIso.Mem FPair x (FPair.mk fun n => (n, .leaf)) := by
  simp

/-! ### In a mixed block

`p : List (Tree α × Forest α)` becomes `p : List (X × Forest.Open α X)` in the open forests: the
parameter for the trees in the same field as the forests' own recursion, under `List`. -/

namespace ListPair

mixed_mutual
codatatype Tree (α : Type u)
  | node (a : α) (children : Forest α)
datatype Forest (α : Type u)
  | nil
  | cons (p : List (Tree α × Forest α))
end

/--
info: @Forest.mem_cons : ∀ {α : Type u_1} (p : List (Tree α × Forest α)) (x : Tree α),
  x ∈ Forest.cons p ↔ (∃ x_1, (x, x_1) ∈ p) ∨ ∃ t, (∃ a, (a, t) ∈ p) ∧ x ∈ t
-/
#guard_msgs in
#check @Forest.mem_cons

/-- The tree with one copy of itself as its child. -/
def Tree.loop {α : Type u} (a : α) : Tree α :=
  Tree.corec (S := Unit) (fun _ => .node a (.cons [((), .nil)])) ()

theorem Tree.loop_eq {α : Type u} (a : α) : Tree.loop a = .node a (.cons [(.loop a, .nil)]) := by
  conv_lhs => rw [← Tree.ctor_dtor (Tree.loop a), Tree.loop, Tree.dtor_corec]
  simp [Tree.loop]

example {α : Type u} (s t : Tree α) : t ∈ Forest.cons [(s, .nil), (t, .nil)] := by simp

end ListPair

end

end NestGaps2Test
