import Colean.MutualCmd

/-! # Test: a run of several types inside a mixed block

An inner run of two `datatype`s is one block, declared open (`Rose_Forest.Open` over the index
`Rose_Forest.Ix`, with the types `Rose.Open` and `Forest.Open`), and closed as `Rose_Forest`,
`Rose` and `Forest` with the interface of a `mutual` block: per-type constructors, `casesOn`,
folds, and recursors with a motive per type. -/

universe u

namespace MixedBlockTest

open Codata

noncomputable section

mixed_mutual
codatatype T (α : Type u)
  | node (a : α) (r : Rose α)
datatype Rose (α : Type u)
  | node (t : T α) (f : Forest α)
datatype Forest (α : Type u)
  | nil
  | cons (r : Rose α) (f : Forest α)
end

/-- info: @T.node : {α : Type u_1} → α → Rose α → T α -/
#guard_msgs in #check @T.node
/-- info: @Rose.node : {α : Type u_1} → T α → Forest α → Rose α -/
#guard_msgs in #check @Rose.node
/-- info: @Forest.cons : {α : Type u_1} → Rose α → Forest α → Forest α -/
#guard_msgs in #check @Forest.cons
/--
info: @Rose.rec : {α : Type u_2} →
  {motive_1 : Rose α → Sort u_1} →
    {motive_2 : Forest α → Sort u_1} →
      ((t : T α) → (f : Forest α) → motive_2 f → motive_1 (Rose.node t f)) →
        motive_2 Forest.nil →
          ((r : Rose α) → (f : Forest α) → motive_1 r → motive_2 f → motive_2 (Forest.cons r f)) →
            (t : Rose α) → motive_1 t
-/
#guard_msgs in #check @Rose.rec
/--
info: Rose_Forest.F : (α : Type u_1) → (Rose_Forest.Ix α → Type u_2) → Rose_Forest.Ix α → Type (max u_2 u_1)
-/
#guard_msgs in #check @Rose_Forest.F
/-- info: @Rose_Forest.Ix.Rose : {α : Type u_1} → Rose_Forest.Ix α -/
#guard_msgs in #check @Rose_Forest.Ix.Rose
/--
info: @Forest.mem_cons : ∀ {α : Type u_1} (r : Rose α) (f : Forest α) (x : T α), x ∈ Forest.cons r f ↔ x ∈ r ∨ x ∈ f
-/
#guard_msgs in #check @Forest.mem_cons
/--
info: @Rose.mem_node : ∀ {α : Type u_1} (t : T α) (f : Forest α) (x : T α), x ∈ Rose.node t f ↔ x = t ∨ x ∈ f
-/
#guard_msgs in #check @Rose.mem_node

/-- The number of roses in a rose, by the recursors per type. -/
def Rose.size {α : Type u} (r : Rose α) : Nat :=
  Rose.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ _ n => n + 1) 0 (fun _ _ a b => a + b) r

example {α : Type u} (t : T α) : (Rose.node t (.cons (.node t .nil) .nil)).size = 2 := by
  simp [Rose.size]

example {α : Type u} (f : Forest α) : f = .nil ∨ ∃ r g, f = .cons r g := by
  cases f with
  | nil => exact .inl rfl
  | cons r g => exact .inr ⟨r, g, rfl⟩

/-- A tree whose rose holds itself twice, corecursively; the state goes into the open roses. -/
def T.twice {α : Type u} (a : α) : T α :=
  T.corec (S := Unit) (fun _ => .node a (.node () (.cons (.node () .nil) .nil))) ()

theorem T.twice_eq {α : Type u} (a : α) :
    T.twice a = .node a (.node (.twice a) (.cons (.node (.twice a) .nil) .nil)) := by
  conv_lhs => rw [← T.ctor_dtor (T.twice a), T.twice, T.dtor_corec]
  simp [T.twice]

/-! A `datatype` run outside a block: its recursor's hypothesis through the block is by membership
in its closed types. -/

mixed_mutual
datatype D (α : Type u)
  | leaf (a : α)
  | node (s : S α)
codatatype S (α : Type u)
  | cons (d : D α) (s : S α) (o : O α)
codatatype O (α : Type u)
  | none
  | some (d : D α)
end

/--
info: @D.rec : {α : Type u_2} →
  {motive : D α → Sort u_1} →
    ((a : α) → motive (D.leaf a)) →
      ((s : S α) → ((t : D α) → t ∈ s → motive t) → motive (D.node s)) → (t : D α) → motive t
-/
#guard_msgs in #check @D.rec
/--
info: @S.mem_cons : ∀ {α : Type u_1} (d : D α) (s : S α) (o : O α) (x : D α), x ∈ S.cons d s o ↔ x = d ∨ x ∈ s ∨ x ∈ o
-/
#guard_msgs in #check @S.mem_cons

/-! ### A constructor name that two types of the inner block share

The closed layers per type have the constructors of the types (`EvenL.F.succ`), restated from the
open ones (`EvenL.Open.F.succ`), for dot notation and patterns. -/

mixed_mutual
codatatype U
  | mk (e : EvenL) (u : U)
datatype EvenL
  | zero
  | succ (o : OddL)
datatype OddL
  | succ (e : EvenL)
end

/-- info: @EvenL.F.succ : {S₁ S₂ : Type u_1} → S₂ → EvenL.F S₁ S₂ -/
#guard_msgs in #check @EvenL.F.succ

def EvenL.toNat (e : EvenL) : Nat :=
  EvenL.fold (S₁ := Nat) (S₂ := Nat) (fun | .zero => 0 | .succ k => k + 1)
    (fun | .succ k => k + 1) e

example : (EvenL.succ (.succ .zero)).toNat = 2 := by
  simp [EvenL.toNat]

def EvenL.isZero (e : EvenL) : Bool :=
  match e.dtor with
  | .zero => true
  | .succ _ => false

example : (EvenL.succ (.succ .zero)).isZero = false := by
  simp [EvenL.isZero]

/-- info: EvenL.dtor_succ : ∀ (o : OddL), (EvenL.succ o).dtor = EvenL.F.succ o -/
#guard_msgs in #check @EvenL.dtor_succ

end

end MixedBlockTest
