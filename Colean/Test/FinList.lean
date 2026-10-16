import Mathlib.Logic.Equiv.Defs
import Colean.DataCmd

/-! # Test: `data`, a plain inductive type -/

universe u

namespace DataTest

noncomputable section

data FinList (α : Type u)
  | nil
  | cons (a : α) (l : FinList α)

#check @FinList.cons
#check @FinList.fold
#check @FinList.fold_ctor
#check @FinList.rec
#check @FinList.rec_cons
#check @FinList.casesOn
#check @FinList.contract

/-- To a native list, by the fold. -/
def FinList.toList {α : Type u} (l : FinList α) : List α :=
  FinList.fold (S := List α) (fun | .nil => [] | .cons a l => a :: l) l

@[simp] theorem FinList.toList_nil {α : Type u} : (FinList.nil : FinList α).toList = [] := by
  simp [FinList.toList]

@[simp] theorem FinList.toList_cons {α : Type u} (a : α) (l : FinList α) :
    (FinList.cons a l).toList = a :: l.toList := by
  simp [FinList.toList]

/-- From a native list, by structural recursion. -/
def FinList.ofList {α : Type u} : List α → FinList α
  | [] => .nil
  | a :: l => .cons a (ofList l)

theorem FinList.toList_ofList {α : Type u} (l : List α) : (FinList.ofList l).toList = l := by
  induction l with
  | nil => simp [FinList.ofList]
  | cons a l ih => simp [FinList.ofList, ih]

/-- The other direction, by induction on the `data` type: `FinList.rec` is the eliminator. -/
theorem FinList.ofList_toList {α : Type u} (l : FinList α) : FinList.ofList l.toList = l := by
  induction l with
  | nil => simp [FinList.ofList]
  | cons a l ih => simp [FinList.ofList, ih]

/-- `FinList α ≃ List α`. -/
def FinList.equivList {α : Type u} : FinList α ≃ List α :=
  ⟨FinList.toList, FinList.ofList, FinList.ofList_toList, FinList.toList_ofList⟩

/-- Case analysis, and the injectivity and disjointness lemmas. -/
example {α : Type u} (l : FinList α) : l = .nil ∨ ∃ a l', l = .cons a l' := by
  cases l with
  | nil => exact Or.inl rfl
  | cons a l => exact Or.inr ⟨a, l, rfl⟩

example {α : Type u} (a b : α) (l m : FinList α) (h : FinList.cons a l = FinList.cons b m) :
    a = b ∧ l = m := by
  simpa using h

example {α : Type u} (a : α) (l : FinList α) : FinList.cons a l ≠ FinList.nil := by simp

/-- Uniqueness of the fold: any function satisfying the equations is the fold. -/
example {α : Type u} : FinList.toList (α := α) = FinList.fold (fun | .nil => [] | .cons a l => a :: l) :=
  funext fun l => FinList.fold_unique _ FinList.toList (fun | .nil => by simp | .cons a l => by simp) l

/-- Length, by the fold, and the specification by `fold_eq`. -/
def FinList.length {α : Type u} (l : FinList α) : Nat :=
  FinList.fold (S := Nat) (fun | .nil => 0 | .cons _ n => n + 1) l

theorem FinList.length_toList {α : Type u} (l : FinList α) : l.toList.length = l.length := by
  induction l with
  | nil => simp [FinList.length]
  | cons a l ih => simp [FinList.length, ih]

end

end DataTest
