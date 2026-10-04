import Colean.Subtypes.DataCmd

/-! # Test: `data`, an indexed family -/

universe u

namespace DataTest

noncomputable section

data FinVec (α : Type u) : Nat → Type u
  | nil : FinVec α 0
  | cons {n : Nat} (a : α) (v : FinVec α n) : FinVec α (n + 1)

#check @FinVec.cons
#check @FinVec.fold
#check @FinVec.rec
#check @FinVec.rec_cons
#check @FinVec.casesOn

/-- The elements, by the fold into a constant family. -/
def FinVec.toList {α : Type u} {n : Nat} (v : FinVec α n) : List α :=
  FinVec.fold (S := fun _ => List α) (fun _ y => match y with | .nil => [] | .cons a l => a :: l) v

@[simp] theorem FinVec.toList_nil {α : Type u} : (FinVec.nil : FinVec α 0).toList = [] := by
  simp [FinVec.toList]

@[simp] theorem FinVec.toList_cons {α : Type u} {n : Nat} (a : α) (v : FinVec α n) :
    (FinVec.cons a v).toList = a :: v.toList := by
  simp [FinVec.toList]

/-- The index is the length: induction over the family. -/
theorem FinVec.length_toList {α : Type u} {n : Nat} (v : FinVec α n) : v.toList.length = n := by
  induction v with
  | nil => simp
  | cons a v ih => simp [ih]

def FinVec.ofList {α : Type u} : (l : List α) → FinVec α l.length
  | [] => .nil
  | a :: l => .cons a (ofList l)

theorem FinVec.toList_ofList {α : Type u} (l : List α) : (FinVec.ofList l).toList = l := by
  induction l with
  | nil => simp [FinVec.ofList]
  | cons a l ih => simp [FinVec.ofList, ih]

/-- The head, by case analysis: the index rules out `nil`. -/
def FinVec.head {α : Type u} {n : Nat} (v : FinVec α (n + 1)) : α :=
  FinVec.casesOn (motive := fun m _ => m = n + 1 → α) v (fun h => nomatch h) (fun a _ _ => a) rfl

@[simp] theorem FinVec.head_cons {α : Type u} {n : Nat} (a : α) (v : FinVec α n) :
    (FinVec.cons a v).head = a := by
  simp [FinVec.head]

/-- A vector of length zero is `nil`. -/
example {α : Type u} (v : FinVec α 0) : v = FinVec.nil := by
  cases v with
  | nil => rfl

end

end DataTest
