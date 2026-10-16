import Colean.DataCmd

/-! # Test: `data` with two indices, bare and repeated (`Le n n`), and proofs by induction -/

namespace DataTest

noncomputable section

-- `Nat.le` as a `Type`-valued family: the classic inductive family with two indices.
data Le : Nat → Nat → Type
  | refl {n : Nat} : Le n n
  | step {n m : Nat} (h : Le n m) : Le n (m + 1)

#check @Le.refl
#check @Le.step
#check @Le.rec
#check @Le.casesOn
#check @Le.fold

/-- Soundness: induction with a `Prop` motive over both indices. -/
theorem Le.toLe {n m : Nat} (h : Le n m) : n ≤ m := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h ih => exact Nat.le_succ_of_le ih

def Le.ofAdd (n : Nat) : ∀ k, Le n (n + k)
  | 0 => .refl
  | k + 1 => .step (ofAdd n k)

/-- Completeness. -/
def Le.ofLe {n m : Nat} (h : n ≤ m) : Le n m :=
  (congrArg (Le n) (Nat.exists_eq_add_of_le h).choose_spec).mpr (Le.ofAdd n _)

/-- Height, by the fold. -/
def Le.height {n m : Nat} (h : Le n m) : Nat :=
  Le.fold (S := fun _ _ => Nat) (fun _ _ y => match y with | .refl => 0 | .step k => k + 1) h

@[simp] theorem Le.height_refl {n : Nat} : (Le.refl : Le n n).height = 0 := by simp [Le.height]

@[simp] theorem Le.height_step {n m : Nat} (h : Le n m) : (Le.step h).height = h.height + 1 := by
  simp [Le.height]

theorem Le.height_eq {n m : Nat} (h : Le n m) : h.height = m - n := by
  induction h with
  | refl => simp
  | step h ih => have := h.toLe; simp [ih]; omega

/-- Case analysis refines both indices. -/
example (n : Nat) (h : Le n n) : h = Le.refl := by
  cases h with
  | refl => rfl
  | step h => exact absurd h.toLe (by omega)

end

end DataTest
