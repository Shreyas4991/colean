import Mathlib.Logic.Equiv.Defs
import Colean.DataCmd

/-! # Test: `datatype` with no parameters, the naturals -/

namespace DataTest

noncomputable section

datatype Nat'
  | zero
  | succ (n : Nat')

#check @Nat'.fold
#check @Nat'.rec

def Nat'.toNat (n : Nat') : Nat := Nat'.fold (S := Nat) (fun | .zero => 0 | .succ k => k + 1) n

def Nat'.ofNat : Nat → Nat'
  | 0 => .zero
  | n + 1 => .succ (ofNat n)

theorem Nat'.toNat_ofNat (n : Nat) : (Nat'.ofNat n).toNat = n := by
  induction n with
  | zero => simp [Nat'.ofNat, Nat'.toNat]
  | succ n ih => simp [Nat'.ofNat, Nat'.toNat] at *; simp [ih]

theorem Nat'.ofNat_toNat (n : Nat') : Nat'.ofNat n.toNat = n := by
  induction n with
  | zero => simp [Nat'.ofNat, Nat'.toNat]
  | succ n ih => simp [Nat'.toNat] at *; simp [Nat'.ofNat, ih]

def Nat'.equivNat : Nat' ≃ Nat := ⟨Nat'.toNat, Nat'.ofNat, Nat'.ofNat_toNat, Nat'.toNat_ofNat⟩

/-- Addition, by the fold in the first argument. -/
def Nat'.add (m n : Nat') : Nat' := Nat'.fold (S := Nat') (fun | .zero => n | .succ k => .succ k) m

@[simp] theorem Nat'.zero_add (n : Nat') : Nat'.add .zero n = n := by simp [Nat'.add]

@[simp] theorem Nat'.succ_add (m n : Nat') : Nat'.add (.succ m) n = .succ (Nat'.add m n) := by
  simp [Nat'.add]

theorem Nat'.add_zero (m : Nat') : Nat'.add m .zero = m := by
  induction m with
  | zero => simp
  | succ m ih => simp [ih]

/-- Every natural is zero or a successor: `casesOn`, with the injectivity lemma. -/
example (n : Nat') (h : n ≠ .zero) : ∃ k, n = .succ k := by
  cases n with
  | zero => exact absurd rfl h
  | succ k => exact ⟨k, rfl⟩

example (m n : Nat') (h : Nat'.succ m = Nat'.succ n) : m = n := by simpa using h

end

end DataTest
