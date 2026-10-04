import Mathlib.Tactic

theorem sumProductPair
    (a b c d : ℤ)
    (hsum : a + b = c + d)
    (hprod : a * b = c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have key : (a - c) * (a - d) = 0 := by linear_combination a * hsum - hprod
  rcases mul_eq_zero.mp key with h | h
  · left; exact ⟨by linarith, by linarith⟩
  · right; exact ⟨by linarith, by linarith⟩
