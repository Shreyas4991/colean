import Mathlib.Tactic.Conv
import Colean.CodataCmd

/-! Conatural numbers: case analysis with the generated eliminator, and the simp lemmas. -/

namespace CodataTest

noncomputable section

codata CoNat
  | zero
  | succ (n : CoNat)

def CoNat.top : CoNat :=
  CoNat.corec (fun _ => .succ ()) ()

theorem top_unfold : CoNat.top = .succ CoNat.top := by
  rw [CoNat.top]
  conv_lhs => rw [CoNat.corec_eq]
  rfl

def CoNat.ofNat (n : Nat) : CoNat :=
  match n with
  | .zero => .zero
  | .succ n => .succ (.ofNat n)

theorem CoNat.top_or_ofNat (n : CoNat) : n = .top ∨ ∃ m, n = .ofNat m := by
  suffices (∀ m, n ≠ .ofNat m) → n = .top by grind
  intro h
  apply CoNat.bisim (fun lhs rhs => (∀ m, lhs ≠ .ofNat m) ∧ rhs = .top)
  · rintro n _ ⟨h, rfl⟩
    conv => arg 3; rw [top_unfold]; simp
    cases n with
    | zero => exact absurd rfl (h 0)
    | succ k =>
      simp only [dtor_succ]
      exact .succ k top ⟨fun m hm => h (m + 1) (by subst hm; rfl), rfl⟩
  · grind

/-- The generated simp lemmas: `ctor` on constructor shapes, injectivity, disjointness. -/
example (n : CoNat) : CoNat.ctor (.succ n) = .succ n := by simp
example : CoNat.ctor .zero = .zero := by simp
example (n m : CoNat) : CoNat.succ n = CoNat.succ m ↔ n = m := by simp
example (n : CoNat) : CoNat.zero ≠ CoNat.succ n := by simp

/-- Case analysis with data: the predecessor. -/
def CoNat.pred (n : CoNat) : CoNat :=
  CoNat.casesOn n CoNat.zero fun k => k

example (k : CoNat) : CoNat.pred (.succ k) = k := by simp [CoNat.pred]
example : CoNat.pred .zero = .zero := by simp [CoNat.pred]

end

end CodataTest
