import Colean.CodataCmd

/-! # Test: a proposition as an index

`Bounded n h` is an infinite walk that never goes above `10`; the proof `h : n ≤ 10` is the
second index. The two indices are packed into `(n : Nat) ×' n ≤ 10`, which is why the packing is
a `PSigma`. -/

namespace CodataTest

noncomputable section

codata Bounded : (n : Nat) → n ≤ 10 → Type
  | step {n : Nat} {h : n + 1 ≤ 10} (s : Bounded (n + 1) h) : Bounded n (Nat.le_of_succ_le h)
  | stay {n : Nat} {h : n ≤ 10} (s : Bounded n h) : Bounded n h

#check Bounded
#check @Bounded.step
#check @Bounded.corec
#check Bounded.Ix

/-- Climb while possible, then stay. The result index is a proof, so proof irrelevance
matches `Nat.le_of_succ_le hn` with the given `h`. -/
def Bounded.climb (n : Nat) (h : n ≤ 10) : Bounded n h :=
  Bounded.corec (S := fun _ _ => Unit)
    (fun n _ _ => if hn : n + 1 ≤ 10 then .step (h := hn) () else .stay ()) ()

@[simp] theorem Bounded.dtor_climb_of_lt (n : Nat) (h : n ≤ 10) (hn : n + 1 ≤ 10) :
    (Bounded.climb n h).dtor = .step (h := hn) (Bounded.climb (n + 1) hn) := by
  simp only [Bounded.climb, Bounded.dtor_corec, dite_eq_left hn, Bounded.F.map_step]

@[simp] theorem Bounded.dtor_climb_of_eq (h : 10 ≤ 10) :
    (Bounded.climb 10 h).dtor = .stay (Bounded.climb 10 h) := by
  simp only [Bounded.climb, Bounded.dtor_corec, dite_eq_right (by omega : ¬ 10 + 1 ≤ 10),
    Bounded.F.map_stay]

/-- At the top, the only possible step is `stay`: case analysis with the index `10`. -/
example (h : 10 ≤ 10) (w : Bounded 10 h) : ∃ w', w = Bounded.stay w' := by
  cases w with
  | step s => exact absurd ‹10 + 1 ≤ 10› (by omega)
  | stay s => exact ⟨s, rfl⟩

end

end CodataTest
