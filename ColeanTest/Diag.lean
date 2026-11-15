import Colean.CodataCmd

/-! # Test: constructors whose indices are bare binders

`step {n} … : Diag n n` repeats a binder in the result index, and `stop {n m} : Diag n m` has no
field at all. Both exercise the pattern-variable bookkeeping of the generated `match`es: the
index binders are explicit discriminants, named at a binder's first occurrence only. -/

namespace CodataTest

noncomputable section

codatatype Diag : Nat → Nat → Type
  | step {n : Nat} (d : Diag (n + 1) (n + 1)) : Diag n n
  | stop {n m : Nat} : Diag n m

#check @Diag.step
#check @Diag.stop
#check @Diag.casesOn

example {n m : Nat} (x : Diag.F (Diag) n m) : Diag.F.fmap (fun _ _ t => t) x = x :=
  Diag.F.fmap_id x

/-- Off the diagonal, only `stop` is possible. -/
example (d : Diag 2 3) : d = Diag.stop := by
  cases d with
  | stop => rfl

/-- The infinite climb along the diagonal: the state carries the proof of being on it. -/
def Diag.climb (n : Nat) : Diag n n :=
  Diag.corec (S := fun j₁ j₂ => PLift (j₁ = j₂))
    (fun _ j₂ h => match j₂, h.down with | _, rfl => .step ⟨rfl⟩) ⟨rfl⟩

theorem Diag.dtor_climb (n : Nat) : (Diag.climb n).dtor = .step (Diag.climb (n + 1)) :=
  Diag.dtor_corec _ _

theorem Diag.climb_eq (n : Nat) : Diag.climb n = Diag.step (Diag.climb (n + 1)) := by
  rw [← Diag.ctor_dtor (Diag.climb n), Diag.dtor_climb, Diag.ctor_step]

end

end CodataTest
