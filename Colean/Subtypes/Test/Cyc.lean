import Colean.Subtypes.CodataCmd

/-! # Test: two indices, the second depending on the first

`Cyc n i` is an infinite walk on the cycle `Fin (n + 1)`, at position `i`. -/

namespace CodataTest

noncomputable section

codata Cyc : (n : Nat) → Fin (n + 1) → Type
  | next {n : Nat} {i : Fin (n + 1)} (c : Cyc n (i + 1)) : Cyc n i
  | prev {n : Nat} {i : Fin (n + 1)} (c : Cyc n (i - 1)) : Cyc n i

#check Cyc
#check @Cyc.next
#check @Cyc.dtor
#check @Cyc.corec
#check @Cyc.bisim
#check @Cyc.casesOn
#check Cyc.Ix

/-- Always forward. -/
def Cyc.forward (n : Nat) (i : Fin (n + 1)) : Cyc n i :=
  Cyc.corec (S := fun _ _ => Unit) (fun _ _ _ => .next ()) ()

@[simp] theorem Cyc.dtor_forward (n : Nat) (i : Fin (n + 1)) :
    (Cyc.forward n i).dtor = .next (Cyc.forward n (i + 1)) := by
  simp [Cyc.forward, Cyc.dtor_corec]

/-- The position after `k` steps. -/
def Cyc.position {n : Nat} {i : Fin (n + 1)} (c : Cyc n i) : Nat → Fin (n + 1)
  | 0 => i
  | k + 1 =>
    match c.dtor with
    | .next c => c.position k
    | .prev c => c.position k

theorem Cyc.position_forward_two (n : Nat) (i : Fin (n + 1)) :
    (Cyc.forward n i).position 2 = i + 1 + 1 := by
  simp [Cyc.position]

/-- Case analysis over both indices. -/
example {n : Nat} {i : Fin (n + 1)} (c : Cyc n i) : c.position 1 = i + 1 ∨ c.position 1 = i - 1 := by
  cases c with
  | next c => left; simp [Cyc.position]
  | prev c => right; simp [Cyc.position]

/-- Two forward walks from the same position are equal, by bisimulation over the family. -/
example (n : Nat) (i : Fin (n + 1)) :
    Cyc.forward n i = Cyc.corec (S := fun _ _ => Unit) (fun _ _ _ => .next ()) () := by
  refine Cyc.bisim (fun n i x y => x = Cyc.forward n i ∧
    y = Cyc.corec (S := fun _ _ => Unit) (fun _ _ _ => .next ()) ()) ?_ ⟨rfl, rfl⟩
  rintro n i x y ⟨rfl, rfl⟩
  simp [Cyc.dtor_corec]
  exact .next _ _ ⟨rfl, rfl⟩

end

end CodataTest
