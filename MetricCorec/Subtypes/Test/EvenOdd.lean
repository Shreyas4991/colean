import MetricCorec.Subtypes.MutualCmd

/-! # Test: a mutual indexed `data` block with a constructor name shared by both types -/

namespace DataTest

noncomputable section

mutual
data Even : Nat → Type
  | zero : Even 0
  | succ {n : Nat} (o : Odd n) : Even (n + 1)
data Odd : Nat → Type
  | succ {n : Nat} (e : Even n) : Odd (n + 1)
end

-- The block-level constructors are qualified; the types keep the plain names.
#check @Even_Odd.F.Even_succ
#check @Even_Odd.F.Odd_succ
#check @Even.succ
#check @Odd.succ
#check @Even.casesOn
#check @Odd.casesOn
#check @Even_Odd.rec

/-- Parity, by induction over the block. -/
def Par : ∀ m (n : Nat), Even_Odd m n → Prop
  | .Even, n, _ => n % 2 = 0
  | .Odd, n, _ => n % 2 = 1

theorem par (m : Even_Odd.Which) (n : Nat) (x : Even_Odd m n) : Par m n x := by
  induction x with
  | zero => simp [Par]
  | Even_succ o ih => simp [Par] at *; omega
  | Odd_succ e ih => simp [Par] at *; omega

theorem Even.even {n : Nat} (e : Even n) : n % 2 = 0 := par .Even n e
theorem Odd.odd {n : Nat} (o : Odd n) : n % 2 = 1 := par .Odd n o

/-- Case analysis refines the index: there is no odd zero, and an even zero is `zero`. -/
example (o : Odd 0) : False := by cases o
example (e : Even 0) : e = Even.zero := by
  cases e with
  | zero => rfl

/-- To the naturals and back. -/
def Even.ofNat : ∀ n, Even (2 * n)
  | 0 => .zero
  | n + 1 => .succ (.succ (Even.ofNat n))

example : (Even.ofNat 2).even = rfl := rfl

end

end DataTest
