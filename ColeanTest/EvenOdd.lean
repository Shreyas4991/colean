import Colean.MutualCmd

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
def Par : ∀ i, Even_Odd i → Prop
  | .Even n, _ => n % 2 = 0
  | .Odd n, _ => n % 2 = 1

theorem par (i : Even_Odd.Ix) (x : Even_Odd i) : Par i x := by
  induction x with
  | zero => simp [Par]
  | Even_succ o ih => simp [Par] at *; omega
  | Odd_succ e ih => simp [Par] at *; omega

theorem Even.even {n : Nat} (e : Even n) : n % 2 = 0 := par (.Even n) e
theorem Odd.odd {n : Nat} (o : Odd n) : n % 2 = 1 := par (.Odd n) o

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

/-! The recursors per type, in the shape of Lean's mutual inductives: a motive per type, the
minor premises of the block with their block-level names, the type's own indices. -/

#check @Even.rec
#check @Odd.rec
#check @Even.rec_succ
#check @Odd.rec_succ
#check @Even_Odd.rec_Even_succ

/-- Parity again, by induction per type: the motive of `Odd` is given, that of `Even` comes from
the goal. -/
theorem Even.even' {n : Nat} (e : Even n) : n % 2 = 0 := by
  induction e using Even.rec (motive_2 := fun n _ => n % 2 = 1) with
  | zero => rfl
  | Even_succ o ih => omega
  | Odd_succ e ih => omega

/-- A function by the recursor of `Even`, computed by the rules per type. -/
def Even.toNat {n : Nat} (e : Even n) : Nat :=
  Even.rec (motive_2 := fun _ _ => Nat) 0 (fun _ k => k + 1) (fun _ k => k + 1) e

example : (Even.succ (Odd.succ Even.zero)).toNat = 2 := by
  simp [Even.toNat]

example {n : Nat} (o : Odd n) : (Even.succ o).toNat =
    Odd.rec (motive_1 := fun _ _ => Nat) 0 (fun _ k => k + 1) (fun _ k => k + 1) o + 1 := by
  rw [Even.toNat, Even.rec_succ]

end

end DataTest
