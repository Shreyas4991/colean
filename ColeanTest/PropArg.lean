import Colean.DataCmd

/-! # Test: proof arguments

As in `T.F.c.injEq`, injectivity leaves the proof arguments out of the conjunction, and there
is no injectivity lemma when nothing is left. -/

namespace PropArgTest

codata P (p : Prop)
  | mk (n : Nat) (h : p) (s : P p)

example {p : Prop} (n n' : Nat) (h h' : p) (s s' : P p) :
    P.mk n h s = P.mk n' h' s' ↔ n = n' ∧ s = s' :=
  P.mk_inj n h s n' h' s'

data Q
  | mk (n : Nat) (h : True)

example (n n' : Nat) (h h' : True) : Q.mk n h = Q.mk n' h' ↔ n = n' := Q.mk_inj n h n' h'

data R
  | mk (h : True)
  | nil

/-- error: Unknown constant `PropArgTest.R.mk_inj` -/
#guard_msgs in
#check @R.mk_inj

example (h : True) : R.mk h ≠ R.nil := R.mk_ne_nil h

end PropArgTest
