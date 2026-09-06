import MetricCorec.Order.SeqAddMul

/-!
# Further `partial_fixpoint` examples on `Seq ℕ`

Definitions whose recursive occurrences sit under `add`: the Fibonacci sequence in two forms, and
a filter of the naturals from a given starting point.
-/

open Stream' Stream'.Seq

def fibA : Seq ℕ :=
  .cons 0 (add (.cons 1 fibA) fibA)
partial_fixpoint

def fibB : Seq ℕ :=
  add (.cons 0 (.cons 1 fibB)) (.cons 0 fibB)
partial_fixpoint

-- example : fibA.take 8 = [0, 1, 1, 2, 3, 5, 8, 13] := by
--   sorry

-- example : fibB.take 8 = [0, 1, 1, 2, 3, 5, 8, 13] := by
--   sorry


def filter (P : ℕ → Bool) (n : ℕ) : Seq ℕ :=
  if P n then
    .cons n (filter P (n + 1))
  else
    filter P (n + 1)
partial_fixpoint
