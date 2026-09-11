import MetricCorec.Order.SeqAddMul

/-!
## Towards `mul xs ys = mul ys xs`: a coinduction principle up to `add`

The natural bisimulation `R s₁ s₂ := ∃ p q, s₁ = mul p q ∧ s₂ = mul q p` is **not** a bisimulation
in the sense of `Seq.eq_of_bisim`. Unfolding one step at `xs = cons a as`, `ys = cons b bs`:

```
mul xs ys = cons (a*b) (add (mul xs bs) (mul as ys))
mul ys xs = cons (b*a) (add (mul ys as) (mul bs xs))
```

The heads agree (`Nat.mul_comm`), but the tails are `add`s of recursive occurrences, **not** bare
`mul`s — so they are not directly related by `R`. `Seq.eq_of_bisim` requires the tail to lie in `R`
itself, which fails here. We need to allow the recursive occurrences to sit under `add`.

The fix is a *bisimulation up to `add`-congruence*: the one-step tails need only lie in the closure
of `R` under `add`, not in `R`. For `mul` this closes the loop, because the two tails above are
`add`-congruent after one rewrite by `add_comm_seq`:
`add (mul ys as) (mul bs xs) = add (mul bs xs) (mul ys as)`, and then `mul xs bs `/`mul bs xs` and
`mul as ys`/`mul ys as` are pairwise `R`-related.
-/

open Stream' Stream'.Seq

/-- One-step unfolding of `mul` at the level of `destruct`. -/
theorem destruct_mul (s1 s2 : Seq ℕ) :
    (mul s1 s2).destruct =
      match s1.destruct, s2.destruct with
      | some (h1, t1), some (h2, t2) => some (h1 * h2, add (mul s1 t2) (mul t1 s2))
      | _, _ => none := by
  rw [mul]
  cases s1 with
  | nil => simp
  | cons h1 t1 => cases s2 <;> simp

/-- Equality of a function at two fixed argument pairs is admissible: it is the conjunction of the
two inequalities, each of which is `admissible_apply₂_rel`. -/
theorem Lean.Order.admissible_apply₂_eq {α : Sort u} {β : Sort v} {γ : Sort w}
    [Lean.Order.CCPO γ] (a a' : α) (b b' : β) :
    Lean.Order.admissible (fun f : α → β → γ => f a b = f a' b') :=
  fun c hc h => Lean.Order.PartialOrder.rel_antisymm
    (Lean.Order.admissible_apply₂_rel a a' b b' c hc fun f hf =>
      Lean.Order.PartialOrder.rel_of_eq (h f hf))
    (Lean.Order.admissible_apply₂_rel a' a b' b c hc fun f hf =>
      Lean.Order.PartialOrder.rel_of_eq (h f hf).symm)

/-- `mul` is commutative, by fixpoint induction on `mul` itself. No coinduction up to `add` is
needed: the induction hypothesis speaks about the previous approximant at *all* argument pairs, so
the recursive occurrences sitting under `add` are handled by it directly, and the two tails are then
identified by `add_comm_seq`. -/
theorem mul_comm_seq (xs ys : Seq ℕ) : mul xs ys = mul ys xs := by
  revert xs ys
  apply mul.fixpoint_induct (motive := fun m => ∀ xs ys : Seq ℕ, m xs ys = m ys xs)
  · apply Lean.Order.admissible_pi; intro xs
    apply Lean.Order.admissible_pi; intro ys
    exact Lean.Order.admissible_apply₂_eq xs ys ys xs
  · intro m ih xs ys
    cases xs with
    | nil => cases ys <;> simp
    | cons a as =>
      cases ys with
      | nil => simp
      | cons b bs =>
        simp
        congr 1
        · grind
        grind [add_comm_seq]
