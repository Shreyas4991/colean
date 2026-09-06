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

/-- Closure of a relation `R` under `add`-congruence. This is the family of contexts we allow
around recursive occurrences when doing coinduction for `mul`. -/
inductive AddCongr (R : Seq ℕ → Seq ℕ → Prop) : Seq ℕ → Seq ℕ → Prop
  | base {a b} : R a b → AddCongr R a b
  | add {a b c d} : AddCongr R a c → AddCongr R b d → AddCongr R (add a b) (add c d)

/-- **Coinduction up to `add`.** To prove `s₁ = s₂` it suffices to exhibit a relation whose
one-step unfolding lands in the `add`-congruence closure `AddCongr R` (rather than in `R` itself).
This lets recursive occurrences appear under `add`, as they do in `mul`.

Soundness sketch (to be discharged): `AddCongr R` is itself an ordinary `Seq.IsBisimulation`, so the
result follows from `Seq.eq_of_bisim (AddCongr R)`. One shows `IsBisimulation (AddCongr R)` by
induction on `AddCongr`: the `base` case is `H`; the `add` case unfolds both sides with
`destruct_add` and combines the two `BisimO` hypotheses (a `some`/`some` pair on each recursive
component yields a `some`/`some` pair whose tail is again an `AddCongr.add`). -/
theorem eq_of_bisim_upto_add (R : Seq ℕ → Seq ℕ → Prop)
    (H : ∀ s1 s2, R s1 s2 → Seq.BisimO (AddCongr R) s1.destruct s2.destruct)
    {s1 s2 : Seq ℕ} (h : R s1 s2) : s1 = s2 := by
  -- The `add`-congruence closure is itself an ordinary bisimulation.
  apply Seq.eq_of_bisim (AddCongr R) _ (AddCongr.base h)
  intro x y hxy
  induction hxy with
  | base hab => exact H _ _ hab
  | @add a b c d _ _ ihac ihbd =>
    rw [destruct_add, destruct_add]
    cases ha : a.destruct with
    | none =>
      cases hc : c.destruct with
      | none => simp [Seq.BisimO]
      | some pc => rw [ha, hc] at ihac; simp [Seq.BisimO] at ihac
    | some pa =>
      cases hc : c.destruct with
      | none => rw [ha, hc] at ihac; simp [Seq.BisimO] at ihac
      | some pc =>
        obtain ⟨h1, ta⟩ := pa
        obtain ⟨h1', tc⟩ := pc
        rw [ha, hc] at ihac
        obtain ⟨rfl, htac⟩ := ihac
        cases hb : b.destruct with
        | none =>
          cases hd : d.destruct with
          | none => simp [Seq.BisimO]
          | some pd => rw [hb, hd] at ihbd; simp [Seq.BisimO] at ihbd
        | some pb =>
          cases hd : d.destruct with
          | none => rw [hb, hd] at ihbd; simp [Seq.BisimO] at ihbd
          | some pd =>
            obtain ⟨h2, tb⟩ := pb
            obtain ⟨h2', td⟩ := pd
            rw [hb, hd] at ihbd
            obtain ⟨rfl, htbd⟩ := ihbd
            simp only [Seq.BisimO]
            exact ⟨trivial, AddCongr.add htac htbd⟩

/-- One-step unfolding of `mul` at the level of `destruct`. -/
theorem destruct_mul (s1 s2 : Seq ℕ) :
    (mul s1 s2).destruct =
      match s1.destruct, s2.destruct with
      | some (h1, t1), some (h2, t2) => some (h1 * h2, add (mul s1 t2) (mul t1 s2))
      | _, _ => none := by
  rw [mul]
  cases s1.destruct with
  | none => simp
  | some p =>
    obtain ⟨h1, t1⟩ := p
    cases s2.destruct with
    | none => simp
    | some q => obtain ⟨h2, t2⟩ := q; simp

/-- `mul` is commutative, proved coinductively with the up-to-`add` principle. The one-step tails
`add (mul s bs) (mul as t)` vs `add (mul t as) (mul bs s)` land in the `add`-congruence closure of
the relation after a single rewrite by `add_comm_seq`. -/
theorem mul_comm_seq (xs ys : Seq ℕ) : mul xs ys = mul ys xs := by
  refine eq_of_bisim_upto_add (fun a b => ∃ p q, a = mul p q ∧ b = mul q p) ?_ ⟨xs, ys, rfl, rfl⟩
  rintro s1 s2 ⟨p, q, rfl, rfl⟩
  rw [destruct_mul, destruct_mul]
  cases hp : p.destruct with
  | none => cases hq : q.destruct with | none => simp [Seq.BisimO] | some => simp [Seq.BisimO]
  | some pp =>
    cases hq : q.destruct with
    | none => simp [Seq.BisimO]
    | some qq =>
      obtain ⟨a, pa⟩ := pp
      obtain ⟨b, qb⟩ := qq
      simp only [Seq.BisimO]
      refine ⟨Nat.mul_comm a b, ?_⟩
      rw [add_comm_seq (mul q pa) (mul qb p)]
      exact AddCongr.add (AddCongr.base ⟨p, qb, rfl, rfl⟩) (AddCongr.base ⟨pa, q, rfl, rfl⟩)
