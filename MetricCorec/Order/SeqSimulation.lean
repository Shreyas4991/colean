import MetricCorec.Order.SeqAddMul

/-!
## The order side: monotonicity is the *same* coinduction, for `⊑` instead of `=`

`add`'s single defining equation `destruct_add` is the only primitive about `add` used above.
The reasoning principle for `=` (`eq_of_bisim_upto_add`) came from feeding it through
`Seq.eq_of_bisim`. The prefix order `⊑` has its *own* coinduction principle — a **simulation**, the
one-sided version of a bisimulation — and feeding the same `destruct_add` through *that* re-derives
the monotonicity `add_mono` needed for the `partial_fixpoint` definition. Same primitive, two
coinductions, two orders (`=` vs `⊑`).
-/

open Stream' Stream'.Seq
open scoped Lean.Order

/-- **Coinduction for the prefix order `⊑`.** A simulation is contained in `⊑`. This is the
one-sided (order) analogue of `Seq.eq_of_bisim`, proved by induction on the position `n`. -/
theorem le_of_simulation (R : Seq ℕ → Seq ℕ → Prop)
    (H : ∀ s1 s2, R s1 s2 →
      s1.destruct = none ∨
        ∃ a t1 t2, s1.destruct = some (a, t1) ∧ s2.destruct = some (a, t2) ∧ R t1 t2)
    {s1 s2 : Seq ℕ} (h : R s1 s2) : s1 ⊑ s2 := by
  rw [rel_iff]
  suffices H2 : ∀ n s1 s2, R s1 s2 → ∀ a, s1.get? n = some a → s2.get? n = some a from
    fun n a => H2 n s1 s2 h a
  intro n
  induction n with
  | zero =>
    intro s1 s2 h a ha
    rcases H s1 s2 h with hnil | ⟨v, t1, t2, h1, h2, _⟩
    · rw [destruct_eq_none hnil] at ha; simp at ha
    · rw [destruct_eq_cons h1] at ha; rw [destruct_eq_cons h2]; simp_all
  | succ n ih =>
    intro s1 s2 h a ha
    rcases H s1 s2 h with hnil | ⟨v, t1, t2, h1, h2, hr⟩
    · rw [destruct_eq_none hnil] at ha; simp at ha
    · rw [destruct_eq_cons h1, get?_cons_succ] at ha
      rw [destruct_eq_cons h2, get?_cons_succ]
      exact ih t1 t2 hr a ha

/-- One-step unfolding of `⊑` (the "simulation" shape): the order analogue of reading off
`BisimO` from a related pair. -/
theorem le_destruct {a c : Seq ℕ} (h : a ⊑ c) :
    a.destruct = none ∨
      ∃ v ta tc, a.destruct = some (v, ta) ∧ c.destruct = some (v, tc) ∧ ta ⊑ tc := by
  cases ha : a.destruct with
  | none => exact Or.inl rfl
  | some pa =>
    obtain ⟨v, ta⟩ := pa
    have hav : a.get? 0 = some v := by rw [destruct_eq_cons ha]; simp
    have hcv : c.get? 0 = some v := (rel_iff.mp h) 0 v hav
    cases hc : c.destruct with
    | none => rw [destruct_eq_none hc] at hcv; simp at hcv
    | some pc =>
      obtain ⟨w, tc⟩ := pc
      have hcw : c.get? 0 = some w := by rw [destruct_eq_cons hc]; simp
      rw [hcv] at hcw
      obtain rfl := Option.some_inj.mp hcw
      refine Or.inr ⟨v, ta, tc, rfl, rfl, ?_⟩
      rw [rel_iff]
      intro n u hu
      have hu' : a.get? (n + 1) = some u := by rw [destruct_eq_cons ha, get?_cons_succ]; exact hu
      have hcu : c.get? (n + 1) = some u := (rel_iff.mp h) (n + 1) u hu'
      rwa [destruct_eq_cons hc, get?_cons_succ] at hcu

/-- Monotonicity of `add` in the prefix order, re-derived from `destruct_add` alone via the order
coinduction `le_of_simulation` — the exact analogue of the `=`-side `eq_of_bisim_upto_add`. -/
theorem prefix_add_mono {a c b d : Seq ℕ} (hac : a ⊑ c) (hbd : b ⊑ d) : add a b ⊑ add c d := by
  refine le_of_simulation
    (fun x y => ∃ a b c d, x = add a b ∧ y = add c d ∧ a ⊑ c ∧ b ⊑ d) ?_
    ⟨a, b, c, d, rfl, rfl, hac, hbd⟩
  rintro x y ⟨a, b, c, d, rfl, rfl, hac, hbd⟩
  rw [destruct_add, destruct_add]
  rcases le_destruct hac with ha | ⟨va, ta, tc, ha, hc, htac⟩
  · left; simp [ha]
  · rcases le_destruct hbd with hb | ⟨vb, tb, td, hb, hd, htbd⟩
    · left; simp [ha, hb]
    · right
      refine ⟨va + vb, add ta tb, add tc td, ?_, ?_, ⟨ta, tb, tc, td, rfl, rfl, htac, htbd⟩⟩
      · simp [ha, hb]
      · simp [hc, hd]
