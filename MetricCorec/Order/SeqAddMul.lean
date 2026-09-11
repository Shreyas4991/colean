import MetricCorec.Order.SeqBindOrStop

/-!
# `add` and `mul` on `Seq ℕ` via `partial_fixpoint`

Corecursive definitions on top of the `CCPO` instance from `MetricCorec.Order.SeqCCPO`: the
examples `zeros` and `zeroOnes`, pointwise addition `add` (written with the strict case analysis
`bindOrStop` from `MetricCorec.Order.SeqBindOrStop`) together with its pointwise description,
its monotonicity (so that recursive occurrences may appear under `add`), its one-step unfolding
`destruct_add`, commutativity and the `nil` laws, and finally the product `mul`, whose recursive
occurrences sit under `add`.
-/

open Stream' Stream'.Seq
open Lean.Order

def zeros : Seq Nat :=
  cons 0 zeros
partial_fixpoint

theorem zeros_get? (n : ℕ) : zeros.get? n = some 0 := by
  induction n with
  | zero => rw [zeros]; simp
  | succ n ih => rw [zeros]; simpa using ih

def zeroOnes : Seq ℕ :=
  .cons 0 (.cons 1 zeroOnes)
partial_fixpoint

def add (s1 s2 : Seq ℕ) : Seq ℕ :=
  s1.bindOrStop fun h1 t1 =>
    s2.bindOrStop fun h2 t2 =>
      .cons (h1 + h2) (add t1 t2)
partial_fixpoint

def filter (s : Seq ℕ) (p : ℕ → Bool) : Seq ℕ :=
  s.bindOrStop fun h t =>
    if p h then
      .cons h <| filter t p
    else
      filter t p
partial_fixpoint

namespace Lean.Order

/-- In a function order, comparing the values of a function at two fixed arguments is an
admissible predicate: the two-point analogue of `admissible_apply`. -/
theorem admissible_apply_rel {α : Sort u} {γ : Sort w} [CCPO γ] (a a' : α) :
    admissible (fun f : α → γ => f a ⊑ f a') := by
  intro c hc h
  show CCPO.csup hc a ⊑ CCPO.csup hc a'
  rw [← fun_csup_eq]
  apply csup_le
  rintro _ ⟨f, hf, rfl⟩
  exact PartialOrder.rel_trans (h f hf) (le_csup _ ⟨f, hf, rfl⟩)

/-- In a function order, comparing the values of a function at two fixed argument pairs is an
admissible predicate. This is the two-point analogue of `admissible_apply`, and it is what fixpoint
induction on a monotonicity statement needs. -/
theorem admissible_apply₂_rel {α : Sort u} {β : Sort v} {γ : Sort w} [CCPO γ] (a a' : α)
    (b b' : β) : admissible (fun f : α → β → γ => f a b ⊑ f a' b') := by
  intro c hc h
  show CCPO.csup hc a b ⊑ CCPO.csup hc a' b'
  rw [← fun_csup_eq]
  show CCPO.csup (chain_apply hc a) b ⊑ CCPO.csup (chain_apply hc a') b'
  rw [← fun_csup_eq, ← fun_csup_eq]
  apply csup_le
  rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  exact PartialOrder.rel_trans (h f hf) (le_csup _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩)

end Lean.Order

/-- `add` is monotone in both arguments, by fixpoint induction on `add` itself (no `get?`): the
motive is the two-argument monotonicity statement, and the one-step unfolding preserves it because
`bindOrStop` and `cons` do. -/
theorem add_le_add_seq {s1 s2 t1 t2 : Seq ℕ} (h1 : s1 ⊑ t1) (h2 : s2 ⊑ t2) :
    add s1 s2 ⊑ add t1 t2 := by
  revert s1 s2 t1 t2
  apply add.fixpoint_induct
    (motive := fun F => ∀ s1 s2 t1 t2 : Seq ℕ, s1 ⊑ t1 → s2 ⊑ t2 → F s1 s2 ⊑ F t1 t2)
  · apply admissible_pi; intro s1
    apply admissible_pi; intro s2
    apply admissible_pi; intro t1
    apply admissible_pi; intro t2
    apply admissible_pi; intro _
    apply admissible_pi; intro _
    exact admissible_apply₂_rel s1 t1 s2 t2
  · intro F ih s1 s2 t1 t2 h1 h2
    refine bindOrStop_le_bindOrStop h1 fun a u1 v1 hu1 => ?_
    refine bindOrStop_le_bindOrStop h2 fun b u2 v2 hu2 => ?_
    exact cons_le_cons_iff.mpr ⟨rfl, ih u1 u2 v1 v2 hu1 hu2⟩

/-- `add` is monotone in both arguments, so recursive occurrences may appear under it. -/
@[partial_fixpoint_monotone]
theorem add_mono {β : Sort v} [Lean.Order.PartialOrder β] (f g : β → Seq ℕ)
    (hf : Lean.Order.monotone f) (hg : Lean.Order.monotone g) :
    Lean.Order.monotone (fun x => add (f x) (g x)) :=
  fun x y hxy => add_le_add_seq (hf x y hxy) (hg x y hxy)

/-- Monotonicity of `filter` in the sequence, by the same recipe. Productivity plays no role: the
unguarded recursive call in the `else` branch is handled by the induction hypothesis directly. -/
theorem filter_le_filter {s t : Seq ℕ} (p : ℕ → Bool) (hst : s ⊑ t) :
    filter s p ⊑ filter t p := by
  revert s t
  -- `p` is constant across the recursive calls, so `partial_fixpoint` made it a fixed parameter
  -- and the induction is over `F : Seq ℕ → Seq ℕ`.
  apply filter.fixpoint_induct (motive := fun F => ∀ s t : Seq ℕ, s ⊑ t → F s ⊑ F t)
  · apply admissible_pi; intro s
    apply admissible_pi; intro t
    apply admissible_pi; intro _
    exact admissible_apply_rel s t
  · intro F ih s t hst
    refine bindOrStop_le_bindOrStop hst fun a u v huv => ?_
    by_cases hp : p a <;> simp [hp, ih u v huv]

/-- One-step unfolding of `add` at the level of `destruct`. -/
theorem destruct_add (s1 s2 : Seq ℕ) :
    (add s1 s2).destruct =
      match s1.destruct, s2.destruct with
      | some (h1, t1), some (h2, t2) => some (h1 + h2, add t1 t2)
      | _, _ => none := by
  rw [add]
  cases s1 with
  | nil => simp
  | cons h1 t1 => cases s2 <;> simp

/-- `add` is commutative, proved by coinduction (`eq_of_bisim`). -/
theorem add_comm_seq (xs ys : Seq ℕ) : add xs ys = add ys xs := by
  apply Seq.eq_of_bisim (fun a b => ∃ xs ys, a = add xs ys ∧ b = add ys xs)
  · rintro s1 s2 ⟨xs, ys, rfl, rfl⟩
    rw [destruct_add, destruct_add]
    cases xs.destruct with
    | none => cases ys.destruct <;> simp [Seq.BisimO]
    | some p =>
      obtain ⟨h1, t1⟩ := p
      cases ys.destruct with
      | none => simp [Seq.BisimO]
      | some q =>
        obtain ⟨h2, t2⟩ := q
        exact ⟨Nat.add_comm h1 h2, t1, t2, rfl, rfl⟩
  · exact ⟨xs, ys, rfl, rfl⟩

/-- `nil` on the left annihilates: `add` truncates to the shorter input. -/
@[simp] theorem nil_add (xs : Seq ℕ) : add Seq.nil xs = Seq.nil := by
  rw [add]; simp

/-- `nil` on the right annihilates. -/
@[simp] theorem add_nil (xs : Seq ℕ) : add xs Seq.nil = Seq.nil := by
  rw [add]; cases xs <;> simp

/-- One-step unfolding of `add` on two `cons`es. -/
@[simp] theorem add_cons_cons (a : ℕ) (x : Seq ℕ) (b : ℕ) (y : Seq ℕ) :
    add (cons a x) (cons b y) = cons (a + b) (add x y) := by
  rw [add]; simp

def mul (s1 s2 : Seq ℕ) : Seq ℕ :=
  s1.bindOrStop fun h1 t1 =>
    s2.bindOrStop fun h2 t2 =>
      .cons (h1 * h2) (add (mul s1 t2) (mul t1 s2))
partial_fixpoint

/-- One-step unfolding of `mul` on two `cons`es. Not a `simp` lemma: its right-hand side contains
further `mul`s. -/
theorem mul_cons_cons (a : ℕ) (x : Seq ℕ) (b : ℕ) (y : Seq ℕ) :
    mul (cons a x) (cons b y) = cons (a * b) (add (mul (cons a x) y) (mul x (cons b y))) := by
  rw [mul]; simp


/-

friendly:

f (⨆ c i) = ⨆ f (c i)



-/
