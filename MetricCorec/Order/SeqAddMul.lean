import MetricCorec.Order.SeqCCPO

/-!
# `add` and `mul` on `Seq ℕ` via `partial_fixpoint`

Corecursive definitions on top of the `CCPO` instance from `MetricCorec.Order.SeqCCPO`: the
examples `zeros` and `zeroOnes`, pointwise addition `add` together with its pointwise description,
its monotonicity (so that recursive occurrences may appear under `add`), its one-step unfolding
`destruct_add`, commutativity and the `nil` laws, and finally the product `mul`, whose recursive
occurrences sit under `add`.
-/

open Stream' Stream'.Seq
open scoped Lean.Order

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
  match s1.destruct, s2.destruct with
  | none, _ => .nil
  | _, none => .nil
  | .some (h1, t1), .some (h2, t2) =>
    .cons (h1 + h2) (add t1 t2)
partial_fixpoint

/-- Pointwise description of `add`: position `n` is defined iff both inputs are, and then holds
their sum. -/
theorem get?_add (s1 s2 : Seq ℕ) (n : ℕ) :
    (add s1 s2).get? n =
      match s1.get? n, s2.get? n with
      | some a, some b => some (a + b)
      | _, _ => none := by
  induction n generalizing s1 s2 with
  | zero =>
    rw [add]
    cases h1 : s1.destruct with
    | none => obtain rfl := destruct_eq_none h1; simp
    | some p =>
      obtain ⟨head1, tail1⟩ := p
      obtain rfl := destruct_eq_cons h1
      cases h2 : s2.destruct with
      | none => obtain rfl := destruct_eq_none h2; simp
      | some q =>
        obtain ⟨head2, tail2⟩ := q
        obtain rfl := destruct_eq_cons h2
        simp
  | succ n ih =>
    rw [add]
    cases h1 : s1.destruct with
    | none => obtain rfl := destruct_eq_none h1; simp
    | some p =>
      obtain ⟨head1, tail1⟩ := p
      obtain rfl := destruct_eq_cons h1
      cases h2 : s2.destruct with
      | none => obtain rfl := destruct_eq_none h2; simp
      | some q =>
        obtain ⟨head2, tail2⟩ := q
        obtain rfl := destruct_eq_cons h2
        simp only [get?_cons_succ]
        exact ih tail1 tail2

#check add.fixpoint_induct

namespace Lean.Order

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
`cons` does. -/
theorem add_le_add_seq {s1 s2 t1 t2 : Seq ℕ} (h1 : s1 ⊑ t1) (h2 : s2 ⊑ t2) :
    add s1 s2 ⊑ add t1 t2 := by
  revert s1 s2 t1 t2
  apply add.fixpoint_induct
    (motive := fun add' => ∀ s1 s2 t1 t2 : Seq ℕ, s1 ⊑ t1 → s2 ⊑ t2 → add' s1 s2 ⊑ add' t1 t2)
  · apply Lean.Order.admissible_pi; intro s1
    apply Lean.Order.admissible_pi; intro s2
    apply Lean.Order.admissible_pi; intro t1
    apply Lean.Order.admissible_pi; intro t2
    apply Lean.Order.admissible_pi; intro _
    apply Lean.Order.admissible_pi; intro _
    exact Lean.Order.admissible_apply₂_rel s1 t1 s2 t2
  · intro add' ih s1 s2 t1 t2 h1 h2
    cases s1 with
    | nil => simp
    | cons a s1 =>
      cases s2 with
      | nil => simp
      | cons b s2 =>
        cases t1 with
        | nil => simp at h1
        | cons a' t1 =>
          cases t2 with
          | nil => simp at h2
          | cons b' t2 =>
            rw [cons_le_cons_iff] at h1 h2
            obtain ⟨rfl, h1⟩ := h1
            obtain ⟨rfl, h2⟩ := h2
            simpa using ih s1 s2 t1 t2 h1 h2

/-- `add` is monotone in both arguments, so recursive occurrences may appear under it. -/
@[partial_fixpoint_monotone]
theorem add_mono {β : Sort v} [Lean.Order.PartialOrder β] (f g : β → Seq ℕ)
    (hf : Lean.Order.monotone f) (hg : Lean.Order.monotone g) :
    Lean.Order.monotone (fun x => add (f x) (g x)) :=
  fun x y hxy => add_le_add_seq (hf x y hxy) (hg x y hxy)

  -- intro x y hxy
  -- simp

  -- rw [get?_add] at ha
  -- rw [get?_add]
  -- cases hb : (f x).get? n with
  -- | none => rw [hb] at ha; simp at ha
  -- | some b =>
  --   cases hc : (g x).get? n with
  --   | none => rw [hb, hc] at ha; simp at ha
  --   | some c =>
  --     rw [hf x y hxy n b hb, hg x y hxy n c hc]
  --     rw [hb, hc] at ha
  --     exact ha

/-- One-step unfolding of `add` at the level of `destruct`. -/
theorem destruct_add (s1 s2 : Seq ℕ) :
    (add s1 s2).destruct =
      match s1.destruct, s2.destruct with
      | some (h1, t1), some (h2, t2) => some (h1 + h2, add t1 t2)
      | _, _ => none := by
  rw [add]
  cases s1.destruct with
  | none => simp
  | some p =>
    obtain ⟨head1, tail1⟩ := p
    cases s2.destruct with
    | none => simp
    | some q => obtain ⟨head2, tail2⟩ := q; simp

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
  rw [add]; cases xs.destruct <;> simp

def mul (s1 s2 : Seq ℕ) : Seq ℕ :=
  match s1.destruct, s2.destruct with
  | none, _ => .nil
  | _, none => .nil
  | .some (h1, t1), .some (h2, t2) =>
    .cons (h1 * h2) (add (mul s1 t2) (mul t1 s2))
partial_fixpoint
