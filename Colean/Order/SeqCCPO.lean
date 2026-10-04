import Mathlib.Data.Seq.Defs
import Init.Internal.Order.Basic

/-!
# A CCPO on `Stream'.Seq` for `partial_fixpoint`

`s₁ ⊑ s₂` is the **prefix order**: every position that `s₁` defines, `s₂` defines to the same
value. Bottom is `Seq.nil`, the finite sequences are the partial elements, and the infinite
sequences are the maximal ones. The supremum of a chain is the union of its prefixes.

With the resulting `CCPO` instance and the monotonicity lemma for `cons`, corecursive
definitions can be written with `partial_fixpoint`.

Note: `PartialOrder` below always means `Lean.Order.PartialOrder`, which is unrelated to
Mathlib's order hierarchy.
-/

namespace Stream'.Seq

open scoped Lean.Order

variable {α : Type u}

/-- The prefix order: `s₁` approximates `s₂` if `s₂` agrees with `s₁` wherever `s₁` is defined. -/
instance instPartialOrder : Lean.Order.PartialOrder (Seq α) where
  rel s₁ s₂ := ∀ n a, s₁.get? n = some a → s₂.get? n = some a
  rel_refl _ _ h := h
  rel_trans h₁ h₂ n a h := h₂ n a (h₁ n a h)
  rel_antisymm {s₁ s₂} h₁ h₂ := Seq.ext fun n => by
    rcases hn : s₁.get? n with _ | a
    · rcases hn' : s₂.get? n with _ | b
      · rfl
      · exact absurd (h₂ n b hn') (by simp [hn])
    · exact (h₁ n a hn).symm

theorem rel_iff {s₁ s₂ : Seq α} :
    s₁ ⊑ s₂ ↔ ∀ n a, s₁.get? n = some a → s₂.get? n = some a := Iff.rfl

open Classical in
/-- Position `n` of the union of a family of sequences. -/
noncomputable def csupFun (c : Seq α → Prop) (n : ℕ) : Option α :=
  if h : ∃ a, ∃ s, c s ∧ s.get? n = some a then some h.choose else none

theorem csupFun_eq_none {c : Seq α → Prop} {n} :
    csupFun c n = none ↔ ¬ ∃ a, ∃ s, c s ∧ s.get? n = some a := by
  unfold csupFun; split <;> simp_all

/-- The union of a family of sequences: position `n` holds the value that some member defines
there. For a chain this is the least upper bound. -/
noncomputable def csup (c : Seq α → Prop) : Seq α :=
  ⟨csupFun c, by
    intro n hn
    rw [csupFun_eq_none] at hn ⊢
    rintro ⟨a, s, hs, ha⟩
    obtain ⟨b, hb⟩ := s.ge_stable (Nat.le_succ n) ha
    exact hn ⟨b, s, hs, hb⟩⟩

theorem get?_csup (c : Seq α → Prop) (n : ℕ) : (csup c).get? n = csupFun c n := rfl

theorem exists_of_get?_csup {c : Seq α → Prop} {n a} (h : (csup c).get? n = some a) :
    ∃ s, c s ∧ s.get? n = some a := by
  rw [get?_csup, csupFun] at h
  split at h
  · rename_i hex
    obtain ⟨s, hs, hsa⟩ := hex.choose_spec
    exact ⟨s, hs, by rw [hsa, Option.some_inj.mp h]⟩
  · simp at h

theorem le_csup {c : Seq α → Prop} (hc : Lean.Order.chain c) {s : Seq α} (hs : c s) :
    s ⊑ csup c := by
  intro n a ha
  have hex : ∃ a, ∃ s, c s ∧ s.get? n = some a := ⟨a, s, hs, ha⟩
  rw [get?_csup, csupFun, dite_eq_left hex]
  obtain ⟨t, ht, hta⟩ := hex.choose_spec
  rcases hc s t hs ht with h | h
  · rw [← hta, h n a ha]
  · rw [← ha, h n _ hta]

theorem csup_spec {c : Seq α → Prop} (hc : Lean.Order.chain c) :
    Lean.Order.is_sup c (csup c) := by
  intro x
  constructor
  · exact fun h y hy => Lean.Order.PartialOrder.rel_trans (le_csup hc hy) h
  · intro h n a ha
    obtain ⟨s, hs, hsa⟩ := exists_of_get?_csup ha
    exact h s hs n a hsa

/-! ### The prefix order against `nil` and `cons` -/

/-- `nil` is the least element. -/
@[simp] theorem nil_le (s : Seq α) : nil ⊑ s := by
  intro n a h
  simp at h

@[simp] theorem le_nil_iff {s : Seq α} : s ⊑ nil ↔ s = nil :=
  ⟨fun h => Lean.Order.PartialOrder.rel_antisymm h (nil_le s), by rintro rfl; exact nil_le _⟩

@[simp] theorem not_cons_le_nil {a : α} {s : Seq α} : ¬ cons a s ⊑ nil := by simp

@[simp] theorem cons_le_cons_iff {a b : α} {s t : Seq α} :
    cons a s ⊑ cons b t ↔ a = b ∧ s ⊑ t := by
  constructor
  · intro h
    refine ⟨by simpa using (h 0 a (by simp)).symm, fun n v hv => ?_⟩
    simpa using h (n + 1) v (by simpa using hv)
  · rintro ⟨rfl, h⟩ n v hv
    cases n with
    | zero => simpa using hv
    | succ n => rw [get?_cons_succ] at hv ⊢; exact h n v hv

noncomputable instance instCCPO : Lean.Order.CCPO (Seq α) where
  has_csup hc := ⟨csup _, csup_spec hc⟩

/-- The bottom element of the `CCPO` structure is `nil`. -/
@[simp] theorem bot_eq_nil : (Lean.Order.bot : Seq α) = nil :=
  le_nil_iff.mp (Lean.Order.bot_le nil)

/-- `cons` is monotone in its tail, so recursive occurrences may appear under it. -/
@[partial_fixpoint_monotone]
theorem cons_mono {β : Sort v} [Lean.Order.PartialOrder β] (a : α) (f : β → Seq α)
    (hf : Lean.Order.monotone f) : Lean.Order.monotone (fun x => cons a (f x)) := by
  intro x y hxy n v hv
  cases n with
  | zero => simpa using hv
  | succ n =>
    rw [get?_cons_succ] at hv ⊢
    exact hf x y hxy n v hv

end Stream'.Seq
