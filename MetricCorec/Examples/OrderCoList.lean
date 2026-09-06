import Mathlib
import Init.Internal.Order.Basic

variable {α : Type}

instance : Lean.Order.CCPO (Stream'.Seq α) where
  rel s₁ s₂ := ∀ n a, s₁.get? n = some a → s₂.get? n = some a
  rel_refl n a h := h
  rel_trans h₁₂ h₂₃ n a h := h₂₃ n a (h₁₂ n a h)
  rel_antisymm h₁₂ h₂₁ := by
    rename_i s₁ s₂
    apply Stream'.Seq.ext
    intro n
    cases hn : s₁.get? n with
    | none =>
      cases hn' : s₂.get? n with
      | none => rfl
      | some b =>
        have hcontra := h₂₁ n b hn'
        simp [hn] at hcontra
    | some a =>
      exact (h₁₂ n a hn).symm
  has_csup := sorry

-- pointwise addition on
def add (xs ys : Stream'.Seq Nat) : Stream'.Seq Nat :=
  Stream'.Seq.zipWith (· + ·) xs ys

def Fib (s : Stream'.Seq Nat) : Stream'.Seq Nat :=
  .cons 0 (add (.cons 1 s) s)

example (xs ys : List Nat) : xs <+: ys → xs.tail <+: ys.tail := by
  intro h
  cases xs with
  | nil => simp
  | cons x xs =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp at h
      grind

#check Lean.Order.ind_not

-- open Lean.Order in
@[partial_fixpoint_monotone]
theorem Lean.Order.Fib_monotone : Order.monotone (fun s => Fib s) := by
  intro s₁ s₂ h n v hn
  cases n with
  | zero =>
    simp only [Fib, Stream'.Seq.get?_cons_zero] at hn ⊢
    exact hn
  | succ n =>
    simp only [Fib, Stream'.Seq.get?_cons_succ, add, Stream'.Seq.get?_zipWith] at hn ⊢
    cases n with
    | zero =>
      simp only [Stream'.Seq.get?_cons_zero] at hn ⊢
      rcases hb : s₁.get? 0 with _ | b
      · simp [hb] at hn
      · rw [hb, Option.map₂_some_some] at hn
        rw [h 0 b hb, Option.map₂_some_some]
        exact hn
    | succ m =>
      simp only [Stream'.Seq.get?_cons_succ] at hn ⊢
      rcases ha : s₁.get? m with _ | a
      · simp [ha] at hn
      · rcases hb : s₁.get? (m + 1) with _ | b
        · simp [ha, hb] at hn
        · rw [ha, hb, Option.map₂_some_some] at hn
          rw [h m a ha, h (m + 1) b hb, Option.map₂_some_some]
          exact hn

noncomputable def fib := Lean.Order.fix _ Lean.Order.Fib_monotone


set_option trace.Elab.Tactic.monotonicity true

open scoped Lean.Order
def fib' : Stream'.Seq Nat := Fib fib'
partial_fixpoint monotonicity by
  monotonicity

open Qq

#eval Lean.Meta.Monotonicity.findMonoThms q(fun s => Fib s)

open Lean

#eval show MetaM Unit from do
  let res := (Lean.Meta.Monotonicity.monotoneExt.getState (← getEnv))
  IO.println res.format
  return
