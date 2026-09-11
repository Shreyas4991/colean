import MetricCorec.Order.SeqCCPO

/-!
# Strict case analysis on `Stream'.Seq`

`bindOrStop s k` looks at the first step of `s`: it stops with `nil` when `s` is `nil`, and
otherwise continues with `k` applied to the head and the tail. This is bind in the `Option` monad
on `destruct s`, followed by the map sending `none` to `nil`.

Two facts make it work with `partial_fixpoint`:

* `bindOrStop_mono`: it is monotone in the continuation, so recursive occurrences may appear inside
  the continuation (registered as `@[partial_fixpoint_monotone]`);
* `bindOrStop_le_bindOrStop`: it is monotone in the sequence, provided the continuation is monotone
  in the tail. This is the step used when proving that a `partial_fixpoint` definition is monotone
  in its arguments.
-/

namespace Stream'.Seq

open scoped Lean.Order

/-- Strict case analysis: `nil` stops, `cons hd tl` continues with `act hd tl`. -/
def bindOrStop {α β : Type} (s : Seq α) (act : α → Seq α → Seq β) : Seq β :=
  match s.destruct with
  | none => .nil
  | .some (hd, tl) => act hd tl

@[simp] theorem nil_bindOrStop {α β : Type} (k : α → Seq α → Seq β) :
    (nil : Seq α).bindOrStop k = nil := by
  simp [bindOrStop]

@[simp] theorem cons_bindOrStop {α β : Type} (a : α) (s : Seq α) (k : α → Seq α → Seq β) :
    (cons a s).bindOrStop k = k a s := by
  simp [bindOrStop]

/-- `bindOrStop` is monotone in its continuation. Registering this is all `partial_fixpoint` needs
in order to accept recursive calls inside the continuation. -/
@[partial_fixpoint_monotone]
theorem bindOrStop_mono {γ : Sort v} [Lean.Order.PartialOrder γ] {α β : Type} (s : Seq α)
    (k : γ → α → Seq α → Seq β) (hk : Lean.Order.monotone k) :
    Lean.Order.monotone (fun x => s.bindOrStop (k x)) := by
  intro x y hxy
  cases s with
  | nil => simp
  | cons a t => simpa using hk x y hxy a t

/-- `bindOrStop` is monotone in the sequence as well, provided the continuation is monotone in the
tail. This relational form is what the fixpoint-induction step for argument monotonicity uses. -/
theorem bindOrStop_le_bindOrStop {α β : Type} {s t : Seq α} {k k' : α → Seq α → Seq β}
    (hst : s ⊑ t) (hk : ∀ a u v, u ⊑ v → k a u ⊑ k' a v) : s.bindOrStop k ⊑ t.bindOrStop k' := by
  cases s with
  | nil => simp
  | cons a u =>
    cases t with
    | nil => simp at hst
    | cons b v =>
      rw [cons_le_cons_iff] at hst
      obtain ⟨rfl, huv⟩ := hst
      simpa using hk a u v huv

end Stream'.Seq
