import Mathlib.Data.W.Basic
import Colean.DataCmd

/-! # Test: `datatype` with a recursive argument under a dependent arrow, against Mathlib's `WType`

`W α β` is the W-type of the container `(α, β)`; `WType β` is Mathlib's. -/

universe u v

namespace DataTest

noncomputable section

datatype W (α : Type u) (β : α → Type v)
  | sup (a : α) (f : β a → W α β)

#check @W.sup
#check @W.rec
#check @W.B.sup_f

def W.toW {α : Type u} {β : α → Type v} (t : W α β) : WType β :=
  W.fold (S := WType β) (fun | .sup a f => ⟨a, f⟩) t

def W.ofW {α : Type u} {β : α → Type v} : WType β → W α β
  | ⟨a, f⟩ => .sup a fun b => ofW (f b)

theorem W.toW_ofW {α : Type u} {β : α → Type v} (t : WType β) : (W.ofW t).toW = t := by
  induction t with
  | mk a f ih => simp [W.ofW, W.toW] at *; simp [ih]

/-- Induction on the `datatype`: the hypothesis for `f` is `∀ b, motive (f b)`. -/
theorem W.ofW_toW {α : Type u} {β : α → Type v} (t : W α β) : W.ofW t.toW = t := by
  induction t with
  | sup a f ih => simp [W.toW] at *; simp [W.ofW, ih]

def W.equivW {α : Type u} {β : α → Type v} : W α β ≃ WType β :=
  ⟨W.toW, W.ofW, W.ofW_toW, W.toW_ofW⟩

end

end DataTest
