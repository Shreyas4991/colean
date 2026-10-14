import Colean.Subtypes.CodataCmd

/-! Colists with a type parameter: corecursion across universes, and `map`. -/

universe u v

namespace CodataTest

noncomputable section

codata PList (α : Type u)
  | nil
  | cons (a : α) (s : PList α)

#check @PList.corec
#check @PList.bisim
#check @PList.cons

/-- Corecursion from a state in `Type` into a type in `Type u`: no `ULift`. -/
def PList.const {α : Type u} (a : α) : PList α := PList.corec (fun _ => .cons a ()) ()

example {α : Type u} (a : α) : PList.const a = .cons a (.const a) := PList.corec_eq _ _

/-- Map, by corecursion; its unfolding, by `dtor_corec` and the simp lemmas. -/
def PList.map {α : Type u} {β : Type v} (f : α → β) (s : PList α) : PList β :=
  PList.corec (fun s => match s.dtor with
    | .nil => .nil
    | .cons a t => .cons (f a) t) s

example {α : Type u} {β : Type v} (f : α → β) (a : α) (s : PList α) :
    (PList.map f (.cons a s)).dtor = .cons (f a) (PList.map f s) := by
  simp [PList.map, PList.dtor_corec]

example {α : Type u} {β : Type v} (f : α → β) : PList.map f .nil = .nil := by
  rw [PList.map, PList.corec_eq]
  simp

end

end CodataTest
