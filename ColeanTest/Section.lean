import Colean.DataCmd

/-! # Test: section variables

The section variables a declaration uses become its first parameters, as with `inductive`, with
their own binder infos in the types and implicit elsewhere; the others are left out. -/

universe u

namespace SectionTest

section

variable (β : Type u) {γ : Type} [Inhabited γ]

codatatype SStream
  | cons (b : β) (t : SStream)

datatype SList
  | nil
  | cons (c : γ) (l : SList)

end

noncomputable section

/-- `β` is explicit in the type, implicit in the constructors and lemmas. -/
example : SStream Nat := SStream.corec (S := Unit) (fun _ => .cons 0 ()) ()

example (s : SStream Nat) : SStream.dtor (SStream.cons 1 s) = .cons 1 s := SStream.dtor_cons 1 s

/-- `γ` is implicit, and the unused instance is not a parameter. -/
example : SList (γ := Bool) := .cons true .nil

example : (SList.cons true .nil).fold (S := Nat) (fun | .nil => 0 | .cons _ n => n + 1) = 1 := by
  simp

end

end SectionTest
