import Colean.Subtypes.CodataCmd

/-! Streams of naturals: the smallest `codata`, one constructor of arity one. -/

namespace CodataTest

noncomputable section

codata Str
  | cons (n : Nat) (s : Str)

#check @Str.dtor
#check @Str.corec
#check @Str.dtor_corec
#check @Str.bisim
#check @Str.ctor
#check @Str.corec_eq
#check @Str.cons
#check @Str.dtor_cons

/-- A constant stream. -/
def Str.const (n : Nat) : Str := Str.corec (fun _ => .cons n ()) ()

example (n : Nat) : Str.dtor (Str.const n) = .cons n (Str.const n) := Str.dtor_corec _ _

/-- The unfolding of a corecursive definition through the derived constructor. -/
example (n : Nat) : Str.const n = Str.cons n (Str.const n) := Str.corec_eq _ _

example (n : Nat) (s : Str) : Str.dtor (Str.cons n s) = .cons n s := by simp

example (n : Nat) (s t : Str) (h : Str.cons n s = Str.cons n t) : s = t := by
  have := congrArg Str.dtor h
  simp at this
  exact this

/-- Two corecursive definitions of the same stream, identified by bisimulation. -/
example (n : Nat) : Str.const n = Str.corec (fun k : Nat => .cons n (k + 1)) 0 := by
  refine Str.bisim
    (fun x y => ∃ k, x = Str.const n ∧ y = Str.corec (fun k : Nat => .cons n (k + 1)) k) ?_
    ⟨0, rfl, rfl⟩
  rintro _ _ ⟨k, rfl, rfl⟩
  rw [Str.const, Str.dtor_corec, Str.dtor_corec]
  exact Str.F.Rel.cons n _ _ ⟨k + 1, rfl, rfl⟩

end

end CodataTest
