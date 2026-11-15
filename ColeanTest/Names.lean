import Colean.MutualCmd

/-! # Test: types named like generated declarations

Inside the namespace of `T`, a generated `T.T` would shadow the type. -/

universe u

namespace NamesTest

codatatype B (α : Type u)
  | cons (a : α) (tail : B α)

#check @B.cons
#check @B.corec
#check @B.B'.cons_tail

datatype F
  | leaf
  | node (l r : F)

#check @F.node
#check @F.rec
#check @F.F'.map

codatatype Shape : Nat → Type
  | mk {n : Nat} (s : Shape (n + 1)) : Shape n

#check @Shape.mk
#check @Shape.bisim

/-! ### Binders users refer to by name

`motive`, `S` and the index `m` of a block are plain names, unless the declaration uses them. -/

noncomputable section

example : F → Nat := fun t => F.rec (motive := fun _ => Nat) 0 (fun _ _ a b => a + b) t

example (t : F) : Nat := F.casesOn (motive := fun _ => Nat) t 0 fun _ _ => 1

example : B Nat := B.corec (S := Nat) (fun n => .cons n (n + 1)) 0

example : F → Nat := F.fold (S := Nat) fun
  | .leaf => 0
  | .node a b => a + b + 1

mutual
codatatype Ev
  | ev (o : Od)
codatatype Od
  | od (e : Ev)
end

example : Ev := Ev.corec (S₁ := Unit) (S₂ := Unit) (fun _ => .ev ()) (fun _ => .od ()) ()

example : Ev_Od Ev_Od.Ix.Ev := Ev_Od.corec (S := fun _ => Unit) (m := .Ev)
  (fun | .Ev, _ => .ev () | .Od, _ => .od ()) ()

-- A parameter named `S`: the state's binder does not shadow it.
codatatype SS (S : Type)
  | cons (a : S) (t : SS S)

example : SS Nat := SS.corec (S := Nat) (fun n => .cons n (n + 1)) 0

end

end NamesTest
