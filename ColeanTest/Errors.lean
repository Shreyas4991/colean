import Colean.MutualCmd

/-! # Test: errors before the types are declared

A universe written in the declared sort must be the one the commands give the types, that of
their encoding; a sort with `_`, or none, is not checked. The names a declaration or a block
declares must be free, and a block may not have a type twice. Each failure is reported where it
is (the sort, the type's name, the block's keyword) and declares nothing. -/

universe u v

namespace ErrorsTest

noncomputable section

/-! ### Declared universes -/

/--
error: `P0` is declared with sort `Prop` but defined with sort `Type`: these commands define types, not propositions; write `Type`, or `Type _` to leave the universe to the command
-/
#guard_msgs in
datatype P0 : Prop
  | mk

/-- error: Unknown identifier `P0` -/
#guard_msgs in
#check P0

/--
error: `C3` is declared with sort `Type 3` but defined with sort `Type`: these commands put a type in the universe of its encoding, the largest of those of its indices and of its constructors' data; write `Type`, or `Type _` to leave the universe to the command
-/
#guard_msgs in
codatatype C3 : Type 3
  | mk (n : Nat)

/-- error: Unknown identifier `C3.mk` -/
#guard_msgs in
#check C3.mk

/--
error: `I` is declared with sort `ℕ → Prop` but defined with sort `ℕ → Type`: these commands define types, not propositions; write `ℕ → Type`, or `Type _` to leave the universe to the command
-/
#guard_msgs in
codatatype I : Nat → Prop
  | mk {n : Nat} (i : I (n + 1)) : I n

/-- error: Unknown identifier `I.F` -/
#guard_msgs in
#check I.F

-- A family whose index is a type comes out one universe up.
/--
error: `Big` is declared with sort `Type → Type` but defined with sort `Type → Type 1`: these commands put a type in the universe of its encoding, the largest of those of its indices and of its constructors' data; write `Type → Type 1`, or `Type _` to leave the universe to the command
-/
#guard_msgs in
datatype Big : Type → Type
  | mk {β : Type} (b : β) : Big β

/-- error: Unknown identifier `Big` -/
#guard_msgs in
#check Big

/--
error: `S` is declared with sort `Type v` but defined with sort `Type u`: these commands put a type in the universe of its encoding, the largest of those of its indices and of its constructors' data; write `Type u`, or `Type _` to leave the universe to the command
-/
#guard_msgs in
codatatype S (α : Type u) : Type v
  | mk (a : α) (s : S α)

/-- error: Unknown identifier `S` -/
#guard_msgs in
#check S

-- In a block, at the first type's sort; the index of the block, declared before, is gone too.
/--
error: `Pa` is declared with sort `Type 1` but defined with sort `Type`: these commands put the types of a block in the universe of its encoding, the largest of those of the block's indices and of the constructors' data; write `Type`, or `Type _` to leave the universe to the command
-/
#guard_msgs in
mutual
datatype Pa : Type 1
  | nil
  | mk (q : Qa)
datatype Qa : Type 1
  | mk (p : Pa)
end

/-- error: Unknown identifier `Pa_Qa.Ix` -/
#guard_msgs in
#check Pa_Qa.Ix

-- In a mixed block, the outermost run and a run inside, closed; the open run is gone too.
/--
error: `Tree` is declared with sort `Type 2` but defined with sort `Type`: these commands put a type in the universe of its encoding, the largest of those of its indices and of its constructors' data; write `Type`, or `Type _` to leave the universe to the command
-/
#guard_msgs in
mixed_mutual
codatatype Tree : Type 2
  | node (children : Forest)
datatype Forest : Type 2
  | nil
  | cons (t : Tree) (f : Forest)
end

/-- error: Unknown identifier `Forest.Open` -/
#guard_msgs in
#check Forest.Open

/--
error: `Forest₁` is declared with sort `Type 1` but defined with sort `Type`: these commands put a type in the universe of its encoding, the largest of those of its indices and of its constructors' data; write `Type`, or `Type _` to leave the universe to the command
-/
#guard_msgs in
mixed_mutual
codatatype Tree₁
  | node (children : Forest₁)
datatype Forest₁ : Type 1
  | nil
  | cons (t : Tree₁) (f : Forest₁)
end

/-- error: Unknown identifier `Forest₁.Open` -/
#guard_msgs in
#check Forest₁.Open

/-- error: Unknown identifier `Tree₁` -/
#guard_msgs in
#check Tree₁

/-! Matching sorts are accepted, up to the order in `max`. -/

datatype A0 : Type
  | mk

codatatype S1 (α : Type u) : Type u
  | cons (a : α) (t : S1 α)

datatype N1 : Nat → Type
  | z : N1 0

datatype Big1 : Type → Type 1
  | mk {β : Type} (b : β) : Big1 β

datatype W1 (α : Type u) : Type _
  | mk (a : α)

datatype Two (α : Type u) (β : Type v) : Type (max v u)
  | mk (a : α) (b : β)

mutual
datatype Pa₁ : Nat → Type
  | nil : Pa₁ 0
  | mk {n : Nat} (q : Qa₁ n) : Pa₁ (n + 1)
datatype Qa₁ : Nat → Type
  | mk {n : Nat} (p : Pa₁ n) : Qa₁ n
end

mixed_mutual
codatatype Tree₂ (α : Type u) : Type u
  | node (a : α) (children : Forest₂ α)
datatype Forest₂ (α : Type u) : Type u
  | nil
  | cons (t : Tree₂ α) (f : Forest₂ α)
end

example : Type := A0
example (α : Type u) : Type u := S1 α
example : Nat → Type := N1
example : Type → Type 1 := Big1
example (α : Type u) : Type u := W1 α
example (α : Type u) (β : Type v) : Type (max u v) := Two α β
example : Nat → Type := Pa₁
example (α : Type u) : Type u := Tree₂ α
example (α : Type u) : Type u := Forest₂ α

/-! ### Names -/

-- A type twice in a block, at the second.
/-- error: `Pc` is declared twice in this block -/
#guard_msgs in
mutual
datatype Pc
  | nil
datatype Pc
  | mk
end

/-- error: Unknown identifier `Pc_Pc.Ix` -/
#guard_msgs in
#check Pc_Pc.Ix

-- A type of a block declared already, at its name.
def Pd := Nat

/-- error: `ErrorsTest.Pd` has already been declared -/
#guard_msgs in
mutual
datatype Pd
  | nil
datatype Qd
  | mk (p : Pd)
end

/-- error: Unknown identifier `Qd` -/
#guard_msgs in
#check Qd

/-- error: Unknown identifier `Pd_Qd.Ix` -/
#guard_msgs in
#check Pd_Qd.Ix

-- The name of the block, or its index, declared already, at the keyword.
def Pb_Qb := Nat

/--
error: `ErrorsTest.Pb_Qb` has already been declared, and this block declares it: the block is named after its types, joined by `_`, in their common namespace, and its index is `Ix` in the block's namespace; rename or reorder the types, or declare the block in another namespace
-/
#guard_msgs in
mutual
datatype Pb
  | nil
  | mk (q : Qb)
datatype Qb
  | mk (p : Pb)
end

/-- error: Unknown identifier `Pb` -/
#guard_msgs in
#check Pb

/-- error: Unknown constant `ErrorsTest.Pb_Qb.Ix` -/
#guard_msgs in
#check Pb_Qb.Ix

def Pe_Qe.Ix := Nat

/--
error: `ErrorsTest.Pe_Qe.Ix` has already been declared, and this block declares it: the block is named after its types, joined by `_`, in their common namespace, and its index is `Ix` in the block's namespace; rename or reorder the types, or declare the block in another namespace
-/
#guard_msgs in
mutual
codatatype Pe
  | mk (q : Qe)
codatatype Qe
  | mk (p : Pe)
end

/-- error: Unknown identifier `Pe_Qe` -/
#guard_msgs in
#check Pe_Qe

-- A single declaration whose name is taken.
/-- error: `ErrorsTest.A0` has already been declared -/
#guard_msgs in
datatype A0
  | other

/-- error: Unknown constant `ErrorsTest.A0.other` -/
#guard_msgs in
#check A0.other

-- In a mixed block: a type twice, an open type and the name of a run declared already.
/-- error: `Mf` is declared twice in this block -/
#guard_msgs in
mixed_mutual
codatatype Mt
  | node (f : Mf)
datatype Mf
  | nil
datatype Mf
  | cons (t : Mt)
end

/-- error: Unknown identifier `Mt` -/
#guard_msgs in
#check Mt

def Forest₃.Open := Nat

/--
error: `ErrorsTest.Forest₃.Open` has already been declared, and this block declares it: a type `T` of a run inside the first is declared open, as `T.Open`; rename the type, or declare the block in another namespace
-/
#guard_msgs in
mixed_mutual
codatatype Tree₃
  | node (children : Forest₃)
datatype Forest₃
  | nil
  | cons (t : Tree₃) (f : Forest₃)
end

/-- error: Unknown identifier `Tree₃` -/
#guard_msgs in
#check Tree₃

def Rs_Fs := Nat

/--
error: `ErrorsTest.Rs_Fs` has already been declared, and this block declares it: a run of several types is named after its types, joined by `_`, in their common namespace, with its index `Ix` and, inside the first run, its open form `Open` in the run's namespace; rename or reorder the types, or declare the block in another namespace
-/
#guard_msgs in
mixed_mutual
codatatype T₄
  | node (r : Rs)
datatype Rs
  | node (t : T₄) (f : Fs)
datatype Fs
  | nil
  | cons (r : Rs) (f : Fs)
end

/-- error: Unknown constant `ErrorsTest.Rs_Fs.Ix` -/
#guard_msgs in
#check Rs_Fs.Ix

end

end ErrorsTest
