import Colean.MutualCmd

/-! # Test: parameters of a mixed block

All declarations share their parameters, names included, as in Lean's `mutual`; the open types
take one more, for the outer types (`X`, at its own universe). Section variables the block uses
are parameters of every type, as with `inductive`. -/

universe u v

namespace MixedParamTest

open Codata

noncomputable section

-- Two parameters, one used only in the inner run.
mixed_mutual
codata Tree (α : Type u) (β : Type v)
  | node (a : α) (children : Forest α β)
data Forest (α : Type u) (β : Type v)
  | nil (b : β)
  | cons (t : Tree α β) (f : Forest α β)
end

/--
info: @Tree.node : {α : Type u_1} → {β : Type u_2} → α → Forest α β → Tree α β
-/
#guard_msgs in #check @Tree.node
/--
info: @Forest.cons : {α : Type u_1} → {β : Type u_2} → Tree α β → Forest α β → Forest α β
-/
#guard_msgs in #check @Forest.cons
/--
info: @Forest.fold : {α : Type u_2} → {β : Type u_3} → {S : Type u_1} → (Forest.F α β S → S) → Forest α β → S
-/
#guard_msgs in #check @Forest.fold
-- The open forests, with the parameter for the trees at its own universe (the universe of a type
-- is that of the data it stores).
/--
info: MixedParamTest.Forest.Open.{u, v, u_Tree} (α : Type u) (β : Type v) (X : Type u_Tree) : Type (max u_Tree v)
-/
#guard_msgs in #check Forest.Open

/-- The last element of a forest. -/
def Forest.last {α : Type u} {β : Type v} (f : Forest α β) : β :=
  Forest.fold (S := β) (fun | .nil b => b | .cons _ b => b) f

example {α : Type u} {β : Type v} (t : Tree α β) (b : β) :
    (Forest.cons t (.cons t (.nil b))).last = b := by
  simp [Forest.last]

-- Section variables: one used by the inner run only is a parameter of both.
section

variable {γ : Type u}

mixed_mutual
data Box
  | mk (c : Stream)
codata Stream
  | cons (g : γ) (b : Box) (s : Stream)
end

end

/-- info: @Box.mk : {γ : Type u_1} → Stream → Box -/
#guard_msgs in #check @Box.mk
/-- info: @Stream.cons : {γ : Type u_1} → γ → Box → Stream → Stream -/
#guard_msgs in #check @Stream.cons
/--
info: @Box.rec : {γ : Type u_2} →
  {motive : Box → Sort u_1} → ((c : Stream) → ((t : Box) → t ∈ c → motive t) → motive (Box.mk c)) → (t : Box) → motive t
-/
#guard_msgs in #check @Box.rec

-- Implicit binders in the constructors, and an implicit parameter, implicit in the types too, as
-- with `inductive`.
mixed_mutual
codata Lab {ι : Type} (f : ι → Nat)
  | node {i : ι} (n : Fin (f i)) (cs : LabList f)
data LabList {ι : Type} (f : ι → Nat)
  | nil
  | cons (t : Lab f) (rest : LabList f)
end

/--
info: @Lab.node : {ι : Type} → {f : ι → ℕ} → {i : ι} → Fin (f i) → LabList f → Lab f
-/
#guard_msgs in #check @Lab.node

-- No parameters, and an inner run that needs no outer type: the open type is a constant on its
-- own, and the statements show the closed one.
namespace NoParam

mixed_mutual
codata Tree
  | node (cs : Forest)
data Forest
  | nil
  | cons (n : Nat) (f : Forest)
end

/-- info: Forest.cons : ℕ → Forest → Forest -/
#guard_msgs in #check @Forest.cons
/-- info: Forest.nil : Forest -/
#guard_msgs in #check @Forest.nil
/-- info: Tree.node : Forest → Tree -/
#guard_msgs in #check @Tree.node
/--
info: @Forest.rec : {motive : Forest → Sort u_1} →
  motive Forest.nil → ((n : ℕ) → (f : Forest) → motive f → motive (Forest.cons n f)) → (t : Forest) → motive t
-/
#guard_msgs in #check @Forest.rec

end NoParam

end

end MixedParamTest
