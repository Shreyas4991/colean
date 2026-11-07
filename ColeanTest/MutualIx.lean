import Colean.MutualCmd

/-! # Test: blocks whose types have different indices

A block is one family over `Blk.Ix`, which has a constructor per type with the indices of that type
as arguments. So the types need not agree on their indices. -/

universe u

open Codata

namespace MutualIxTest

noncomputable section

/-! Different index types, used as in the user's declaration. -/

mutual
data Pa : Nat → Type
  | nil : Pa 0
  | mk {n : Nat} (q : Qa true) : Pa (n + 1)
data Qa : Bool → Type
  | mk (p : Pa 3) : Qa true
end

example (q : Qa false) : False := by cases q

example (p : Pa 0) : p = Pa.nil := by
  cases p with
  | nil => rfl

/-- An algebra over the block matches the type and its indices at once. -/
def depthAlg : ∀ i, Pa_Qa.F (fun _ => Nat) i → Nat
  | .Pa _, .nil => 0
  | .Pa _, .Pa_mk k => k + 1
  | .Qa _, .Qa_mk k => k + 1

def Pa.depth {n : Nat} (p : Pa n) : Nat := Pa.fold depthAlg p
def Qa.depth {b : Bool} (q : Qa b) : Nat := Qa.fold depthAlg q

@[simp] theorem Pa.depth_nil : Pa.nil.depth = 0 := by
  simp [Pa.depth, depthAlg]

@[simp] theorem Pa.depth_mk {n : Nat} (q : Qa true) :
    (Pa.mk q : Pa (n + 1)).depth = q.depth + 1 := by
  simp [Pa.depth, Qa.depth, depthAlg]

/-- Induction over the block: the motive is a family over `Ix`. -/
def Tops : ∀ i, Pa_Qa i → Prop
  | .Pa n, _ => n = 0 ∨ 0 < n
  | .Qa b, _ => b = true

theorem tops (i : Pa_Qa.Ix) (x : Pa_Qa i) : Tops i x := by
  induction x with
  | nil => simp [Tops]
  | Pa_mk q ih => simp [Tops]
  | Qa_mk p ih => simp [Tops]

theorem Qa.index {b : Bool} (q : Qa b) : b = true := tops (.Qa b) q

/-! No index, one index, two indices, with a parameter that the indices depend on. -/

mutual
codata Ca (α : Type u) : List α → Type u
  | nil (l : List α) (q : Cb α) : Ca α l
codata Cb (α : Type u)
  | mk (r : Cc α 2 1)
codata Cc (α : Type u) : (n : Nat) → Fin n → Type u
  | go {n : Nat} {i : Fin n} (l : List α) (p : Ca α l) : Cc α n i
end

/-- A coalgebra with a trivial state: the same list everywhere. -/
def constCoalg {α : Type u} (l : List α) : ∀ i, Unit → Ca_Cb_Cc.F α (fun _ => Unit) i
  | .Ca l', _ => .nil l' ()
  | .Cb, _ => .mk ()
  | .Cc _ _, _ => .go l ()

def Cb.const {α : Type u} (l : List α) : Cb α := Cb.corec (constCoalg l) ()

example {α : Type u} (l : List α) : (Cb.const l).dtor = .mk (Ca_Cb_Cc.corec (constCoalg l) ()) := by
  simp [Cb.const, Ca_Cb_Cc.dtor_corec, constCoalg]

/-! A type under a built-in form or a leaf in its own constructors, and a type of a block with
indices under them. -/

mutual
data Own
  | nil
  | mk (p : List Own)
  | pr (p : Own × Nat)
data Other : Nat → Type
  | stop : Other 0
  | mk {n : Nat} (a : Own) (l : List (Other n)) (p : Other n × Nat) : Other (n + 1)
end

/-- The recursors per type, with nested arguments: the hypothesis of the list of `Other n` is at
`motive_2 n` for every position; that of the pair keeps the block's index of its position, whose
type the recursor cannot read off. -/
theorem Other.index {n : Nat} (o : Other n) : n = 0 ∨ 0 < n := by
  induction o using Other.rec (motive_1 := fun _ => True) with
  | nil => trivial
  | Own_mk p ih => trivial
  | pr p ih => trivial
  | stop => simp
  | Other_mk a l p iha ihl ihp => simp

/-- The length of the list of an `Own.mk`, by the recursor of `Own`, computed by its rules. -/
def Own.width (o : Own) : Nat :=
  Own.rec (motive_2 := fun _ _ => Nat) 0 (fun p _ => p.length) (fun _ _ => 0) 0
    (fun _ _ _ _ _ _ => 0) o

example : (Own.mk [.nil, .mk []]).width = 2 := by
  simp [Own.width]

example (p : List Own) : (Own.mk p).width = p.length := by
  rw [Own.width, Own.rec_mk]

mutual
codata OwnCo
  | mk (p : OwnCo' × OwnCo)
codata OwnCo'
  | mk (a : OwnCo)
end

/-! The same for a single family, with a constant as the index of the result. -/

inductive Color
  | red
  | blue

data Paint : Color → Type
  | nil : Paint Color.red
  | mk (p : List (Paint Color.red)) : Paint Color.red

end

end MutualIxTest
