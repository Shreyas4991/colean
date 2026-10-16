import Colean.MutualCmd

/-! # Test: a mutual `data` block, finite rose trees -/

universe u

namespace DataTest.Mutual

noncomputable section

mutual
data Rose (α : Type u)
  | node (a : α) (children : Forest α)
data Forest (α : Type u)
  | nil
  | cons (t : Rose α) (f : Forest α)
end

#check @Rose_Forest.F.cons
#check @Rose.node
#check @Rose.fold
#check @Rose_Forest.rec
#check @Rose.casesOn
#check @Forest.casesOn
#check @Rose.fold_node
#check @Forest.rec_cons
-- Each type of the block is a container in the parameter.
#check @Rose.occ
#check @Forest.occ

/-- One algebra for the block: the number of nodes. -/
def sizeAlg {α : Type u} : ∀ m, Rose_Forest.F α (fun _ => Nat) m → Nat
  | .Rose, .node _ n => n + 1
  | .Forest, .nil => 0
  | .Forest, .cons n k => n + k

def Rose.size {α : Type u} (t : Rose α) : Nat := Rose.fold sizeAlg t
def Forest.size {α : Type u} (f : Forest α) : Nat := Forest.fold sizeAlg f

@[simp] theorem Rose.size_node {α : Type u} (a : α) (c : Forest α) :
    (Rose.node a c).size = c.size + 1 := by
  simp [Rose.size, Forest.size, sizeAlg]

@[simp] theorem Forest.size_nil {α : Type u} : (Forest.nil : Forest α).size = 0 := by
  simp [Forest.size, sizeAlg]

@[simp] theorem Forest.size_cons {α : Type u} (t : Rose α) (f : Forest α) :
    (Forest.cons t f).size = t.size + f.size := by
  simp [Rose.size, Forest.size, sizeAlg]

/-- The number of trees in a forest. -/
def lengthAlg {α : Type u} : ∀ m, Rose_Forest.F α (fun _ => Nat) m → Nat
  | .Rose, _ => 0
  | .Forest, .nil => 0
  | .Forest, .cons _ k => k + 1

def Forest.length {α : Type u} (f : Forest α) : Nat := Forest.fold lengthAlg f

@[simp] theorem Forest.length_nil {α : Type u} : (Forest.nil : Forest α).length = 0 := by
  simp [Forest.length, lengthAlg]

@[simp] theorem Forest.length_cons {α : Type u} (t : Rose α) (f : Forest α) :
    (Forest.cons t f).length = f.length + 1 := by
  simp [Forest.length, lengthAlg]

/-- Induction over the block: the motive is a family over `Which`. -/
def LenLe {α : Type u} : ∀ m, Rose_Forest α m → Prop
  | .Rose, t => 1 ≤ Rose.size t
  | .Forest, f => Forest.length f ≤ Forest.size f

theorem lenLe {α : Type u} (m : Rose_Forest.Which) (x : Rose_Forest α m) : LenLe m x := by
  induction x with
  | node a c ih => simp [LenLe]
  | nil => simp [LenLe]
  | cons t f iht ihf => simp [LenLe] at *; omega

theorem Forest.length_le_size {α : Type u} (f : Forest α) : f.length ≤ f.size := lenLe .Forest f

/-- Case analysis per type. -/
theorem Rose.size_pos {α : Type u} (t : Rose α) : 0 < t.size := by
  cases t with
  | node a c => simp

end

end DataTest.Mutual
