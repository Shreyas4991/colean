import Colean.MutualCmd

/-! # Test: a mutual `datatype` block, finite rose trees -/

universe u

namespace DataTest.Mutual

noncomputable section

mutual
datatype Rose (α : Type u)
  | node (a : α) (children : Forest α)
datatype Forest (α : Type u)
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
#check @Rose_Forest.fold_cons
#check @Forest.rec_cons

/-- The number of nodes, by the folds per type: one algebra per type, as Lean's mutual
recursors have one motive per type. -/
def sizeRose {α : Type u} : Rose.F α Nat Nat → Nat
  | .node _ n => n + 1

def sizeForest {α : Type u} : Forest.F α Nat Nat → Nat
  | .nil => 0
  | .cons n k => n + k

def Rose.size {α : Type u} (t : Rose α) : Nat := Rose.fold sizeRose sizeForest t
def Forest.size {α : Type u} (f : Forest α) : Nat := Forest.fold sizeRose sizeForest f

@[simp] theorem Rose.size_node {α : Type u} (a : α) (c : Forest α) :
    (Rose.node a c).size = c.size + 1 := by
  simp [Rose.size, Forest.size, sizeRose]

@[simp] theorem Forest.size_nil {α : Type u} : (Forest.nil : Forest α).size = 0 := by
  simp [Forest.size, sizeForest]

@[simp] theorem Forest.size_cons {α : Type u} (t : Rose α) (f : Forest α) :
    (Forest.cons t f).size = t.size + f.size := by
  simp [Rose.size, Forest.size, sizeForest]

/-- The number of trees in a forest, by the fold over the block: one algebra for the block, over
`Rose_Forest.Ix`. -/
def lengthAlg {α : Type u} : ∀ m, Rose_Forest.F α (fun _ => Nat) m → Nat
  | .Rose, _ => 0
  | .Forest, .nil => 0
  | .Forest, .cons _ k => k + 1

def Forest.length {α : Type u} (f : Forest α) : Nat := Rose_Forest.fold lengthAlg f

@[simp] theorem Forest.length_nil {α : Type u} : (Forest.nil : Forest α).length = 0 := by
  simp [Forest.length, lengthAlg]

@[simp] theorem Forest.length_cons {α : Type u} (t : Rose α) (f : Forest α) :
    (Forest.cons t f).length = f.length + 1 := by
  simp [Forest.length, lengthAlg]

/-- Induction over the block: the motive is a family over `Ix`. -/
def LenLe {α : Type u} : ∀ m, Rose_Forest α m → Prop
  | .Rose, t => 1 ≤ Rose.size t
  | .Forest, f => Forest.length f ≤ Forest.size f

theorem lenLe {α : Type u} (m : Rose_Forest.Ix α) (x : Rose_Forest α m) : LenLe m x := by
  induction x with
  | node a c ih => simp [LenLe]
  | nil => simp [LenLe]
  | cons t f iht ihf => simp [LenLe] at *; omega

theorem Forest.length_le_size {α : Type u} (f : Forest α) : f.length ≤ f.size := lenLe .Forest f

/-! The recursors per type. -/

#check @Rose.rec
#check @Forest.rec
#check @Rose_Forest.rec_cons

/-- Induction per type: the motive of `Forest` is given, that of `Rose` comes from the goal. -/
theorem Rose.one_le_size {α : Type u} (t : Rose α) : 1 ≤ t.size := by
  induction t using Rose.rec (motive_2 := fun f => f.length ≤ f.size) with
  | node a c ih => simp
  | nil => simp
  | cons t f iht ihf => simp; omega

/-- The number of trees in a forest, by the recursor of `Forest`. -/
def Forest.count {α : Type u} (f : Forest α) : Nat :=
  Forest.rec (motive_1 := fun _ => Nat) (fun _ _ k => k) 0 (fun _ _ _ k => k + 1) f

example {α : Type u} (a b : α) :
    (Forest.cons (.node a .nil) (.cons (.node b .nil) .nil)).count = 2 := by
  simp [Forest.count]

/-- Case analysis per type. -/
theorem Rose.size_pos {α : Type u} (t : Rose α) : 0 < t.size := by
  cases t with
  | node a c => simp

end

end DataTest.Mutual
