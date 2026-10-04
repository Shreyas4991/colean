import Colean.Subtypes.CodataCmd

/-! # Test: an indexed family, `Vec` -/

universe u

namespace CodataTest

noncomputable section

codata Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

#check @Vec.cons
#check @Vec.dtor
#check @Vec.corec
#check @Vec.bisim
#check @Vec.casesOn
#check @Vec.B.cons_v

/-- The constant vector, by corecursion over the index. -/
def Vec.const {α : Type u} (a : α) (n : Nat) : Vec α n :=
  Vec.corec (S := fun _ => Unit) (fun n _ => match n with
    | 0 => .nil
    | _ + 1 => .cons a ()) ()

@[simp] theorem Vec.dtor_const_zero {α : Type u} (a : α) : (Vec.const a 0).dtor = .nil := by
  simp [Vec.const, Vec.dtor_corec]

@[simp] theorem Vec.dtor_const_succ {α : Type u} (a : α) (n : Nat) :
    (Vec.const a (n + 1)).dtor = .cons a (Vec.const a n) := by
  simp [Vec.const, Vec.dtor_corec]

/-- The head and the tail of a non-empty vector: the index forces the constructor, so the
`match` needs no `nil` case. -/
def Vec.head {α : Type u} {n : Nat} (v : Vec α (n + 1)) : α :=
  match v.dtor with
  | .cons a _ => a

def Vec.tail {α : Type u} {n : Nat} (v : Vec α (n + 1)) : Vec α n :=
  match v.dtor with
  | .cons _ v => v

@[simp] theorem Vec.head_cons {α : Type u} {n : Nat} (a : α) (v : Vec α n) :
    (Vec.cons a v).head = a := by
  simp [Vec.head]

@[simp] theorem Vec.tail_cons {α : Type u} {n : Nat} (a : α) (v : Vec α n) :
    (Vec.cons a v).tail = v := by
  simp [Vec.tail]

example {α : Type u} (a : α) (n : Nat) : (Vec.const a (n + 1)).head = a := by
  rw [← Vec.ctor_dtor (Vec.const a (n + 1)), Vec.dtor_const_succ, Vec.ctor_cons, Vec.head_cons]

/-! ### Lists and vectors -/

/-- The elements of a vector, by recursion on the index. -/
def Vec.toList {α : Type u} : ∀ {n : Nat}, Vec α n → List α
  | 0, _ => []
  | _ + 1, v => v.head :: v.tail.toList

/-- The vector of a list. -/
def Vec.ofList {α : Type u} : (l : List α) → Vec α l.length
  | [] => .nil
  | a :: l => .cons a (Vec.ofList l)

@[simp] theorem Vec.toList_nil {α : Type u} : (Vec.nil : Vec α 0).toList = [] := rfl

@[simp] theorem Vec.toList_cons {α : Type u} {n : Nat} (a : α) (v : Vec α n) :
    (Vec.cons a v).toList = a :: v.toList := by
  simp [Vec.toList]

@[simp] theorem Vec.ofList_nil {α : Type u} : Vec.ofList ([] : List α) = Vec.nil := rfl

@[simp] theorem Vec.ofList_cons {α : Type u} (a : α) (l : List α) :
    Vec.ofList (a :: l) = Vec.cons a (Vec.ofList l) := rfl

theorem Vec.toList_ofList {α : Type u} (l : List α) : (Vec.ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem Vec.length_toList {α : Type u} {n : Nat} (v : Vec α n) : v.toList.length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases v with
    | cons a v => simp [ih]

/-- `cons` respects heterogeneous equality of tails, given that the lengths agree. -/
theorem Vec.cons_heq {α : Type u} {m n : Nat} (h : m = n) (a : α) {v : Vec α m} {w : Vec α n}
    (hvw : HEq v w) : HEq (Vec.cons a v) (Vec.cons a w) := by
  subst h
  cases hvw
  rfl

/-- The other direction of the inverse, up to the equality of the lengths. -/
theorem Vec.ofList_toList {α : Type u} {n : Nat} (v : Vec α n) :
    HEq (Vec.ofList v.toList) v := by
  induction n with
  | zero =>
    cases v with
    | nil => exact HEq.rfl
  | succ n ih =>
    cases v with
    | cons a v =>
      have h : HEq (Vec.ofList (Vec.cons a v).toList) (Vec.ofList (a :: v.toList)) := by
        rw [Vec.toList_cons]
      exact h.trans (Vec.cons_heq (Vec.length_toList v) a (ih v))

/-- The same as an equality, with the cast made explicit. -/
def Vec.cast {α : Type u} {m n : Nat} (h : m = n) (v : Vec α m) : Vec α n := h ▸ v

theorem Vec.cast_heq {α : Type u} {m n : Nat} (h : m = n) (v : Vec α m) : HEq (v.cast h) v := by
  subst h
  rfl

theorem Vec.ofList_toList' {α : Type u} {n : Nat} (v : Vec α n) :
    Vec.ofList v.toList = v.cast (Vec.length_toList v).symm :=
  eq_of_heq ((Vec.ofList_toList v).trans (Vec.cast_heq _ v).symm)

/-- Every vector of length 0 is `nil`: case analysis on the index refines the cases. -/
example {α : Type u} (v : Vec α 0) : v = Vec.nil := by
  cases v with
  | nil => rfl

/-- Vectors are determined by their elements: two constant vectors agree, by bisimulation. -/
example {α : Type u} (a : α) (n : Nat) :
    Vec.const a n = Vec.corec (fun (n : Nat) (_ : Unit) => match n with
      | 0 => .nil
      | _ + 1 => .cons a ()) () := by
  refine Vec.bisim (fun n x y => x = Vec.const a n ∧ y = Vec.corec (fun (n : Nat) (_ : Unit) =>
    match n with | 0 => .nil | _ + 1 => .cons a ()) ()) ?_ ⟨rfl, rfl⟩
  rintro n x y ⟨rfl, rfl⟩
  cases n with
  | zero => simp [Vec.dtor_corec]; constructor
  | succ n => simp [Vec.dtor_corec]; exact .cons _ _ _ ⟨rfl, rfl⟩

end

end CodataTest
