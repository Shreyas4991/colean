import Colean.Subtypes.DataCmd

/-! # Test: `data`, an indexed family; and the same family as `codata`, which is the same type -/

universe u

namespace DataTest

noncomputable section

data FinVec (α : Type u) : Nat → Type u
  | nil : FinVec α 0
  | cons {n : Nat} (a : α) (v : FinVec α n) : FinVec α (n + 1)

#check @FinVec.cons
#check @FinVec.fold
#check @FinVec.rec
#check @FinVec.rec_cons
#check @FinVec.casesOn

/-- The elements, by the fold into a constant family. -/
def FinVec.toList {α : Type u} {n : Nat} (v : FinVec α n) : List α :=
  FinVec.fold (S := fun _ => List α) (fun _ y => match y with | .nil => [] | .cons a l => a :: l) v

@[simp] theorem FinVec.toList_nil {α : Type u} : (FinVec.nil : FinVec α 0).toList = [] := by
  simp [FinVec.toList]

@[simp] theorem FinVec.toList_cons {α : Type u} {n : Nat} (a : α) (v : FinVec α n) :
    (FinVec.cons a v).toList = a :: v.toList := by
  simp [FinVec.toList]

/-- The index is the length: induction over the family. -/
theorem FinVec.length_toList {α : Type u} {n : Nat} (v : FinVec α n) : v.toList.length = n := by
  induction v with
  | nil => simp
  | cons a v ih => simp [ih]

def FinVec.ofList {α : Type u} : (l : List α) → FinVec α l.length
  | [] => .nil
  | a :: l => .cons a (ofList l)

theorem FinVec.toList_ofList {α : Type u} (l : List α) : (FinVec.ofList l).toList = l := by
  induction l with
  | nil => simp [FinVec.ofList]
  | cons a l ih => simp [FinVec.ofList, ih]

/-- The head, by case analysis: the index rules out `nil`. -/
def FinVec.head {α : Type u} {n : Nat} (v : FinVec α (n + 1)) : α :=
  FinVec.casesOn (motive := fun m _ => m = n + 1 → α) v (fun h => nomatch h) (fun a _ _ => a) rfl

@[simp] theorem FinVec.head_cons {α : Type u} {n : Nat} (a : α) (v : FinVec α n) :
    (FinVec.cons a v).head = a := by
  simp [FinVec.head]

/-- A vector of length zero is `nil`. -/
example {α : Type u} (v : FinVec α 0) : v = FinVec.nil := by
  cases v with
  | nil => rfl

/-! ### The same declaration as `codata`

The index decreases along every recursive argument, so a coinductive vector of length `n`
unfolds exactly `n` times: `CoVec α n` and `FinVec α n` are the same type. The contract is the
coinductive one: `corec` from a coalgebra over the index, `bisim` for relations over the index;
here both are bounded by `n`, and the equivalence with `FinVec` is proved by induction on `n`. -/

codata CoVec (α : Type u) : Nat → Type u
  | nil : CoVec α 0
  | cons {n : Nat} (a : α) (v : CoVec α n) : CoVec α (n + 1)

#check @CoVec.corec
#check @CoVec.dtor_corec
#check @CoVec.bisim
#check @CoVec.F.Rel.cons

/-- A coalgebra over the index: the state at `n + 1` produces a `cons` whose tail is a state at
`n`. The constant vector. -/
def CoVec.const {α : Type u} (a : α) (n : Nat) : CoVec α n :=
  CoVec.corec (S := fun _ => Unit) (fun n _ => match n with
    | 0 => .nil
    | _ + 1 => .cons a ()) ()

@[simp] theorem CoVec.dtor_const_succ {α : Type u} (a : α) (n : Nat) :
    (CoVec.const a (n + 1)).dtor = .cons a (CoVec.const a n) := by
  simp [CoVec.const, CoVec.dtor_corec]

/-- Finite vectors are coinductive vectors: the fold into the coinductive family. -/
def FinVec.toCo {α : Type u} {n : Nat} (v : FinVec α n) : CoVec α n :=
  FinVec.fold (S := CoVec α)
    (fun _ y => match y with | .nil => CoVec.nil | .cons a w => CoVec.cons a w) v

@[simp] theorem FinVec.toCo_nil {α : Type u} : (FinVec.nil : FinVec α 0).toCo = CoVec.nil := by
  simp [FinVec.toCo]

@[simp] theorem FinVec.toCo_cons {α : Type u} {n : Nat} (a : α) (v : FinVec α n) :
    (FinVec.cons a v).toCo = CoVec.cons a v.toCo := by
  simp [FinVec.toCo]

/-- Coinductive vectors are finite: recursion on the index, one destructor step each. -/
def CoVec.toFin {α : Type u} : ∀ {n : Nat}, CoVec α n → FinVec α n
  | 0, _ => .nil
  | _ + 1, v => match v.dtor with | .cons a w => .cons a (CoVec.toFin w)

@[simp] theorem CoVec.toFin_nil {α : Type u} (v : CoVec α 0) : v.toFin = FinVec.nil := rfl

@[simp] theorem CoVec.toFin_cons {α : Type u} {n : Nat} (a : α) (v : CoVec α n) :
    (CoVec.cons a v).toFin = FinVec.cons a v.toFin := by
  simp [CoVec.toFin]

theorem FinVec.toFin_toCo {α : Type u} {n : Nat} (v : FinVec α n) : v.toCo.toFin = v := by
  induction v with
  | nil => simp
  | cons a v ih => simp [ih]

/-- The other composite, by induction on the index: at `n + 1` the vector is a `cons` of its
head and tail (`ctor_dtor`), and the tail is at `n`. -/
theorem CoVec.toCo_toFin {α : Type u} : ∀ {n : Nat} (v : CoVec α n), v.toFin.toCo = v
  | 0, v => by cases v with | nil => simp
  | n + 1, v => by
    cases v with
    | cons a w => simp [CoVec.toCo_toFin w]

/-- `CoVec α n ≃ FinVec α n`. -/
def CoVec.equivFin {α : Type u} (n : Nat) : CoVec α n ≃ FinVec α n :=
  ⟨CoVec.toFin, FinVec.toCo, CoVec.toCo_toFin, FinVec.toFin_toCo⟩

@[simp] theorem CoVec.dtor_const_zero {α : Type u} (a : α) : (CoVec.const a 0).dtor = .nil := by
  simp [CoVec.const, CoVec.dtor_corec]

def FinVec.replicate {α : Type u} (a : α) : (n : Nat) → FinVec α n
  | 0 => .nil
  | n + 1 => .cons a (replicate a n)

/-- `bisim`: a relation indexed by `n`, and one destructor step per index; for this family it
is induction on the index in disguise, since a bisimulation at `n + 1` only ever needs the
relation at `n`. -/
example {α : Type u} (a : α) (n : Nat) : CoVec.const a n = (FinVec.replicate a n).toCo := by
  refine CoVec.bisim (fun n x y => x = CoVec.const a n ∧ y = (FinVec.replicate a n).toCo) ?_
    ⟨rfl, rfl⟩
  rintro n _ _ ⟨rfl, rfl⟩
  cases n with
  | zero => simp [FinVec.replicate]; exact .nil
  | succ n => simp [FinVec.replicate]; exact .cons a _ _ ⟨rfl, rfl⟩

end

end DataTest
