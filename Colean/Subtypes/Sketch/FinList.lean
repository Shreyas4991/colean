import Mathlib.Logic.Equiv.Defs
import Colean.Subtypes.Sketch.CoListLemmas

/-!
# `FinList`: the inductive type defined by the operator of `CoList`

```
inductive FinList (α) | nil | cons (a : α) (s : FinList α)
```

`IsFinList` is the least fixpoint (`inductive_fixpoint`) of the *same* one-step operator as
`CoList.IsCoList`; the only difference between the two definitions is the trailing keyword.

What the inductive subtype supports:

* an induction principle `induction`, from the generated `IsFinList.induct`;
* the inclusion into the coinductive type, `toCoList` (least fixpoint ≤ greatest fixpoint);
* recursion into data. `IsFinList` is a proposition, so `IsFinList.induct` only eliminates
  into `Prop`; functions into a `Type` are defined by well-founded recursion on the relation
  "is the tail of", whose well-foundedness is a `Prop` and so *is* proved by `induction`. This
  gives a general recursor `rec'` (through `WellFounded.fix`, so it does not reduce in the
  kernel) and computable functions written with `termination_by`, such as `toList`;
* the isomorphism `FinList α ≃ List α` with the native type.
-/

universe u v

open CoList

namespace CoList

variable {α : Type u}

/-- The least fixpoint of the operator of `IsCoList`. -/
def IsFinList (t : Raw ℕ (Shape α)) : Prop :=
  t = rawNil ∨ ∃ a s, t = rawCons a s ∧ IsFinList s
inductive_fixpoint

end CoList

/-- Finite lists, as the subtype of `Raw` cut out by the least fixpoint. -/
def FinList (α : Type u) : Type u := {t : Raw ℕ (CoList.Shape α) // CoList.IsFinList t}

namespace FinList

variable {α : Type u}

theorem isFinList_rawNil : IsFinList (rawNil : Raw ℕ (Shape α)) := by
  rw [IsFinList.eq_def]; exact Or.inl rfl

theorem isFinList_rawCons {a : α} {s : Raw ℕ (Shape α)} (h : IsFinList s) :
    IsFinList (rawCons a s) := by
  rw [IsFinList.eq_def]; exact Or.inr ⟨a, s, rfl, h⟩

/-- The empty list. -/
def nil : FinList α := ⟨rawNil, isFinList_rawNil⟩

/-- Prepend an element. -/
def cons (a : α) (s : FinList α) : FinList α := ⟨rawCons a s.1, isFinList_rawCons s.2⟩

@[simp] theorem nil_ne_cons (a : α) (s : FinList α) : nil ≠ cons a s := fun h =>
  rawNil_ne_rawCons a s.1 (congrArg Subtype.val h)

@[simp] theorem cons_ne_nil (a : α) (s : FinList α) : cons a s ≠ nil := (nil_ne_cons a s).symm

@[simp] theorem cons_inj {a a' : α} {s s' : FinList α} :
    cons a s = cons a' s' ↔ a = a' ∧ s = s' := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := rawCons_inj.mp (congrArg Subtype.val h)
    exact ⟨h₁, Subtype.ext h₂⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- Induction, from the generated `IsFinList.induct`. -/
theorem induction {motive : FinList α → Prop} (nil : motive nil)
    (cons : ∀ a s, motive s → motive (cons a s)) (s : FinList α) : motive s := by
  obtain ⟨t, ht⟩ := s
  refine (IsFinList.induct (fun t => ∃ h : IsFinList t, motive ⟨t, h⟩) ?_ t ht).elim fun _ h => h
  rintro t (rfl | ⟨a, s, rfl, hs, ih⟩)
  · exact ⟨isFinList_rawNil, nil⟩
  · exact ⟨isFinList_rawCons hs, cons a ⟨s, hs⟩ ih⟩

/-- Every finite list is a colist: the least fixpoint is below the greatest. -/
theorem isCoList_of_isFinList {t : Raw ℕ (Shape α)} (h : IsFinList t) : IsCoList t :=
  IsFinList.induct IsCoList (fun t h => IsCoList.eq_def t ▸ h) t h

/-- The inclusion of finite lists into colists. -/
def toCoList (s : FinList α) : CoList α := ⟨s.1, isCoList_of_isFinList s.2⟩

theorem toCoList_injective : Function.Injective (toCoList (α := α)) := fun _ _ h =>
  Subtype.ext (show (toCoList _).1 = (toCoList _).1 from congrArg Subtype.val h)

@[simp] theorem toCoList_nil : toCoList (nil : FinList α) = CoList.nil := rfl
@[simp] theorem toCoList_cons (a : α) (s : FinList α) :
    toCoList (cons a s) = CoList.cons a (toCoList s) := rfl

/-- Every finite list is `nil` or a `cons`. -/
theorem cases (s : FinList α) : s = nil ∨ ∃ a t, s = cons a t :=
  induction (motive := fun s => s = nil ∨ ∃ a t, s = cons a t) (Or.inl rfl)
    (fun a t _ => Or.inr ⟨a, t, rfl⟩) s

theorem isFinList_child_zero {t : Raw ℕ (Shape α)} (ht : IsFinList t) {a : α}
    (h : t.root = some (.cons a)) : IsFinList (t.child 0) := by
  rw [IsFinList.eq_def] at ht
  rcases ht with rfl | ⟨a', s, rfl, hs⟩
  · simp at h
  · simpa using hs

/-- The computable destructor. -/
def dest (s : FinList α) : Option (α × FinList α) :=
  match h : s.1.root with
  | some (.cons a) => some (a, ⟨s.1.child 0, isFinList_child_zero s.2 h⟩)
  | _ => none

@[simp] theorem dest_nil : dest (nil : FinList α) = none := rfl
@[simp] theorem dest_cons (a : α) (s : FinList α) : dest (cons a s) = some (a, s) := rfl

theorem dest_eq_none_iff {s : FinList α} : dest s = none ↔ s = nil := by
  rcases cases s with rfl | ⟨a, t, rfl⟩ <;> simp

theorem dest_eq_some_iff {s : FinList α} {a : α} {t : FinList α} :
    dest s = some (a, t) ↔ s = cons a t := by
  rcases cases s with rfl | ⟨a', t', rfl⟩ <;> simp

/-! ### Recursion into data -/

/-- `s` is the immediate tail of `t`. -/
def IsTail (s t : FinList α) : Prop := ∃ a, t = cons a s

theorem isTail_wf : WellFounded (IsTail (α := α)) :=
  ⟨induction (motive := Acc IsTail)
    (Acc.intro _ fun _ ⟨a, h⟩ => absurd h (nil_ne_cons a _))
    fun _ _ ih => Acc.intro _ fun _ ⟨_, h⟩ => (cons_inj.mp h).2 ▸ ih⟩

instance : WellFoundedRelation (FinList α) := ⟨IsTail, isTail_wf⟩

/-- The recursor into any `Sort`, by well-founded recursion. Being built from
`WellFounded.fix` it does not compute by `rfl`, only through `WellFounded.fix_eq`. -/
noncomputable def rec' {motive : FinList α → Sort v} (nil : motive nil)
    (cons : ∀ a s, motive s → motive (cons a s)) (s : FinList α) : motive s :=
  isTail_wf.fix
    (fun s ih =>
      match h : dest s with
      | none => (dest_eq_none_iff.mp h) ▸ nil
      | some (a, t) => (dest_eq_some_iff.mp h) ▸ cons a t (ih t ⟨a, dest_eq_some_iff.mp h⟩))
    s

theorem rec'_nil {motive : FinList α → Sort v} (nil : motive nil)
    (cons : ∀ a s, motive s → motive (cons a s)) : rec' nil cons FinList.nil = nil := by
  rw [rec', WellFounded.fix_eq]
  rfl

theorem rec'_cons {motive : FinList α → Sort v} (nil : motive nil)
    (cons : ∀ a s, motive s → motive (cons a s)) (a : α) (s : FinList α) :
    rec' nil cons (FinList.cons a s) = cons a s (rec' nil cons s) := by
  rw [rec', WellFounded.fix_eq]
  rfl

-- The linter does not see the use of `h` inside `decreasing_by`.
set_option linter.unusedVariables false in
/-- To a native list, by well-founded recursion on `IsTail`. Computable. -/
def toList (s : FinList α) : List α :=
  match h : dest s with
  | none => []
  | some (a, t) => a :: toList t
termination_by s
decreasing_by exact ⟨a, dest_eq_some_iff.mp h⟩

@[simp] theorem toList_nil : toList (nil : FinList α) = [] := by
  rw [toList]; rfl

@[simp] theorem toList_cons (a : α) (s : FinList α) : toList (cons a s) = a :: toList s := by
  rw [toList]; rfl

/-- From a native list. -/
def ofList : List α → FinList α
  | [] => nil
  | a :: l => cons a (ofList l)

theorem toList_ofList (l : List α) : toList (ofList l) = l := by
  induction l with
  | nil => simp [ofList]
  | cons a l ih => simp [ofList, ih]

theorem ofList_toList (s : FinList α) : ofList (toList s) = s := by
  refine induction (motive := fun s => ofList (toList s) = s) ?_ ?_ s
  · simp [ofList]
  · intro a s ih
    simp [ofList, ih]

/-- `FinList α` is the native `List α`. -/
def equivList : FinList α ≃ List α := ⟨toList, ofList, ofList_toList, toList_ofList⟩

/-- Well-founded recursion does not reduce in the kernel, so `decide` cannot check this; it is
proved by the computation rules instead, and evaluated by the compiler. -/
example : toList (ofList [1, 2, 3]) = [1, 2, 3] := by simp [ofList]

#eval toList (ofList [1, 2, 3])

end FinList
