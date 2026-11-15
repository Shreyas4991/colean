import Mathlib.Data.Seq.Defs
import Mathlib.Logic.Equiv.Defs
import Sketch.CoList

open Codata

-- Lean 4.34 compares implicit arguments and metavariable types without unfolding definitions.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# What `CoList` supports beyond its corecursor

* injectivity and disjointness of constructors, inherited from `Raw.node`;
* case analysis (`cases`) and a computable destructor `dest`, read off `IsCoList.eq_def`;
* bisimulation `eq_of_bisim`, inherited from `Raw.eq_of_bisim'`;
* examples that compute in the kernel (`take`, `iterate`, `map`);
* the isomorphism `CoList α ≃ Stream'.Seq α` with Mathlib's sequences.
-/

universe u v

open Raw

namespace CoList

variable {α : Type u} {β : Type v} {S : Type v}

/-! ### The raw constructors -/

@[simp] theorem root_rawNil : (rawNil : Raw ℕ (Shape α)).root = some .nil := rfl
@[simp] theorem child_rawNil (i : ℕ) : (rawNil : Raw ℕ (Shape α)).child i = empty := by
  cases i <;> rfl
@[simp] theorem root_rawCons (a : α) (s : Raw ℕ (Shape α)) :
    (rawCons a s).root = some (.cons a) := rfl
@[simp] theorem child_rawCons_zero (a : α) (s : Raw ℕ (Shape α)) : (rawCons a s).child 0 = s := rfl
@[simp] theorem child_rawCons_succ (a : α) (s : Raw ℕ (Shape α)) (i : ℕ) :
    (rawCons a s).child (i + 1) = empty := by
  cases i <;> rfl

@[simp] theorem rawNil_ne_rawCons (a : α) (s : Raw ℕ (Shape α)) : rawNil ≠ rawCons a s := by
  intro h; simpa using congrArg root h

@[simp] theorem rawCons_inj {a a' : α} {s s' : Raw ℕ (Shape α)} :
    rawCons a s = rawCons a' s' ↔ a = a' ∧ s = s' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg root h, by simpa using congrArg (child · 0) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-! ### Constructors -/

@[simp] theorem val_nil : (nil : CoList α).1 = rawNil := rfl
@[simp] theorem val_cons (a : α) (s : CoList α) : (cons a s).1 = rawCons a s.1 := rfl

@[simp] theorem nil_ne_cons (a : α) (s : CoList α) : nil ≠ cons a s := fun h =>
  rawNil_ne_rawCons a s.1 (congrArg Subtype.val h)

@[simp] theorem cons_ne_nil (a : α) (s : CoList α) : cons a s ≠ nil := (nil_ne_cons a s).symm

@[simp] theorem cons_inj {a a' : α} {s s' : CoList α} :
    cons a s = cons a' s' ↔ a = a' ∧ s = s' := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := rawCons_inj.mp (congrArg Subtype.val h)
    exact ⟨h₁, Subtype.ext h₂⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-! ### Case analysis and the destructor -/

/-- Every colist is `nil` or a `cons`: the unfolding of the predicate, read through the
subtype. -/
theorem cases (s : CoList α) : s = nil ∨ ∃ a t, s = cons a t := by
  obtain ⟨t, ht⟩ := s
  rw [IsCoList.eq_def] at ht
  rcases ht with rfl | ⟨a, t', rfl, ht'⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨a, ⟨t', ht'⟩, rfl⟩

/-- Case analysis as an eliminator into `Prop`. -/
theorem casesOn' {motive : CoList α → Prop} (s : CoList α) (nil : motive nil)
    (cons : ∀ a t, motive (cons a t)) : motive s := by
  rcases cases s with rfl | ⟨a, t, rfl⟩
  · exact nil
  · exact cons a t

theorem isCoList_child_zero {t : Raw ℕ (Shape α)} (ht : IsCoList t) {a : α}
    (h : t.root = some (.cons a)) : IsCoList (t.child 0) := by
  rw [IsCoList.eq_def] at ht
  rcases ht with rfl | ⟨a', s, rfl, hs⟩
  · simp at h
  · simpa using hs

/-- The computable destructor: look at the root label and, for a `cons`, return the first
child together with the proof that it is a colist. -/
def dest (s : CoList α) : Option (α × CoList α) :=
  match h : s.1.root with
  | some (.cons a) => some (a, ⟨s.1.child 0, isCoList_child_zero s.2 h⟩)
  | _ => none

@[simp] theorem dest_nil : dest (nil : CoList α) = none := rfl
@[simp] theorem dest_cons (a : α) (s : CoList α) : dest (cons a s) = some (a, s) := rfl

theorem dest_eq_none_iff {s : CoList α} : dest s = none ↔ s = nil := by
  rcases cases s with rfl | ⟨a, t, rfl⟩ <;> simp

theorem dest_eq_some_iff {s : CoList α} {a : α} {t : CoList α} :
    dest s = some (a, t) ↔ s = cons a t := by
  rcases cases s with rfl | ⟨a', t', rfl⟩ <;> simp

/-- The head, if any. -/
def head (s : CoList α) : Option α := (dest s).map Prod.fst

/-- The tail, or `nil`. -/
def tail (s : CoList α) : CoList α := ((dest s).map Prod.snd).getD nil

@[simp] theorem head_cons (a : α) (s : CoList α) : head (cons a s) = some a := rfl
@[simp] theorem tail_cons (a : α) (s : CoList α) : tail (cons a s) = s := rfl

@[simp] theorem dest_corec (f : S → Option (α × S)) (s : S) :
    dest (corec f s) = (f s).map fun p => (p.1, corec f p.2) := by
  rw [corec_eq]
  rcases f s with _ | ⟨a, s'⟩ <;> simp

/-! ### Bisimulation -/

/-- Two colists related by a bisimulation are equal. Inherited from `Raw.eq_of_bisim'`: the
children beyond the first are `empty` on both sides, and are handled by the `Eq` disjunct. -/
theorem eq_of_bisim (R : CoList α → CoList α → Prop)
    (H : ∀ s₁ s₂, R s₁ s₂ →
      (s₁ = nil ∧ s₂ = nil) ∨ ∃ a t₁ t₂, s₁ = cons a t₁ ∧ s₂ = cons a t₂ ∧ R t₁ t₂)
    {s₁ s₂ : CoList α} (h : R s₁ s₂) : s₁ = s₂ := by
  apply Subtype.ext
  refine Raw.eq_of_bisim' (R := fun t₁ t₂ => ∃ s₁ s₂ : CoList α, t₁ = s₁.1 ∧ t₂ = s₂.1 ∧ R s₁ s₂)
    ?_ ⟨s₁, s₂, rfl, rfl, h⟩
  rintro _ _ ⟨s₁, s₂, rfl, rfl, h⟩
  rcases H s₁ s₂ h with ⟨rfl, rfl⟩ | ⟨a, t₁, t₂, rfl, rfl, h'⟩
  · exact ⟨rfl, fun _ => Or.inl rfl⟩
  · refine ⟨rfl, fun i => ?_⟩
    cases i with
    | zero => exact Or.inr ⟨t₁, t₂, rfl, rfl, h'⟩
    | succ i => exact Or.inl rfl

/-! ### Examples -/

/-- The first `n` elements. -/
def take : ℕ → CoList α → List α
  | 0, _ => []
  | n + 1, s =>
    match dest s with
    | none => []
    | some (a, t) => a :: take n t

/-- The infinite colist `a, f a, f (f a), …`. -/
def iterate (f : α → α) (a : α) : CoList α := corec (fun x => some (x, f x)) a

/-- Map, by corecursion. -/
def map (f : α → β) (s : CoList α) : CoList β :=
  corec (fun s => (dest s).map fun p => (f p.1, p.2)) s

/-- Colists compute in the kernel. -/
example : take 5 (iterate Nat.succ 0) = [0, 1, 2, 3, 4] := by decide
example : take 5 (map (· * 2) (iterate Nat.succ 0)) = [0, 2, 4, 6, 8] := by decide

theorem iterate_eq (f : α → α) (a : α) : iterate f a = cons a (iterate f (f a)) := by
  rw [iterate, corec_eq]; rfl

@[simp] theorem map_nil (f : α → β) : map f nil = nil := by
  rw [map, corec_eq]; rfl

@[simp] theorem map_cons (f : α → β) (a : α) (s : CoList α) :
    map f (cons a s) = cons (f a) (map f s) := by
  rw [map, corec_eq]; rfl

theorem map_id (s : CoList α) : map id s = s := by
  refine eq_of_bisim (fun s₁ s₂ => s₁ = map id s₂) ?_ rfl
  rintro _ s rfl
  rcases cases s with rfl | ⟨a, t, rfl⟩
  · simp
  · exact Or.inr ⟨a, map id t, t, by simp, rfl, rfl⟩

/-! ### The isomorphism with Mathlib's `Seq` -/

/-- Colists to Mathlib's sequences, by Mathlib's corecursion. -/
def toSeq (s : CoList α) : Stream'.Seq α := Stream'.Seq.corec dest s

/-- Mathlib's sequences to colists, by our corecursion. -/
def ofSeq (s : Stream'.Seq α) : CoList α := corec Stream'.Seq.destruct s

theorem ofSeq_toSeq (s : CoList α) : ofSeq (toSeq s) = s := by
  refine eq_of_bisim (fun s₁ s₂ => s₁ = ofSeq (toSeq s₂)) ?_ rfl
  rintro _ s rfl
  rcases cases s with rfl | ⟨a, t, rfl⟩
  · left
    refine ⟨dest_eq_none_iff.mp ?_, rfl⟩
    simp [ofSeq, toSeq]
  · right
    refine ⟨a, ofSeq (toSeq t), t, dest_eq_some_iff.mp ?_, rfl, rfl⟩
    simp [ofSeq, toSeq]

theorem toSeq_ofSeq (s : Stream'.Seq α) : toSeq (ofSeq s) = s := by
  refine Stream'.Seq.eq_of_bisim' (fun s₁ s₂ => s₁ = toSeq (ofSeq s₂)) rfl ?_
  rintro _ s rfl
  rcases hs : Stream'.Seq.destruct s with _ | ⟨a, t⟩
  · left
    refine ⟨Stream'.Seq.destruct_eq_none ?_, Stream'.Seq.destruct_eq_none hs⟩
    simp [ofSeq, toSeq, hs]
  · right
    refine ⟨a, toSeq (ofSeq t), t, Stream'.Seq.destruct_eq_cons ?_, Stream'.Seq.destruct_eq_cons hs,
      rfl⟩
    simp [ofSeq, toSeq, hs]

/-- `CoList α` is Mathlib's `Seq α`. -/
def equivSeq : CoList α ≃ Stream'.Seq α := ⟨toSeq, ofSeq, ofSeq_toSeq, toSeq_ofSeq⟩

end CoList
