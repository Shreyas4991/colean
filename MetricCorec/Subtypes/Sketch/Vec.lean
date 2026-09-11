import MetricCorec.Subtypes.Sketch.CoList

/-!
# `Vec`: an indexed family

The translation of

```
inductive Vec (α) : ℕ → Type
  | nil : Vec α 0
  | cons (a : α) (v : Vec α n) : Vec α (n + 1)
```

The index is an extra argument of the predicate: the fixpoint is taken over
`ℕ → Raw ℕ (Shape α) → Prop`, and each constructor says how it acts on the index. The raw
encoding is that of `CoList`, so `Vec α n` refines `FinList α` by its length. As for any
inductive type here, the recursor is the induction principle `Vec.induction`, obtained from the
generated `IsVec.induct`; case analysis follows the index (`eq_nil`, `exists_cons`).
-/

universe u

namespace Vec

open CoList (Shape rawNil rawCons)

variable {α : Type u}

/-- The predicate cutting vectors of length `n` out of `Raw`: the least fixpoint of the
one-step operator on indexed predicates. -/
def IsVec (n : ℕ) (t : Raw ℕ (Shape α)) : Prop :=
  (n = 0 ∧ t = rawNil) ∨ ∃ m a s, n = m + 1 ∧ t = rawCons a s ∧ IsVec m s
inductive_fixpoint

end Vec

/-- Vectors of length `n`. -/
def Vec (α : Type u) (n : ℕ) : Type u := {t : Raw ℕ (CoList.Shape α) // Vec.IsVec n t}

namespace Vec

open CoList (Shape rawNil rawCons)

variable {α : Type u} {n : ℕ}

/-- The empty vector. -/
def nil : Vec α 0 := ⟨rawNil, by rw [IsVec.eq_def]; exact Or.inl ⟨rfl, rfl⟩⟩

/-- Prepend an element. -/
def cons (a : α) (v : Vec α n) : Vec α (n + 1) :=
  ⟨rawCons a v.1, by rw [IsVec.eq_def]; exact Or.inr ⟨n, a, v.1, rfl, rfl, v.2⟩⟩

/-! ### The recursor -/

/-- Induction, with the index in the motive, from the generated `IsVec.induct`. -/
theorem induction {motive : ∀ n, Vec α n → Prop} (nil : motive 0 nil)
    (cons : ∀ n a (v : Vec α n), motive n v → motive (n + 1) (cons a v)) (n : ℕ) (v : Vec α n) :
    motive n v := by
  obtain ⟨t, ht⟩ := v
  refine (IsVec.induct (fun n t => ∃ h : IsVec n t, motive n ⟨t, h⟩) ?_ n t ht).elim fun _ h => h
  rintro n t (⟨rfl, rfl⟩ | ⟨m, a, s, rfl, rfl, hs, ih⟩)
  · exact ⟨_, nil⟩
  · exact ⟨_, cons m a ⟨s, hs⟩ ih⟩

/-! ### Case analysis follows the index -/

theorem eq_nil (v : Vec α 0) : v = nil := by
  obtain ⟨t, ht⟩ := v
  rw [IsVec.eq_def] at ht
  rcases ht with ⟨-, rfl⟩ | ⟨m, a, s, h, -⟩
  · rfl
  · exact absurd h (Nat.succ_ne_zero m).symm

theorem exists_cons (v : Vec α (n + 1)) : ∃ a w, v = cons a w := by
  obtain ⟨t, ht⟩ := v
  rw [IsVec.eq_def] at ht
  rcases ht with ⟨h, -⟩ | ⟨m, a, s, h, rfl, hs⟩
  · exact absurd h (Nat.succ_ne_zero n)
  · obtain rfl := Nat.succ.inj h
    exact ⟨a, ⟨s, hs⟩, rfl⟩

theorem root_eq (v : Vec α (n + 1)) : ∃ a, v.1.root = some (.cons a) := by
  obtain ⟨a, w, rfl⟩ := exists_cons v
  exact ⟨a, rfl⟩

/-- The head of a non-empty vector: computable, total thanks to the index. -/
def head (v : Vec α (n + 1)) : α :=
  match h : v.1.root with
  | some (.cons a) => a
  | some .nil => absurd h (by obtain ⟨a, ha⟩ := root_eq v; simp [ha])
  | none => absurd h (by obtain ⟨a, ha⟩ := root_eq v; simp [ha])

theorem isVec_child_zero (v : Vec α (n + 1)) : IsVec n (v.1.child 0) := by
  obtain ⟨a, w, rfl⟩ := exists_cons v
  exact w.2

/-- The tail of a non-empty vector. -/
def tail (v : Vec α (n + 1)) : Vec α n := ⟨v.1.child 0, isVec_child_zero v⟩

@[simp] theorem head_cons (a : α) (v : Vec α n) : head (cons a v) = a := rfl
@[simp] theorem tail_cons (a : α) (v : Vec α n) : tail (cons a v) = v := rfl

theorem cons_head_tail (v : Vec α (n + 1)) : cons (head v) (tail v) = v := by
  obtain ⟨a, w, rfl⟩ := exists_cons v
  rfl

end Vec
