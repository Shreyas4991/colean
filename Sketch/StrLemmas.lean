import Mathlib.Logic.Equiv.Defs
import Sketch.Str

/-!
# What `Str` supports beyond its corecursor

Injectivity of `cons`, case analysis, computable `head` and `tail`, bisimulation `eq_of_bisim`,
the isomorphism `Str α ≃ (ℕ → α)`, and the observation that the least fixpoint of the same
operator is empty (`not_isFinStr`), exactly as the native `inductive` with this signature
would be.
-/

universe u v

namespace Str

variable {α : Type u} {S : Type v}

/-! ### The raw constructor -/

@[simp] theorem root_rawCons (a : α) (s : Raw ℕ α) : (rawCons a s).root = some a := rfl
@[simp] theorem child_rawCons_zero (a : α) (s : Raw ℕ α) : (rawCons a s).child 0 = s := rfl
@[simp] theorem child_rawCons_succ (a : α) (s : Raw ℕ α) (i : ℕ) :
    (rawCons a s).child (i + 1) = Raw.empty := by
  cases i <;> rfl

@[simp] theorem rawCons_inj {a a' : α} {s s' : Raw ℕ α} :
    rawCons a s = rawCons a' s' ↔ a = a' ∧ s = s' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg Raw.root h, by simpa using congrArg (Raw.child · 0) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-! ### Constructor, case analysis, head and tail -/

@[simp] theorem cons_inj {a a' : α} {s s' : Str α} : cons a s = cons a' s' ↔ a = a' ∧ s = s' := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := rawCons_inj.mp (congrArg Subtype.val h)
    exact ⟨h₁, Subtype.ext h₂⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem cases (s : Str α) : ∃ a t, s = cons a t := by
  obtain ⟨t, ht⟩ := s
  rw [IsStr.eq_def] at ht
  obtain ⟨a, t', rfl, ht'⟩ := ht
  exact ⟨a, ⟨t', ht'⟩, rfl⟩

theorem root_ne_none {t : Raw ℕ α} (ht : IsStr t) : t.root ≠ none := by
  rw [IsStr.eq_def] at ht
  obtain ⟨a, s, rfl, -⟩ := ht
  simp

theorem isStr_child_zero {t : Raw ℕ α} (ht : IsStr t) : IsStr (t.child 0) := by
  rw [IsStr.eq_def] at ht
  obtain ⟨a, s, rfl, hs⟩ := ht
  simpa using hs

/-- The head: the root label, which the predicate guarantees to exist. -/
def head (s : Str α) : α :=
  match h : s.1.root with
  | some a => a
  | none => absurd h (root_ne_none s.2)

/-- The tail: the first child. -/
def tail (s : Str α) : Str α := ⟨s.1.child 0, isStr_child_zero s.2⟩

@[simp] theorem head_cons (a : α) (s : Str α) : head (cons a s) = a := rfl
@[simp] theorem tail_cons (a : α) (s : Str α) : tail (cons a s) = s := rfl

@[simp] theorem cons_head_tail (s : Str α) : cons (head s) (tail s) = s := by
  obtain ⟨a, t, rfl⟩ := cases s
  rfl

@[simp] theorem head_corec (f : S → α × S) (s : S) : head (corec f s) = (f s).1 := by
  rw [corec_eq, head_cons]

@[simp] theorem tail_corec (f : S → α × S) (s : S) : tail (corec f s) = corec f (f s).2 := by
  rw [corec_eq, tail_cons]

/-! ### Bisimulation -/

theorem eq_of_bisim (R : Str α → Str α → Prop)
    (H : ∀ s₁ s₂, R s₁ s₂ → head s₁ = head s₂ ∧ R (tail s₁) (tail s₂))
    {s₁ s₂ : Str α} (h : R s₁ s₂) : s₁ = s₂ := by
  apply Subtype.ext
  refine Raw.eq_of_bisim' (R := fun t₁ t₂ => ∃ s₁ s₂ : Str α, t₁ = s₁.1 ∧ t₂ = s₂.1 ∧ R s₁ s₂)
    ?_ ⟨s₁, s₂, rfl, rfl, h⟩
  rintro _ _ ⟨s₁, s₂, rfl, rfl, h⟩
  obtain ⟨hh, ht⟩ := H s₁ s₂ h
  obtain ⟨a₁, t₁, rfl⟩ := cases s₁
  obtain ⟨a₂, t₂, rfl⟩ := cases s₂
  simp only [head_cons, tail_cons] at hh ht
  subst hh
  refine ⟨rfl, fun i => ?_⟩
  cases i with
  | zero => exact Or.inr ⟨t₁, t₂, rfl, rfl, ht⟩
  | succ i => exact Or.inl rfl

/-! ### The isomorphism with `ℕ → α` -/

/-- The `n`-th element. -/
def get (s : Str α) : ℕ → α
  | 0 => head s
  | n + 1 => get (tail s) n

@[simp] theorem get_zero (s : Str α) : get s 0 = head s := rfl
@[simp] theorem get_succ (s : Str α) (n : ℕ) : get s (n + 1) = get (tail s) n := rfl

/-- A function on `ℕ` as a stream, by corecursion. -/
def ofFun (f : ℕ → α) : Str α := corec (fun f => (f 0, fun n => f (n + 1))) f

@[simp] theorem head_ofFun (f : ℕ → α) : head (ofFun f) = f 0 := head_corec _ _
@[simp] theorem tail_ofFun (f : ℕ → α) : tail (ofFun f) = ofFun fun n => f (n + 1) := tail_corec _ _

theorem get_ofFun (f : ℕ → α) : get (ofFun f) = f := by
  funext n
  induction n generalizing f with
  | zero => simp
  | succ n ih => simp [ih]

theorem ofFun_get (s : Str α) : ofFun (get s) = s := by
  refine eq_of_bisim (fun s₁ s₂ => s₁ = ofFun (get s₂)) ?_ rfl
  rintro _ s rfl
  exact ⟨by simp, by simp⟩

/-- `Str α` is `ℕ → α`. -/
def equivFun : Str α ≃ (ℕ → α) := ⟨get, ofFun, ofFun_get, get_ofFun⟩

/-- The stream `a, f a, f (f a), …`, and its specification without positions. -/
def iterate (f : α → α) (a : α) : Str α := corec (fun x => (x, f x)) a

theorem iterate_eq (f : α → α) (a : α) : iterate f a = cons a (iterate f (f a)) := corec_eq _ _

/-- Streams compute in the kernel. -/
example : get (iterate Nat.succ 0) 5 = 5 := by decide

/-! ### The inductive twin is empty -/

/-- The least fixpoint of the operator of `IsStr`. -/
def IsFinStr (t : Raw ℕ α) : Prop :=
  ∃ a s, t = rawCons a s ∧ IsFinStr s
inductive_fixpoint

/-- Without a base case the least fixpoint is empty. -/
theorem not_isFinStr (t : Raw ℕ α) : ¬ IsFinStr t :=
  IsFinStr.induct (fun _ => False) (fun _ ⟨_, _, _, h⟩ => h) t

end Str
