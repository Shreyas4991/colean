import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Forall2
import Colean.Raw

/-!
# `CoList`: the coinductive type and its corecursor

The translation of

```
coinductive CoList (α) | nil | cons (a : α) (s : CoList α)
```

into a subtype of `Raw`:

1. `Shape α` holds the non-recursive data of each constructor; the raw constructors are
   `Raw.node`s carrying that data, with the recursive arguments as children.
2. `IsCoList` is the greatest fixpoint (`coinductive_fixpoint`) of the one-step operator
   `P ↦ fun t => t = rawNil ∨ ∃ a s, t = rawCons a s ∧ P s`.
3. `CoList α` is the subtype; its constructors are the raw ones, with the proofs read off the
   unfolding lemma `IsCoList.eq_def`.
4. The corecursor `corec` is `Raw.corecList`, and `IsCoList.coinduct` proves that its image lies
   in the subtype. Its specification is `corec_eq`.

`CoListLemmas.lean` has the destructor, case analysis, bisimulation, examples and the
isomorphism with Mathlib's `Seq`; `FinList.lean` has the inductive type defined by the same
operator.
-/

open Codata

universe u v

/-- The non-recursive data of each constructor. -/
inductive CoList.Shape (α : Type u)
  | nil
  | cons (a : α)

namespace CoList

variable {α : Type u} {S : Type v}

/-- The raw encoding of `nil`. -/
def rawNil : Raw ℕ (Shape α) := Raw.node .nil []

/-- The raw encoding of `cons a s`. -/
def rawCons (a : α) (s : Raw ℕ (Shape α)) : Raw ℕ (Shape α) := Raw.node (.cons a) [s]

/-- The predicate cutting colists out of `Raw`: the greatest fixpoint of the one-step
operator. -/
def IsCoList (t : Raw ℕ (Shape α)) : Prop :=
  t = rawNil ∨ ∃ a s, t = rawCons a s ∧ IsCoList s
coinductive_fixpoint

end CoList

/-- Potentially infinite lists. -/
def CoList (α : Type u) : Type u := {t : Raw ℕ (CoList.Shape α) // CoList.IsCoList t}

namespace CoList

variable {α : Type u} {S : Type v}

/-- The empty colist. -/
def nil : CoList α := ⟨rawNil, by rw [IsCoList.eq_def]; exact Or.inl rfl⟩

/-- Prepend an element. -/
def cons (a : α) (s : CoList α) : CoList α :=
  ⟨rawCons a s.1, by rw [IsCoList.eq_def]; exact Or.inr ⟨a, s.1, rfl, s.2⟩⟩

/-! ### The corecursor -/

/-- A coalgebra `S → Option (α × S)` as a `Raw.corecList` coalgebra: constructor data and the
list of recursive states. -/
def coalg (f : S → Option (α × S)) (s : S) : Shape α × List S :=
  match f s with
  | none => (.nil, [])
  | some (a, s') => (.cons a, [s'])

/-- The unfoldings of a coalgebra are colists: coinduction with `R` the set of all unfoldings. -/
theorem isCoList_corecList (f : S → Option (α × S)) (s : S) :
    IsCoList (Raw.corecList (coalg f) s) := by
  refine IsCoList.coinduct (fun t => ∃ s, t = Raw.corecList (coalg f) s) ?_ _ ⟨s, rfl⟩
  rintro _ ⟨s, rfl⟩
  rw [Raw.corecList_eq]
  rcases hf : f s with _ | ⟨a, s'⟩
  · exact Or.inl (by simp [coalg, hf, rawNil])
  · exact Or.inr ⟨a, _, by simp [coalg, hf, rawCons], s', rfl⟩

/-- Corecursion into colists. -/
def corec (f : S → Option (α × S)) (s : S) : CoList α :=
  ⟨Raw.corecList (coalg f) s, isCoList_corecList f s⟩

/-- The specification of the corecursor. -/
theorem corec_eq (f : S → Option (α × S)) (s : S) :
    corec f s = match f s with
      | none => nil
      | some (a, s') => cons a (corec f s') := by
  apply Subtype.ext
  show Raw.corecList (coalg f) s = _
  rw [Raw.corecList_eq]
  rcases hf : f s with _ | ⟨a, s'⟩ <;> simp [coalg, hf, rawNil, rawCons, nil, cons, corec]

end CoList
