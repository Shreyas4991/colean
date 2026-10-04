import Colean.Subtypes.Raw

/-!
# `Str`: the coinductive type and its corecursor

The translation of

```
coinductive Str (α) | cons (a : α) (s : Str α)
```

into a subtype of `Raw`, as in `CoList.lean`. The only constructor carries an `α`, so no
`Shape` type is needed: the labels of the raw trees are the elements themselves. A coalgebra is
just `S → α × S`, and `corec_eq` is `Subtype.ext` of `Raw.corecList_eq`.

`StrLemmas.lean` has head and tail, bisimulation, the isomorphism with `ℕ → α`, and the empty
inductive twin; `StrArith.lean` defines arithmetic by `partial_fixpoint` on `Raw`.
-/

universe u v

namespace Str

variable {α : Type u} {S : Type v}

/-- The raw encoding of `cons a s`: label `a`, single child `s`. -/
def rawCons (a : α) (s : Raw ℕ α) : Raw ℕ α := Raw.node a [s]

/-- The predicate cutting streams out of `Raw`: the greatest fixpoint of the one-step
operator. -/
def IsStr (t : Raw ℕ α) : Prop :=
  ∃ a s, t = rawCons a s ∧ IsStr s
coinductive_fixpoint

end Str

/-- Streams. -/
def Str (α : Type u) : Type u := {t : Raw ℕ α // Str.IsStr t}

namespace Str

variable {α : Type u} {S : Type v}

/-- Prepend an element. -/
def cons (a : α) (s : Str α) : Str α :=
  ⟨rawCons a s.1, by rw [IsStr.eq_def]; exact ⟨a, s.1, rfl, s.2⟩⟩

/-! ### The corecursor -/

/-- The unfoldings of a coalgebra are streams. -/
theorem isStr_corecList (f : S → α × S) (s : S) :
    IsStr (Raw.corecList (fun s => ((f s).1, [(f s).2])) s) := by
  refine IsStr.coinduct (fun t => ∃ s, t = Raw.corecList (fun s => ((f s).1, [(f s).2])) s) ?_ _
    ⟨s, rfl⟩
  rintro _ ⟨s, rfl⟩
  exact ⟨(f s).1, _, Raw.corecList_eq _ s, (f s).2, rfl⟩

/-- Corecursion into streams. -/
def corec (f : S → α × S) (s : S) : Str α :=
  ⟨Raw.corecList (fun s => ((f s).1, [(f s).2])) s, isStr_corecList f s⟩

/-- The specification of the corecursor. -/
theorem corec_eq (f : S → α × S) (s : S) : corec f s = cons (f s).1 (corec f (f s).2) :=
  Subtype.ext (Raw.corecList_eq _ s)

end Str
