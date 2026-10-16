/-!
# Failing example: a `mutual` block mixing `inductive_fixpoint` and `coinductive_fixpoint`

Self-contained, on streams of bits `Nat → Bool`. Not imported by `Colean.lean`.

1. Both coinductive, both inductive: accepted (and the two fixpoints differ: the inductive pair
   is empty).
2. Mixed: rejected, with

   ```
   Could not prove 'MixedFail.Fair' to be monotone in its recursive calls:
     Cannot eliminate recursive call in Eventually (tl s)
   ```

   A `mutual` block is one fixpoint of the joint operator on pairs of predicates, and Lean can
   only take the least fixpoint for the implication order or the greatest for the reverse
   order, of an operator monotone for that order. With `Fair` in the reverse order and
   `Eventually` in the implication order, the body of `Fair` is not monotone (raising
   `Eventually` raises `Fair` the wrong way), and the extremal fixpoint of any single order
   would not be the intended predicate anyway.
3. What a mixed block means is a *nested* fixpoint, and there are two of them. Both are written
   out below: `Fair` (coinductive outside, `EventuallyOf` inside) is the intended one, non-empty;
   `Eventually'` (inductive outside) is empty. Nesting is composition: the inner fixpoint is a
   function of the outer predicate, and the outer definition may recurse through it only given
   a monotonicity lemma tagged `@[partial_fixpoint_monotone]`.
-/

universe v

namespace MixedFail

abbrev Stream := Nat → Bool

/-- The tail of a stream. -/
def tl (s : Stream) : Stream := fun n => s (n + 1)

/-! ### Both coinductive: accepted. `Alt₀ s`: `s` alternates `false, true, false, …`. -/

mutual
def Alt₀ (s : Stream) : Prop := s 0 = false ∧ Alt₁ (tl s)
coinductive_fixpoint
def Alt₁ (s : Stream) : Prop := s 0 = true ∧ Alt₀ (tl s)
coinductive_fixpoint
end

#check @Alt₀.coinduct

/-! ### Both inductive: accepted, but empty: no finite derivation exists. -/

mutual
def AltInd₀ (s : Stream) : Prop := s 0 = false ∧ AltInd₁ (tl s)
inductive_fixpoint
def AltInd₁ (s : Stream) : Prop := s 0 = true ∧ AltInd₀ (tl s)
inductive_fixpoint
end

#check @AltInd₀.mutual_induct

theorem altInd_empty : (∀ s, ¬ AltInd₀ s) ∧ (∀ s, ¬ AltInd₁ s) :=
  AltInd₀.mutual_induct (fun _ => False) (fun _ => False) (fun _ h => h.2) (fun _ h => h.2)

/-! ### Mixed: rejected.

Intended meaning: `Fair s` says `s` is `false` now and, after finitely many `true`s, fair
again; that is, infinitely many `false`s with finite runs of `true`s between them. -/

mutual
  def Fair (s : Stream) : Prop := s 0 = false ∧ Eventually (tl s)
  coinductive_fixpoint
  def Eventually (s : Stream) : Prop := Fair s ∨ (s 0 = true ∧ Eventually (tl s))
  inductive_fixpoint
  -- inductive Eventually (s : Stream)
  -- | fair (h : Fair s)
  -- | next (h0 : s 0 = true) (h1 : Eventually (tl s))
end

/-! ### The intended reading as a nested fixpoint: coinductive outside. -/

/-- After finitely many `true`s, `P`: the least fixpoint, parameterised by `P`. -/
def EventuallyOf (P : Stream → Prop) (s : Stream) : Prop :=
  P s ∨ (s 0 = true ∧ EventuallyOf P (tl s))
inductive_fixpoint

open Lean.Order in
/-- Monotone in `P` for the order of coinductive definitions; this is what lets a greatest
fixpoint recurse through it. -/
@[partial_fixpoint_monotone]
theorem eventuallyOf_mono {β : Sort v} [PartialOrder β] (P : β → Stream → ReverseImplicationOrder)
    (hP : monotone P) (s : Stream) :
    @monotone _ _ _ ReverseImplicationOrder.instOrder (fun x => EventuallyOf (P x) s) :=
  fun x y hxy h => by
    refine EventuallyOf.induct (P y) (EventuallyOf (P x)) ?_ s h
    intro s hs
    rw [EventuallyOf.eq_def]
    rcases hs with hs | ⟨hr, hs'⟩
    · exact Or.inl (hP x y hxy s hs)
    · exact Or.inr ⟨hr, hs'⟩

/-- Infinitely many `false`s, finite runs of `true`s. -/
def Fair' (s : Stream) : Prop := s 0 = false ∧ EventuallyOf Fair' (tl s)
coinductive_fixpoint

#check @Fair'.coinduct

/-- Non-empty: the constant `false` stream is fair. -/
theorem fair'_const : Fair' fun _ => false :=
  Fair'.coinduct (fun s => s = fun _ => false)
    (fun _ h => by subst h; exact ⟨rfl, by rw [EventuallyOf.eq_def]; exact Or.inl rfl⟩) _ rfl

def Eventually' (s : Stream) : Prop := Fair' s ∨ (s 0 = true ∧ Eventually' (tl s))
inductive_fixpoint

-- inductive Eventually (s : Stream)
-- | fair (h : Fair s)
-- | next (h0 : s 0 = true) (h1 : Eventually (tl s))

#check Fair'.coinduct

#check Eventually'.induct

-- s := [1, 1, 0, 0, ..]
-- pred := allZero


-- s := [1, 0] :: s
-- pred s := 0 ∈ s

-- example :


-- /-! ### The other nesting: inductive outside. Empty. -/

-- /-- `μ Q. FairOf Q ∨ (s 0 = true ∧ Q (tl s))`, where `FairOf Q := ν P. (s 0 = false ∧ Q (tl s))`
-- is just `s 0 = false ∧ Q (tl s)`, since that body does not mention `P`. Written inline. -/
-- def Eventually' (s : Stream) : Prop :=
--   (s 0 = false ∧ Eventually' (tl s)) ∨ (s 0 = true ∧ Eventually' (tl s))
-- inductive_fixpoint


-- #check Eventually'.induct

-- /-- Every derivation would have to be infinite. -/
-- theorem eventually'_empty (s : Stream) : ¬ Eventually' s :=
--   Eventually'.induct (fun _ => False) (fun _ h => h.elim (·.2) (·.2)) s

end MixedFail
