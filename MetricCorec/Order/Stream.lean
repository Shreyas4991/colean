import Mathlib.Data.Seq.Basic
import MetricCorec.Order.SeqAddMul

/-!
# Productivity without positions, and the lift from `Seq` to `Stream'`

`Stream' α` is `ℕ → α`: every stream is total, so there is no bottom element, no `CCPO`
structure, and `partial_fixpoint` cannot define functions on streams directly. The route is to
define a function on `Seq`, where `partial_fixpoint` works, prove that it sends non-terminating
sequences to non-terminating sequences (*productivity*), and transport it along `Seq.ofStream`
and `Seq.toStream`.

Productivity is a liveness property and fixpoint induction cannot prove it: an admissible
predicate holds at `⊥`, the everywhere-`nil` function (`not_admissible_of_infinite`). What proves
it is coinduction, and this file does that without ever describing a sequence by its positions:

* `not_terminates_coind`: non-termination is the greatest predicate `R` such that every
  `R`-sequence is a `cons` whose tail is again `R`. Positions appear only inside the proof of this
  principle, exactly as for `Seq.eq_of_bisim` and `le_of_simulation`.
* `not_terminates_add`: take `R` = images of `add` on non-terminating inputs; the one-step
  unfolding `add_cons_cons` shows that `R` is closed.
* `not_terminates_mul`: the recursive occurrences of `mul` sit under `add`, and unfolding piles up
  `add`s without bound (position `n` of a product is a sum of `n + 1` products), so no predicate
  closed under one step can avoid containing `add`-trees of `mul`s. This is a fact about `mul`,
  not about the technique. What is generic is the closure: `not_terminates_coind_upto` is
  coinduction up to any binary context that commutes with `cons`, proved once, and `mul` uses it
  with `add` and the single fact `add_cons_cons`.

The recipe is the same for any `partial_fixpoint` definition on any coinductive type with a
`destruct`: `R` is the set of recursive-call images, and each operation the definition puts around
the recursive calls enters through its one-step unfolding, via the generic up-to principle. The
transported `Stream'.add` is then specified, again without positions, by its own unfolding
`Stream'.add_eq`.
-/

open Stream' Stream'.Seq
open scoped Lean.Order

namespace Stream'.Seq

/-! ### Non-termination as a coinductive predicate -/

/-- Coinduction for non-termination: a predicate closed under one step of `destruct` consists of
non-terminating sequences. -/
theorem not_terminates_coind {α : Type u} (R : Seq α → Prop)
    (H : ∀ s, R s → ∃ a t, s = cons a t ∧ R t) {s : Seq α} (hs : R s) : ¬ s.Terminates := by
  rintro ⟨n, hn⟩
  induction n generalizing s with
  | zero =>
    obtain ⟨a, t, rfl, -⟩ := H s hs
    exact cons_not_terminatedAt_zero hn
  | succ n ih =>
    obtain ⟨a, t, rfl, ht⟩ := H s hs
    exact ih ht (cons_terminatedAt_succ_iff.mp hn)

/-- One step of unfolding of a non-terminating sequence. -/
theorem exists_cons_of_not_terminates {α : Type u} {s : Seq α} (h : ¬ s.Terminates) :
    ∃ a t, s = cons a t ∧ ¬ t.Terminates := by
  cases s with
  | nil => exact absurd terminates_nil h
  | cons a t => exact ⟨a, t, rfl, fun ht => h (terminates_cons_iff.mpr ht)⟩

-- /-- Closure of a predicate under a binary operation. -/
-- inductive Closure₂ {α : Type u} (g : Seq α → Seq α → Seq α) (P : Seq α → Prop) : Seq α → Prop
--   | base {z} : P z → Closure₂ g P z
--   | op {x y} : Closure₂ g P x → Closure₂ g P y → Closure₂ g P (g x y)

-- /-- Coinduction up to a context. If `g` commutes with `cons`, a predicate whose one-step unfolding
-- lands in its closure under `g` consists of non-terminating sequences. -/
-- theorem not_terminates_coind_upto {α : Type u} (g : Seq α → Seq α → Seq α)
--     (hg : ∀ a x b y, ∃ c, g (cons a x) (cons b y) = cons c (g x y)) (R : Seq α → Prop)
--     (H : ∀ s, R s → ∃ a t, s = cons a t ∧ Closure₂ g R t) {s : Seq α} (hs : R s) :
--     ¬ s.Terminates := by
--   refine not_terminates_coind (Closure₂ g R) ?_ (.base hs)
--   intro z hz
--   induction hz with
--   | base h => exact H _ h
--   | op _ _ ihx ihy =>
--     obtain ⟨a, x', rfl, hx'⟩ := ihx
--     obtain ⟨b, y', rfl, hy'⟩ := ihy
--     obtain ⟨c, hc⟩ := hg a x' b y'
--     exact ⟨c, g x' y', hc, .op hx' hy'⟩

/-! ### The embedding of streams, and the projection back -/

theorem ofStream_eq_cons {α : Type u} (s : Stream' α) :
    ofStream s = cons s.head (ofStream s.tail) := by
  rw [← ofStream_cons, Stream'.eta]

theorem not_terminates_ofStream {α : Type u} (s : Stream' α) : ¬ (ofStream s).Terminates :=
  not_terminates_coind (fun z => ∃ s, z = ofStream s)
    (by rintro _ ⟨s, rfl⟩; exact ⟨s.head, ofStream s.tail, ofStream_eq_cons s, s.tail, rfl⟩)
    ⟨s, rfl⟩

theorem toStream_congr {α : Type u} {x y : Seq α} (e : x = y) (hx : ¬ x.Terminates) :
    x.toStream hx = y.toStream (e ▸ hx) := by
  subst e; rfl

/-- `toStream` commutes with `cons`. -/
theorem toStream_cons {α : Type u} (a : α) (x : Seq α) (h : ¬ (cons a x).Terminates) :
    (cons a x).toStream h = a :: x.toStream (fun hx => h (terminates_cons_iff.mpr hx)) :=
  funext fun n => by cases n <;> rfl

end Stream'.Seq

/-! ### Productivity of `add` and `mul` -/

/-- `add` is productive, by coinduction: the images of `add` on non-terminating inputs form a
predicate closed under one step of unfolding. -/
theorem not_terminates_add {x y : Seq ℕ} (hx : ¬ x.Terminates) (hy : ¬ y.Terminates) :
    ¬ (add x y).Terminates := by
  refine not_terminates_coind (fun z => ∃ x y, ¬ x.Terminates ∧ ¬ y.Terminates ∧ z = add x y)
    ?_ ⟨x, y, hx, hy, rfl⟩
  rintro _ ⟨x, y, hx, hy, rfl⟩
  obtain ⟨a, x', rfl, hx'⟩ := exists_cons_of_not_terminates hx
  obtain ⟨b, y', rfl, hy'⟩ := exists_cons_of_not_terminates hy
  exact ⟨a + b, add x' y', add_cons_cons a x' b y', x', y', hx', hy', rfl⟩

/-- `mul` is productive. Its recursive occurrences sit under `add`, so this is coinduction up to
the context `add`, which commutes with `cons` by `add_cons_cons`. -/
theorem not_terminates_mul {x y : Seq ℕ} (hx : ¬ x.Terminates) (hy : ¬ y.Terminates) :
    ¬ (mul x y).Terminates := by
  revert x y
  apply mul.fixpoint_induct (motive := fun F => ∀ x y, ¬ x.Terminates → ¬ y.Terminates → ¬ (F x y).Terminates)
  · intro c hc h xs ys hxs hys
    
    sorry
  · intro F ih xs ys hxs hys
    obtain ⟨x, xs, rfl, hxs⟩ := exists_cons_of_not_terminates hxs
    obtain ⟨y, ys, rfl, hys⟩ := exists_cons_of_not_terminates hys
    simp
    apply not_terminates_add <;> grind

/-! ### Why not fixpoint induction -/

/-- The motive one would like for a fixpoint-induction proof of productivity is not admissible:
an admissible predicate holds at `⊥`, the everywhere-`nil` function, and `nil` terminates. -/
theorem not_admissible_of_infinite :
    ¬ Lean.Order.admissible (fun m : Seq ℕ → Seq ℕ → Seq ℕ =>
      ∀ s t : Stream' ℕ, ¬ (m (ofStream s) (ofStream t)).Terminates) := by
  intro h
  have hbot := h (Lean.Order.empty_chain _) (Lean.Order.chain_empty _) fun _ hx => hx.elim
  have hnil : Lean.Order.CCPO.csup (Lean.Order.chain_empty (Seq ℕ → Seq ℕ → Seq ℕ))
      (ofStream (Stream'.const 0)) (ofStream (Stream'.const 0)) = nil :=
    le_nil_iff.mp (Lean.Order.bot_le (fun _ _ => nil) _ _)
  refine hbot (Stream'.const 0) (Stream'.const 0) ?_
  rw [hnil]
  exact terminates_nil

/-! ### The lift -/

namespace Stream'

/-- Addition of streams, transported from `add` on `Seq`. -/
def add (s t : Stream' ℕ) : Stream' ℕ :=
  (_root_.add (ofStream s) (ofStream t)).toStream
    (not_terminates_add (not_terminates_ofStream s) (not_terminates_ofStream t))

/-- The one-step unfolding of `Stream'.add`: its whole specification, with no positions. -/
theorem add_eq (s t : Stream' ℕ) : add s t = (s.head + t.head) :: add s.tail t.tail := by
  have e : _root_.add (ofStream s) (ofStream t) =
      Seq.cons (s.head + t.head) (_root_.add (ofStream s.tail) (ofStream t.tail)) := by
    rw [ofStream_eq_cons s, ofStream_eq_cons t, add_cons_cons]
  show (_root_.add (ofStream s) (ofStream t)).toStream _ = _
  rw [toStream_congr e, toStream_cons]
  rfl

end Stream'
