import Init.Internal.Order.Basic
import MetricCorec.Subtypes.Sketch.StrLemmas

/-!
# `partial_fixpoint` on the general type, coinduction on the subtype

Up to its structure wrapper, `Raw I L` is `List I → Option L`, whose `CCPO` structure
`partial_fixpoint` already knows: the flat order on `Option L`, pointwise. So corecursive
definitions can be written with `partial_fixpoint` on `Raw` with no bespoke order (compare
`MetricCorec.Order.SeqCCPO`, which builds one by hand for `Seq`), and get transported to the
subtypes once the coinduction principle of the predicate shows that they stay inside it.

* `Raw.instCCPO`: the order transported from `List I → Option L`; `Raw.empty` is the bottom.
* `Str.addRaw` on `Raw ℕ ℕ` is pointwise, hence monotone (`Str.addRaw_mono`); this is what lets
  recursive occurrences sit under `add`.
* `Str.mulRaw` is defined with `partial_fixpoint`, its recursive occurrences under `addRaw`.
  `Str.isStr_mulRaw` proves by coinduction that it sends streams to streams. Its one-step
  unfolding piles up `add`s, so the relation used is the closure of the images of `mulRaw` under
  `addRaw` (`Str.AddClosure`): this is coinduction up to `add`, `Str.isStr_coinduct_upto_add`,
  proved once from `IsStr.coinduct`. Fixpoint induction cannot prove productivity (see
  `not_admissible_of_infinite` in `MetricCorec.Order.Stream`), and here it is not needed.
* `Str.add` and `Str.mul` on `Str ℕ` are the transports, specified by their unfoldings
  `Str.add_cons_cons` and `Str.mul_cons_cons`, with no positions in sight.
-/

universe u v

open Lean.Order

namespace Raw

variable {I : Type u} {L : Type v}

/-- The order of `List I → Option L`: `t₁ ⊑ t₂` if `t₂` agrees with `t₁` wherever `t₁` is
defined. -/
instance instPartialOrder : Lean.Order.PartialOrder (Raw I L) where
  rel t₁ t₂ := t₁.get ⊑ t₂.get
  rel_refl := Lean.Order.PartialOrder.rel_refl
  rel_trans := Lean.Order.PartialOrder.rel_trans
  rel_antisymm h₁ h₂ := ext (congrFun (Lean.Order.PartialOrder.rel_antisymm h₁ h₂))

theorem rel_iff {t₁ t₂ : Raw I L} : t₁ ⊑ t₂ ↔ ∀ p, t₁.get p ⊑ t₂.get p := Iff.rfl

/-- The chain-complete structure, transported from `List I → Option L`. -/
noncomputable instance instCCPO : CCPO (Raw I L) where
  has_csup {c} hc := by
    obtain ⟨f, hf⟩ := CCPO.has_csup (c := fun f : List I → Option L => c ⟨f⟩)
      (fun f g hf hg => hc _ _ hf hg)
    exact ⟨⟨f⟩, fun t => ⟨fun h y hy => (hf t.get).mp h y.get hy,
      fun h => (hf t.get).mpr fun g hg => h ⟨g⟩ hg⟩⟩

@[simp] theorem empty_le (t : Raw I L) : empty ⊑ t := fun _ => FlatOrder.rel.bot

theorem bot_eq_empty : (Lean.Order.bot : Raw I L) = empty :=
  Lean.Order.PartialOrder.rel_antisymm (bot_le _) (empty_le _)

end Raw

namespace Str

/-- `rawCons a` is monotone in the tail, so recursive occurrences may appear under it. -/
@[partial_fixpoint_monotone]
theorem rawCons_mono {L : Type u} {β : Sort v} [Lean.Order.PartialOrder β] (a : L) (f : β → Raw ℕ L)
    (hf : monotone f) : monotone fun x => rawCons a (f x) := by
  intro x y hxy p
  match p with
  | [] => exact FlatOrder.rel.refl
  | 0 :: p => exact hf x y hxy p
  | (_ + 1) :: _ => exact FlatOrder.rel.bot

/-! ### Pointwise addition -/

/-- Addition on optional values, defined where both are. -/
def addOpt : Option ℕ → Option ℕ → Option ℕ
  | some a, some b => some (a + b)
  | _, _ => none

theorem addOpt_mono {u₁ u₂ v₁ v₂ : Option ℕ} (hu : u₁ ⊑ u₂) (hv : v₁ ⊑ v₂) :
    addOpt u₁ v₁ ⊑ addOpt u₂ v₂ := by
  cases hu with
  | bot => exact FlatOrder.rel.bot
  | refl =>
    cases hv with
    | bot => cases u₁ <;> exact FlatOrder.rel.bot
    | refl => exact FlatOrder.rel.refl

/-- Pointwise addition on `Raw ℕ ℕ`. -/
def addRaw (x y : Raw ℕ ℕ) : Raw ℕ ℕ := ⟨fun p => addOpt (x.get p) (y.get p)⟩

@[simp] theorem get_addRaw (x y : Raw ℕ ℕ) (p : List ℕ) :
    (addRaw x y).get p = addOpt (x.get p) (y.get p) := rfl

theorem addRaw_rawCons_rawCons (a b : ℕ) (x y : Raw ℕ ℕ) :
    addRaw (rawCons a x) (rawCons b y) = rawCons (a + b) (addRaw x y) :=
  Raw.ext fun p => match p with
    | [] => rfl
    | 0 :: _ => rfl
    | (_ + 1) :: _ => rfl

/-- `addRaw` is monotone in both arguments. -/
@[partial_fixpoint_monotone]
theorem addRaw_mono {β : Sort v} [Lean.Order.PartialOrder β] (f g : β → Raw ℕ ℕ) (hf : monotone f)
    (hg : monotone g) : monotone fun x => addRaw (f x) (g x) :=
  fun x y hxy p => addOpt_mono (hf x y hxy p) (hg x y hxy p)

/-! ### Multiplication by `partial_fixpoint` -/

/-- The product of two streams, as in `MetricCorec.Order.SeqAddMul`: the recursive occurrences
sit under `addRaw`. Defined on the general type by `partial_fixpoint`; on inputs that are not
streams it may be partial, which is what makes the fixpoint exist. -/
def mulRaw (x y : Raw ℕ ℕ) : Raw ℕ ℕ :=
  match x.root, y.root with
  | some a, some b => rawCons (a * b) (addRaw (mulRaw x (y.child 0)) (mulRaw (x.child 0) y))
  | _, _ => Raw.empty
partial_fixpoint

theorem mulRaw_rawCons_rawCons (a b : ℕ) (x y : Raw ℕ ℕ) :
    mulRaw (rawCons a x) (rawCons b y) =
      rawCons (a * b) (addRaw (mulRaw (rawCons a x) y) (mulRaw x (rawCons b y))) :=
  (mulRaw.eq_def _ _).trans rfl

/-! ### Productivity, by coinduction up to `add` -/

/-- The closure of a predicate under `addRaw`. -/
inductive AddClosure (P : Raw ℕ ℕ → Prop) : Raw ℕ ℕ → Prop
  | base {t} : P t → AddClosure P t
  | add {s t} : AddClosure P s → AddClosure P t → AddClosure P (addRaw s t)

/-- Coinduction up to `add`: a predicate whose one-step unfolding lands in its `add`-closure
consists of streams. -/
theorem isStr_coinduct_upto_add (P : Raw ℕ ℕ → Prop)
    (H : ∀ t, P t → ∃ a s, t = rawCons a s ∧ AddClosure P s) {t : Raw ℕ ℕ} (ht : P t) :
    IsStr t := by
  refine IsStr.coinduct (AddClosure P) ?_ t (.base ht)
  intro t h
  induction h with
  | base h => exact H _ h
  | add _ _ ihs iht =>
    obtain ⟨a, s', rfl, hs'⟩ := ihs
    obtain ⟨b, t', rfl, ht'⟩ := iht
    exact ⟨a + b, addRaw s' t', addRaw_rawCons_rawCons a b s' t', .add hs' ht'⟩

theorem isStr_addRaw {x y : Raw ℕ ℕ} (hx : IsStr x) (hy : IsStr y) : IsStr (addRaw x y) := by
  refine IsStr.coinduct (fun t => ∃ x y, IsStr x ∧ IsStr y ∧ t = addRaw x y) ?_ _
    ⟨x, y, hx, hy, rfl⟩
  rintro _ ⟨x, y, hx, hy, rfl⟩
  rw [IsStr.eq_def] at hx hy
  obtain ⟨a, x', rfl, hx'⟩ := hx
  obtain ⟨b, y', rfl, hy'⟩ := hy
  exact ⟨a + b, addRaw x' y', addRaw_rawCons_rawCons a b x' y', x', y', hx', hy', rfl⟩

/-- `mulRaw` sends streams to streams. The predicate is the set of products of streams, and its
unfolding is an `add` of two products, so coinduction up to `add` applies. -/
theorem isStr_mulRaw {x y : Raw ℕ ℕ} (hx : IsStr x) (hy : IsStr y) : IsStr (mulRaw x y) := by
  refine isStr_coinduct_upto_add (fun t => ∃ x y, IsStr x ∧ IsStr y ∧ t = mulRaw x y) ?_
    ⟨x, y, hx, hy, rfl⟩
  rintro _ ⟨x, y, hx, hy, rfl⟩
  have hx' := hx
  have hy' := hy
  rw [IsStr.eq_def] at hx' hy'
  obtain ⟨a, x', rfl, hx''⟩ := hx'
  obtain ⟨b, y', rfl, hy''⟩ := hy'
  exact ⟨a * b, _, mulRaw_rawCons_rawCons a b x' y',
    .add (.base ⟨_, _, hx, hy'', rfl⟩) (.base ⟨_, _, hx'', hy, rfl⟩)⟩

/-! ### The transport to `Str ℕ` -/

/-- Addition of streams. -/
def add (x y : Str ℕ) : Str ℕ := ⟨addRaw x.1 y.1, isStr_addRaw x.2 y.2⟩

/-- Multiplication of streams. -/
noncomputable def mul (x y : Str ℕ) : Str ℕ := ⟨mulRaw x.1 y.1, isStr_mulRaw x.2 y.2⟩

theorem add_cons_cons (a b : ℕ) (x y : Str ℕ) :
    add (cons a x) (cons b y) = cons (a + b) (add x y) :=
  Subtype.ext (addRaw_rawCons_rawCons a b x.1 y.1)

theorem mul_cons_cons (a b : ℕ) (x y : Str ℕ) :
    mul (cons a x) (cons b y) = cons (a * b) (add (mul (cons a x) y) (mul x (cons b y))) :=
  Subtype.ext (mulRaw_rawCons_rawCons a b x.1 y.1)

@[simp] theorem head_add (x y : Str ℕ) : head (add x y) = head x + head y := by
  obtain ⟨a, x, rfl⟩ := cases x
  obtain ⟨b, y, rfl⟩ := cases y
  rw [add_cons_cons]; rfl

@[simp] theorem tail_add (x y : Str ℕ) : tail (add x y) = add (tail x) (tail y) := by
  obtain ⟨a, x, rfl⟩ := cases x
  obtain ⟨b, y, rfl⟩ := cases y
  rw [add_cons_cons]; rfl

theorem get_add (x y : Str ℕ) (n : ℕ) : get (add x y) n = get x n + get y n := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih => simp [ih]

theorem add_comm (x y : Str ℕ) : add x y = add y x := by
  refine eq_of_bisim (fun s₁ s₂ => ∃ x y, s₁ = add x y ∧ s₂ = add y x) ?_ ⟨x, y, rfl, rfl⟩
  rintro _ _ ⟨x, y, rfl, rfl⟩
  exact ⟨by simp [Nat.add_comm], tail x, tail y, by simp, by simp⟩

end Str
