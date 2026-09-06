import Init.Internal.Order.Basic
import Mathlib.Data.Countable.Defs

namespace Lean.Order

variable {α : Type} [PartialOrder α]

/-- The **down-set completion** of a partial order `α`: the downward-closed predicates on `α`,
ordered by inclusion.

This is a complete lattice — the supremum of any family is its union — so in particular every chain
has a least upper bound and it is a `CCPO`. The original order embeds into it via principal
down-sets (`Completion.of`), and that embedding reflects and preserves `⊑`. -/
def Completion (α : Type) [PartialOrder α] : Type :=
  { S : α → Prop // ∀ ⦃x y : α⦄, x ⊑ y → S y → S x }

namespace Completion

/-- Down-sets ordered by inclusion. -/
instance : PartialOrder (Completion α) where
  rel S T := ∀ a, S.1 a → T.1 a
  rel_refl _ h := h
  rel_trans hST hTU a ha := hTU a (hST a ha)
  rel_antisymm hST hTS := Subtype.ext (funext fun a => propext ⟨hST a, hTS a⟩)

theorem le_def {S T : Completion α} : S ⊑ T ↔ ∀ a, S.1 a → T.1 a := Iff.rfl

/-- The union of a family of down-sets, again a down-set. -/
def sUnion (c : Completion α → Prop) : Completion α :=
  ⟨fun a => ∃ S, c S ∧ S.1 a, fun _ _ hxy => fun ⟨S, hS, hSy⟩ => ⟨S, hS, S.2 hxy hSy⟩⟩

/-- The union is the least upper bound of any family: down-sets form a complete lattice, so every
family — in particular every chain — has a supremum. -/
theorem isSup_sUnion (c : Completion α → Prop) : is_sup c (sUnion c) := by
  intro T
  constructor
  · intro hsup S hS a ha
    exact hsup a ⟨S, hS, ha⟩
  · rintro h a ⟨S, hS, hSa⟩
    exact h S hS a hSa

/-- The down-set completion is a `CCPO` (indeed a complete lattice): suprema of chains are unions.
The empty chain's supremum is the empty down-set, the required bottom element. -/
instance : CCPO (Completion α) where
  has_csup {_} _ := ⟨sUnion _, isSup_sUnion _⟩

/-- The principal down-set embedding `α ↪ Completion α`, `a ↦ { x | x ⊑ a }`. -/
def of (a : α) : Completion α := ⟨fun x => x ⊑ a, fun _ _ hxy hy => PartialOrder.rel_trans hxy hy⟩

/-- `of` is a full order embedding: it both reflects and preserves `⊑`. -/
theorem of_le_of {a b : α} : of a ⊑ of b ↔ a ⊑ b := by
  constructor
  · intro h; exact h a PartialOrder.rel_refl
  · intro hab x hx; exact PartialOrder.rel_trans hx hab

/-- `of` is injective, so `α` genuinely sits inside its completion. -/
theorem of_injective {a b : α} (h : of a = of b) : a = b := by
  have hab : of a ⊑ of b := by rw [h]; exact PartialOrder.rel_refl
  have hba : of b ⊑ of a := by rw [h]; exact PartialOrder.rel_refl
  exact PartialOrder.rel_antisymm (of_le_of.mp hab) (of_le_of.mp hba)

end Completion

/-!
## The ideal completion

The down-set completion above is a full complete lattice — it also adjoins *antichain* joins that a
`CCPO` never requires (e.g. `of a ⊔ of b` for incomparable `a, b`). The **ideal completion** keeps
only the sups that chain-completeness forces, by restricting to **directed** down-sets (ideals).

It is still a `CCPO`, the original order embeds via principal ideals, and — the desired property —
every element is the least upper bound of the embedded points below it. For a *tree-like* order
(e.g. the prefix order on lists), directed sets are chains, so this is literally "a sup of a chain
of `of x`s", and the completion is exactly the finite-and-infinite objects (`Seq`, for lists). -/

/-- An **order ideal**: a downward-closed, up-directed subset. The empty set qualifies (giving the
bottom `⊥` of the completion). -/
def Ideal (P : Type) [PartialOrder P] : Type :=
  { m : P → Prop //
    (∀ ⦃x y⦄, x ⊑ y → m y → m x) ∧ (∀ ⦃x y⦄, m x → m y → ∃ z, m z ∧ x ⊑ z ∧ y ⊑ z) }

namespace Ideal

variable {P : Type} [PartialOrder P]

@[ext] theorem ext {I J : Ideal P} (h : ∀ x, I.1 x ↔ J.1 x) : I = J :=
  Subtype.ext (funext fun x => propext (h x))

/-- Ideals ordered by inclusion. -/
instance : PartialOrder (Ideal P) where
  rel I J := ∀ x, I.1 x → J.1 x
  rel_refl _ h := h
  rel_trans hIJ hJK x hx := hJK x (hIJ x hx)
  rel_antisymm hIJ hJI := ext fun x => ⟨hIJ x, hJI x⟩

theorem le_def {I J : Ideal P} : I ⊑ J ↔ ∀ x, I.1 x → J.1 x := Iff.rfl

/-- The union of a chain of ideals is again an ideal: down-closure is clear, and directedness uses
that the two witnessing ideals are comparable (this is the one place chain-ness is needed). -/
def sUnion (c : Ideal P → Prop) (hc : chain c) : Ideal P :=
  ⟨fun x => ∃ I, c I ∧ I.1 x, by
    refine ⟨?_, ?_⟩
    · rintro x y hxy ⟨I, hI, hIy⟩; exact ⟨I, hI, I.2.1 hxy hIy⟩
    · rintro x y ⟨I, hI, hIx⟩ ⟨J, hJ, hJy⟩
      rcases hc I J hI hJ with h | h
      · obtain ⟨z, hz, hxz, hyz⟩ := J.2.2 (h x hIx) hJy
        exact ⟨z, ⟨J, hJ, hz⟩, hxz, hyz⟩
      · obtain ⟨z, hz, hxz, hyz⟩ := I.2.2 hIx (h y hJy)
        exact ⟨z, ⟨I, hI, hz⟩, hxz, hyz⟩⟩

theorem isSup_sUnion (c : Ideal P → Prop) (hc : chain c) : is_sup c (sUnion c hc) := by
  intro T
  constructor
  · intro hsup I hI x hx; exact hsup x ⟨I, hI, hx⟩
  · rintro h x ⟨I, hI, hx⟩; exact h I hI x hx

/-- The ideal completion is a `CCPO`: sups of chains are unions; the empty chain's sup is the empty
ideal `⊥`. -/
instance : CCPO (Ideal P) where
  has_csup hc := ⟨sUnion _ hc, isSup_sUnion _ hc⟩

/-- The principal-ideal embedding `α ↪ Ideal α`, `x ↦ ↓x`. -/
def of (x : P) : Ideal P :=
  ⟨fun y => y ⊑ x,
   fun _ _ hab hbx => PartialOrder.rel_trans hab hbx,
   fun _ _ ha hb => ⟨x, PartialOrder.rel_refl, ha, hb⟩⟩

theorem of_le_of {x y : P} : of x ⊑ of y ↔ x ⊑ y :=
  ⟨fun h => h x PartialOrder.rel_refl, fun hxy _ hz => PartialOrder.rel_trans hz hxy⟩

/-- **Algebraicity / density.** Every ideal is the least upper bound of the principal ideals below
it — i.e. of the embedded points it contains. This is the desired property in its general form. -/
theorem isSup_of_principals (I : Ideal P) :
    is_sup (fun J => ∃ x, I.1 x ∧ J = of x) I := by
  intro T
  constructor
  · rintro hIT J ⟨x, hx, rfl⟩ y hy
    exact hIT y (I.2.1 hy hx)
  · intro h x hx
    exact h (of x) ⟨x, hx, rfl⟩ x PartialOrder.rel_refl

/-- In a **tree-like** order — any two elements with a common upper bound are comparable, so there
are no diamonds — every ideal is totally ordered. Prefix orders on lists and trees are tree-like. -/
theorem isChain_of_treeLike (htree : ∀ x y z : P, x ⊑ z → y ⊑ z → x ⊑ y ∨ y ⊑ x)
    (I : Ideal P) (x y : P) (hx : I.1 x) (hy : I.1 y) : x ⊑ y ∨ y ⊑ x := by
  obtain ⟨z, hz, hxz, hyz⟩ := I.2.2 hx hy
  exact htree x y z hxz hyz

/-- **The desired property, chain form.** If `I` is totally ordered (automatic when `P` is
tree-like), the principal ideals below it form a *chain*, and `I` is the supremum of that chain of
embedded points. So every element is `⊥`, `of x`, or the sup of a chain of `of x`s. -/
theorem isSup_of_principals_chain (I : Ideal P)
    (hI : ∀ x y, I.1 x → I.1 y → x ⊑ y ∨ y ⊑ x) :
    chain (fun J => ∃ x, I.1 x ∧ J = of x) ∧ is_sup (fun J => ∃ x, I.1 x ∧ J = of x) I := by
  refine ⟨?_, isSup_of_principals I⟩
  rintro J K ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  rcases hI x y hx hy with h | h
  · exact Or.inl (of_le_of.mpr h)
  · exact Or.inr (of_le_of.mpr h)

/-- Running joins of a countable family `enum` inside the ideal `I`: an ascending sequence of
elements of `I` that dominates every `enum n`. -/
noncomputable def joinChain (I : Ideal P) (enum : Nat → P) (hmem : ∀ n, I.1 (enum n)) :
    Nat → {x : P // I.1 x}
  | 0 => ⟨enum 0, hmem 0⟩
  | n + 1 =>
      ⟨(I.2.2 (joinChain I enum hmem n).2 (hmem (n + 1))).choose,
       (I.2.2 (joinChain I enum hmem n).2 (hmem (n + 1))).choose_spec.1⟩

theorem joinChain_le_succ (I : Ideal P) (enum : Nat → P) (hmem : ∀ n, I.1 (enum n)) (n : Nat) :
    (joinChain I enum hmem n).1 ⊑ (joinChain I enum hmem (n + 1)).1 :=
  (I.2.2 (joinChain I enum hmem n).2 (hmem (n + 1))).choose_spec.2.1

theorem enum_le_joinChain (I : Ideal P) (enum : Nat → P) (hmem : ∀ n, I.1 (enum n)) (n : Nat) :
    enum n ⊑ (joinChain I enum hmem n).1 := by
  cases n with
  | zero => exact PartialOrder.rel_refl
  | succ n => exact (I.2.2 (joinChain I enum hmem n).2 (hmem (n + 1))).choose_spec.2.2

theorem joinChain_mono (I : Ideal P) (enum : Nat → P) (hmem : ∀ n, I.1 (enum n)) {m n : Nat}
    (h : m ≤ n) : (joinChain I enum hmem m).1 ⊑ (joinChain I enum hmem n).1 := by
  induction h with
  | refl => exact PartialOrder.rel_refl
  | step _ ih => exact PartialOrder.rel_trans ih (joinChain_le_succ I enum hmem _)

/-- **Point (2).** If a countable family `enum` is cofinal in the ideal `I` (every approximant in
`I` is dominated by some `enum n` — i.e. `I` is countably generated), then `I` is the supremum of a
**chain** of embedded points `of x`, `x ∈ X`. The chain is the running joins of `enum` inside `I`;
its existence is exactly the property that makes branching (but countable) inductive types work. -/
theorem isSup_of_principals_cofinalChain (I : Ideal P) (enum : Nat → P)
    (hmem : ∀ n, I.1 (enum n)) (hcofinal : ∀ x, I.1 x → ∃ n, x ⊑ enum n) :
    ∃ c : Ideal P → Prop,
      chain c ∧ (∀ J, c J → ∃ x, I.1 x ∧ J = of x) ∧ is_sup c I := by
  refine ⟨fun J => ∃ n, J = of (joinChain I enum hmem n).1, ?_, ?_, ?_⟩
  · rintro J K ⟨m, rfl⟩ ⟨n, rfl⟩
    rcases Nat.le_total m n with h | h
    · exact Or.inl (of_le_of.mpr (joinChain_mono I enum hmem h))
    · exact Or.inr (of_le_of.mpr (joinChain_mono I enum hmem h))
  · rintro J ⟨n, rfl⟩
    exact ⟨(joinChain I enum hmem n).1, (joinChain I enum hmem n).2, rfl⟩
  · intro T
    constructor
    · rintro hIT J ⟨n, rfl⟩ y hy
      exact hIT y (I.2.1 hy (joinChain I enum hmem n).2)
    · intro h x hx
      obtain ⟨n, hn⟩ := hcofinal x hx
      exact h (of (joinChain I enum hmem n).1) ⟨n, rfl⟩ x
        (PartialOrder.rel_trans hn (enum_le_joinChain I enum hmem n))

/-- **Point (2), for a countable base.** If `X = P` is countable then *every* element of the
completion is the supremum of a chain of embedded points `of x`. The countability is unavoidable:
without it (2) is false (an element with uncountably many "positions" cannot be reached by a chain,
since a chain of finite objects has a countable union). -/
theorem isSup_of_principals_chain_of_countable [Countable P] (I : Ideal P) :
    ∃ c : Ideal P → Prop, chain c ∧ (∀ J, c J → ∃ x, J = of x) ∧ is_sup c I := by
  by_cases hne : ∃ x, I.1 x
  · obtain ⟨x₀, hx₀⟩ := hne
    haveI : Nonempty {y : P // I.1 y} := ⟨⟨x₀, hx₀⟩⟩
    obtain ⟨f, hf⟩ := exists_surjective_nat {y : P // I.1 y}
    have hcof : ∀ x, I.1 x → ∃ n, x ⊑ (f n).1 := by
      intro x hx
      obtain ⟨n, hn⟩ := hf ⟨x, hx⟩
      exact ⟨n, by rw [hn]; exact PartialOrder.rel_refl⟩
    obtain ⟨c, hchain, hprinc, hsup⟩ :=
      isSup_of_principals_cofinalChain I (fun n => (f n).1) (fun n => (f n).2) hcof
    exact ⟨c, hchain, fun J hJ => (hprinc J hJ).imp fun x h => h.2, hsup⟩
  · refine ⟨fun _ => False, fun _ _ h => h.elim, fun _ h => h.elim, ?_⟩
    intro T
    exact ⟨fun _ J hJ => hJ.elim, fun _ x hx => (hne ⟨x, hx⟩).elim⟩

end Ideal

end Lean.Order
