import Colean.Raw

open Codata

-- Lean 4.34 compares implicit arguments and metavariable types without unfolding definitions.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Mutual types: trees and forests

Three readings of the mutual signature

```
Tree α   | node (a : α) (children : Forest α)
Forest α | nil | cons (t : Tree α) (rest : Forest α)
```

all on the same raw encoding (`Rose.Shape`, `Rose.rawNode`, `Rose.rawNil`, `Rose.rawCons`),
each with its (co)recursor:

* **both inductive** (`FinRose`, `FinForest`: finite rose trees). A `mutual` block of two
  `inductive_fixpoint`s; Lean generates the mutual induction principle `IsFinTree.mutual_induct`,
  from which `FinRose.induction` with two motives follows.
* **both coinductive** (`CoRose`, `CoForest`: infinite depth and infinite width). A `mutual`
  block of two `coinductive_fixpoint`s; the generated `IsCoTree.mutual_induct` is the mutual
  coinduction principle, and it is what the mutual corecursor `CoRose.corec`/`CoForest.corec`
  needs: one coalgebra per type, sharing the state types.
* **inductive forests, coinductive trees** (`Rose`, `Forest`: finitely many children at every
  node, but infinite depth). A mixed `mutual` block is rejected ("Cannot eliminate recursive
  call"), and rightly so: with the implication order on forests and the reverse implication
  order on trees, the joint operator is not monotone. The mixed type is a *nested* fixpoint
  instead. `IsForestOf P` is the least fixpoint for forests of `P`-trees, parameterised by the
  tree predicate and proved monotone in it (`isForestOf_mono`, registered for the monotonicity
  tactic), and `IsTree` is the greatest fixpoint using it. Its coinduction principle asks, for a
  tree in `R`, for a *finite* forest of `R`-trees, so the corecursor `Rose.corec` takes a
  coalgebra `S → α × List S`, and its proof obligation is a coinduction with an induction on the
  list inside.

The other mixed reading (inductive trees, coinductive forests: finite depth, infinite width) is
the same construction with the roles exchanged.
-/

universe u v w

namespace Rose

/-- The non-recursive data of each constructor of both types. -/
inductive Shape (α : Type u)
  | node (a : α)
  | nil
  | cons

variable {α : Type u}

/-- The raw encoding of `Tree.node a f`. -/
def rawNode (a : α) (f : Raw ℕ (Shape α)) : Raw ℕ (Shape α) := Raw.node (.node a) [f]

/-- The raw encoding of `Forest.nil`. -/
def rawNil : Raw ℕ (Shape α) := Raw.node .nil []

/-- The raw encoding of `Forest.cons t f`. -/
def rawCons (t f : Raw ℕ (Shape α)) : Raw ℕ (Shape α) := Raw.node .cons [t, f]

/-! ## Both inductive -/

mutual
/-- Finite trees: the least fixpoint, jointly with `IsFinForest`. -/
def IsFinTree (t : Raw ℕ (Shape α)) : Prop :=
  ∃ a f, t = rawNode a f ∧ IsFinForest f
inductive_fixpoint
/-- Finite forests of finite trees. -/
def IsFinForest (f : Raw ℕ (Shape α)) : Prop :=
  f = rawNil ∨ ∃ t f', f = rawCons t f' ∧ IsFinTree t ∧ IsFinForest f'
inductive_fixpoint
end

/-! ## Both coinductive -/

mutual
/-- Trees of infinite depth and width: the greatest fixpoint, jointly with `IsCoForest`. -/
def IsCoTree (t : Raw ℕ (Shape α)) : Prop :=
  ∃ a f, t = rawNode a f ∧ IsCoForest f
coinductive_fixpoint
/-- Possibly infinite forests. -/
def IsCoForest (f : Raw ℕ (Shape α)) : Prop :=
  f = rawNil ∨ ∃ t f', f = rawCons t f' ∧ IsCoTree t ∧ IsCoForest f'
coinductive_fixpoint
end

/-! ## Inductive forests of coinductive trees -/

/-- Finite forests of `P`-trees: a least fixpoint parameterised by the tree predicate. -/
def IsForestOf (P : Raw ℕ (Shape α) → Prop) (f : Raw ℕ (Shape α)) : Prop :=
  f = rawNil ∨ ∃ t f', f = rawCons t f' ∧ P t ∧ IsForestOf P f'
inductive_fixpoint

open Lean.Order in
/-- `IsForestOf` is monotone in the tree predicate, in the order of coinductive definitions.
This is what lets the greatest fixpoint `IsTree` recurse through it. -/
@[partial_fixpoint_monotone]
theorem isForestOf_mono {β : Sort v} [PartialOrder β]
    (P : β → Raw ℕ (Shape α) → ReverseImplicationOrder) (hP : monotone P) (f : Raw ℕ (Shape α)) :
    @monotone _ _ _ ReverseImplicationOrder.instOrder (fun x => IsForestOf (P x) f) :=
  fun x y hxy h => by
    refine IsForestOf.induct (P y) (IsForestOf (P x)) ?_ f h
    intro f hf
    rw [IsForestOf.eq_def]
    rcases hf with hf | ⟨t, f', rfl, ht, hf'⟩
    · exact Or.inl hf
    · exact Or.inr ⟨t, f', rfl, hP x y hxy t ht, hf'⟩

/-- Trees of infinite depth with finitely many children at every node: the greatest fixpoint
through the least fixpoint `IsForestOf`. -/
def IsTree (t : Raw ℕ (Shape α)) : Prop :=
  ∃ a f, t = rawNode a f ∧ IsForestOf IsTree f
coinductive_fixpoint

end Rose

/-- Finite rose trees. -/
def FinRose (α : Type u) : Type u := {t : Raw ℕ (Rose.Shape α) // Rose.IsFinTree t}
/-- Finite forests of finite rose trees. -/
def FinForest (α : Type u) : Type u := {f : Raw ℕ (Rose.Shape α) // Rose.IsFinForest f}

/-- Rose trees of infinite depth and width. -/
def CoRose (α : Type u) : Type u := {t : Raw ℕ (Rose.Shape α) // Rose.IsCoTree t}
/-- Possibly infinite forests of them. -/
def CoForest (α : Type u) : Type u := {f : Raw ℕ (Rose.Shape α) // Rose.IsCoForest f}

/-- Rose trees of infinite depth and finite width. -/
def Rose (α : Type u) : Type u := {t : Raw ℕ (Rose.Shape α) // Rose.IsTree t}
/-- Finite forests of them. -/
def Forest (α : Type u) : Type u := {f : Raw ℕ (Rose.Shape α) // Rose.IsForestOf Rose.IsTree f}

namespace Rose

variable {α : Type u}

/-! ## Both inductive: constructors and the mutual induction principle -/

/-- A finite tree. -/
def FinRose.node (a : α) (f : FinForest α) : FinRose α :=
  ⟨rawNode a f.1, by rw [IsFinTree.eq_def]; exact ⟨a, f.1, rfl, f.2⟩⟩

/-- The empty finite forest. -/
def FinForest.nil : FinForest α := ⟨rawNil, by rw [IsFinForest.eq_def]; exact Or.inl rfl⟩

/-- Prepend a finite tree. -/
def FinForest.cons (t : FinRose α) (f : FinForest α) : FinForest α :=
  ⟨rawCons t.1 f.1, by rw [IsFinForest.eq_def]; exact Or.inr ⟨t.1, f.1, rfl, t.2, f.2⟩⟩

/-- Mutual induction, from the generated `IsFinTree.mutual_induct`. -/
theorem FinRose.induction {motiveT : FinRose α → Prop} {motiveF : FinForest α → Prop}
    (node : ∀ a f, motiveF f → motiveT (FinRose.node a f)) (nil : motiveF FinForest.nil)
    (cons : ∀ t f, motiveT t → motiveF f → motiveF (FinForest.cons t f)) :
    (∀ t, motiveT t) ∧ (∀ f, motiveF f) := by
  have := IsFinTree.mutual_induct (fun t => ∃ h : IsFinTree t, motiveT ⟨t, h⟩)
    (fun f => ∃ h : IsFinForest f, motiveF ⟨f, h⟩) ?_ ?_
  · exact ⟨fun ⟨t, ht⟩ => (this.1 t ht).elim fun _ h => h,
      fun ⟨f, hf⟩ => (this.2 f hf).elim fun _ h => h⟩
  · rintro t ⟨a, f, rfl, hf, ih⟩
    exact ⟨_, node a ⟨f, hf⟩ ih⟩
  · rintro f (rfl | ⟨t, f', rfl, ⟨ht, iht⟩, ⟨hf', ihf'⟩⟩)
    · exact ⟨_, nil⟩
    · exact ⟨_, cons ⟨t, ht⟩ ⟨f', hf'⟩ iht ihf'⟩

/-! ## Both coinductive: constructors and the mutual corecursor -/

/-- A tree. -/
def CoRose.node (a : α) (f : CoForest α) : CoRose α :=
  ⟨rawNode a f.1, by rw [IsCoTree.eq_def]; exact ⟨a, f.1, rfl, f.2⟩⟩

/-- The empty forest. -/
def CoForest.nil : CoForest α := ⟨rawNil, by rw [IsCoForest.eq_def]; exact Or.inl rfl⟩

/-- Prepend a tree. -/
def CoForest.cons (t : CoRose α) (f : CoForest α) : CoForest α :=
  ⟨rawCons t.1 f.1, by rw [IsCoForest.eq_def]; exact Or.inr ⟨t.1, f.1, rfl, t.2, f.2⟩⟩

section

variable {S₁ : Type v} {S₂ : Type w}

/-- A coalgebra for trees and one for forests, sharing state types, as one `Raw.corecList`
coalgebra on the sum of the states. -/
def coalgCo (fT : S₁ → α × S₂) (fF : S₂ → Option (S₁ × S₂)) :
    S₁ ⊕ S₂ → Shape α × List (S₁ ⊕ S₂)
  | .inl s => (.node (fT s).1, [.inr (fT s).2])
  | .inr s =>
    match fF s with
    | none => (.nil, [])
    | some (s₁, s₂) => (.cons, [.inl s₁, .inr s₂])

/-- The unfoldings are trees and forests: mutual coinduction, with the two sets of unfoldings. -/
theorem isCo_corecList (fT : S₁ → α × S₂) (fF : S₂ → Option (S₁ × S₂)) :
    (∀ s, IsCoTree (Raw.corecList (coalgCo fT fF) (.inl s))) ∧
      ∀ s, IsCoForest (Raw.corecList (coalgCo fT fF) (.inr s)) := by
  have := IsCoTree.mutual_induct (fun t => ∃ s, t = Raw.corecList (coalgCo fT fF) (.inl s))
    (fun f => ∃ s, f = Raw.corecList (coalgCo fT fF) (.inr s)) ?_ ?_
  · exact ⟨fun s => this.1 _ ⟨s, rfl⟩, fun s => this.2 _ ⟨s, rfl⟩⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨(fT s).1, Raw.corecList (coalgCo fT fF) (.inr (fT s).2),
      (Raw.corecList_eq _ _).trans rfl, (fT s).2, rfl⟩
  · rintro _ ⟨s, rfl⟩
    rw [Raw.corecList_eq]
    rcases hf : fF s with _ | ⟨s₁, s₂⟩
    · exact Or.inl (by simp [coalgCo, hf, rawNil])
    · exact Or.inr ⟨Raw.corecList (coalgCo fT fF) (.inl s₁),
        Raw.corecList (coalgCo fT fF) (.inr s₂), by simp [coalgCo, hf, rawCons], ⟨s₁, rfl⟩,
        ⟨s₂, rfl⟩⟩

/-- Mutual corecursion: the tree half. -/
def CoRose.corec (fT : S₁ → α × S₂) (fF : S₂ → Option (S₁ × S₂)) (s : S₁) : CoRose α :=
  ⟨_, (isCo_corecList fT fF).1 s⟩

/-- Mutual corecursion: the forest half. -/
def CoForest.corec (fT : S₁ → α × S₂) (fF : S₂ → Option (S₁ × S₂)) (s : S₂) : CoForest α :=
  ⟨_, (isCo_corecList fT fF).2 s⟩

theorem CoRose.corec_eq (fT : S₁ → α × S₂) (fF : S₂ → Option (S₁ × S₂)) (s : S₁) :
    CoRose.corec fT fF s = CoRose.node (fT s).1 (CoForest.corec fT fF (fT s).2) :=
  Subtype.ext (Raw.corecList_eq _ _)

theorem CoForest.corec_eq (fT : S₁ → α × S₂) (fF : S₂ → Option (S₁ × S₂)) (s : S₂) :
    CoForest.corec fT fF s = match fF s with
      | none => CoForest.nil
      | some (s₁, s₂) => CoForest.cons (CoRose.corec fT fF s₁) (CoForest.corec fT fF s₂) := by
  apply Subtype.ext
  show Raw.corecList (coalgCo fT fF) (.inr s) = _
  rw [Raw.corecList_eq]
  rcases hf : fF s with _ | ⟨s₁, s₂⟩ <;>
    simp [coalgCo, hf, rawNil, rawCons, CoForest.nil, CoForest.cons, CoRose.corec, CoForest.corec]

end

/-! ## Inductive forests of coinductive trees: constructors and the corecursor -/

/-- A tree with a finite forest of children. -/
def node (a : α) (f : Forest α) : Rose α :=
  ⟨rawNode a f.1, by rw [IsTree.eq_def]; exact ⟨a, f.1, rfl, f.2⟩⟩

/-- The empty forest. -/
def Forest.nil : Forest α := ⟨rawNil, by rw [IsForestOf.eq_def]; exact Or.inl rfl⟩

/-- Prepend a tree. -/
def Forest.cons (t : Rose α) (f : Forest α) : Forest α :=
  ⟨rawCons t.1 f.1, by rw [IsForestOf.eq_def]; exact Or.inr ⟨t.1, f.1, rfl, t.2, f.2⟩⟩

section

variable {S : Type v}

/-- A coalgebra `S → α × List S` — a label and finitely many child states — as a
`Raw.corecList` coalgebra on tree states and forest states (lists of tree states). -/
def coalgList (f : S → α × List S) : S ⊕ List S → Shape α × List (S ⊕ List S)
  | .inl s => (.node (f s).1, [.inr (f s).2])
  | .inr [] => (.nil, [])
  | .inr (s :: l) => (.cons, [.inl s, .inr l])

/-- Forest states unfold to finite forests of unfolded trees, whatever predicate `P` the
unfolded trees satisfy: induction on the list of states. -/
theorem isForestOf_corecList (f : S → α × List S) {P : Raw ℕ (Shape α) → Prop}
    (hP : ∀ s, P (Raw.corecList (coalgList f) (.inl s))) :
    ∀ l, IsForestOf P (Raw.corecList (coalgList f) (.inr l))
  | [] => by
    rw [IsForestOf.eq_def]
    exact Or.inl ((Raw.corecList_eq _ _).trans rfl)
  | s :: l => by
    rw [IsForestOf.eq_def]
    exact Or.inr ⟨_, _, (Raw.corecList_eq _ _).trans rfl, hP s, isForestOf_corecList f hP l⟩

/-- Tree states unfold to trees: coinduction, whose one-step obligation is the induction
above with `P` the set of unfoldings. -/
theorem isTree_corecList (f : S → α × List S) (s : S) :
    IsTree (Raw.corecList (coalgList f) (.inl s)) := by
  refine IsTree.coinduct (fun t => ∃ s, t = Raw.corecList (coalgList f) (.inl s)) ?_ _ ⟨s, rfl⟩
  rintro _ ⟨s, rfl⟩
  exact ⟨(f s).1, _, (Raw.corecList_eq _ _).trans rfl,
    isForestOf_corecList f (fun s => ⟨s, rfl⟩) (f s).2⟩

/-- Corecursion into finitely branching trees. -/
def corec (f : S → α × List S) (s : S) : Rose α :=
  ⟨Raw.corecList (coalgList f) (.inl s), isTree_corecList f s⟩

/-- Corecursion into forests, from a list of states. -/
def Forest.corec (f : S → α × List S) (l : List S) : Forest α :=
  ⟨Raw.corecList (coalgList f) (.inr l), isForestOf_corecList f (isTree_corecList f) l⟩

theorem corec_eq (f : S → α × List S) (s : S) :
    corec f s = node (f s).1 (Forest.corec f (f s).2) :=
  Subtype.ext (Raw.corecList_eq _ _)

theorem Forest.corec_nil (f : S → α × List S) : Forest.corec f [] = Forest.nil :=
  Subtype.ext (Raw.corecList_eq _ _)

theorem Forest.corec_cons (f : S → α × List S) (s : S) (l : List S) :
    Forest.corec f (s :: l) = Forest.cons (Rose.corec f s) (Forest.corec f l) :=
  Subtype.ext (Raw.corecList_eq _ _)

end

end Rose
