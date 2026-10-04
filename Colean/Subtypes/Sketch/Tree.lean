import Colean.Subtypes.Raw

/-!
# `Tree`: the coinductive type and its corecursor

The translation of

```
coinductive Tree (α) | leaf | node (a : α) (l r : Tree α)
```

into a subtype of `Raw`, exactly as in `CoList.lean`, now with two recursive arguments: the
raw `node` has two children, the operator has two recursive conjuncts, and the coalgebra of the
corecursor returns two states.

`TreeLemmas.lean` has the destructor, case analysis, bisimulation and examples;
`FinTree.lean` has the inductive type defined by the same operator.
-/

universe u v

/-- The non-recursive data of each constructor. -/
inductive Tree.Shape (α : Type u)
  | leaf
  | node (a : α)

namespace Tree

variable {α : Type u} {S : Type v}

/-- The raw encoding of `leaf`. -/
def rawLeaf : Raw ℕ (Shape α) := Raw.node .leaf []

/-- The raw encoding of `node a l r`: children `0` and `1` are the subtrees. -/
def rawNode (a : α) (l r : Raw ℕ (Shape α)) : Raw ℕ (Shape α) := Raw.node (.node a) [l, r]

/-- The predicate cutting trees out of `Raw`: the greatest fixpoint of the one-step
operator. -/
def IsTree (t : Raw ℕ (Shape α)) : Prop :=
  t = rawLeaf ∨ ∃ a l r, t = rawNode a l r ∧ IsTree l ∧ IsTree r
coinductive_fixpoint

end Tree

/-- Possibly infinite binary trees with leaves. -/
def Tree (α : Type u) : Type u := {t : Raw ℕ (Tree.Shape α) // Tree.IsTree t}

namespace Tree

variable {α : Type u} {S : Type v}

/-- The leaf. -/
def leaf : Tree α := ⟨rawLeaf, by rw [IsTree.eq_def]; exact Or.inl rfl⟩

/-- A node with two subtrees. -/
def node (a : α) (l r : Tree α) : Tree α :=
  ⟨rawNode a l.1 r.1, by rw [IsTree.eq_def]; exact Or.inr ⟨a, l.1, r.1, rfl, l.2, r.2⟩⟩

/-! ### The corecursor -/

/-- A coalgebra `S → Option (α × S × S)` as a `Raw.corecList` coalgebra. -/
def coalg (f : S → Option (α × S × S)) (s : S) : Shape α × List S :=
  match f s with
  | none => (.leaf, [])
  | some (a, l, r) => (.node a, [l, r])

/-- The unfoldings of a coalgebra are trees: coinduction with `R` the set of all unfoldings. -/
theorem isTree_corecList (f : S → Option (α × S × S)) (s : S) :
    IsTree (Raw.corecList (coalg f) s) := by
  refine IsTree.coinduct (fun t => ∃ s, t = Raw.corecList (coalg f) s) ?_ _ ⟨s, rfl⟩
  rintro _ ⟨s, rfl⟩
  rw [Raw.corecList_eq]
  rcases hf : f s with _ | ⟨a, l, r⟩
  · exact Or.inl (by simp [coalg, hf, rawLeaf])
  · exact Or.inr ⟨a, _, _, by simp [coalg, hf, rawNode], ⟨l, rfl⟩, ⟨r, rfl⟩⟩

/-- Corecursion into trees. -/
def corec (f : S → Option (α × S × S)) (s : S) : Tree α :=
  ⟨Raw.corecList (coalg f) s, isTree_corecList f s⟩

/-- The specification of the corecursor. -/
theorem corec_eq (f : S → Option (α × S × S)) (s : S) :
    corec f s = match f s with
      | none => leaf
      | some (a, l, r) => node a (corec f l) (corec f r) := by
  apply Subtype.ext
  show Raw.corecList (coalg f) s = _
  rw [Raw.corecList_eq]
  rcases hf : f s with _ | ⟨a, l, r⟩ <;> simp [coalg, hf, rawLeaf, rawNode, leaf, node, corec]

end Tree
