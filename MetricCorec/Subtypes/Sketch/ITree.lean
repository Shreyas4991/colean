import MetricCorec.Subtypes.Raw

/-!
# `ITree`: branching over an arbitrary type

The translation of

```
coinductive ITree (I α) | node (a : α) (children : I → ITree I α)
```

into a subtype of `Raw I α`. The index type of `Raw` is the branching type of the constructor,
and nothing requires it to be countable: `ITree ℝ α` has a continuum of children at every node
(`ITreeLemmas.lean`). Streams are `I = Unit`, infinite binary trees are `I = Bool`, and the
coalgebras are `S → α × (I → S)`, handled directly by `Raw.corec`.
-/

universe u v w

namespace ITree

variable {I : Type u} {α : Type v} {S : Type w}

/-- The raw encoding of `node a c`: label `a`, children `c`. -/
def rawNode (a : α) (c : I → Raw I α) : Raw I α := Raw.mk (some a) c

/-- The predicate cutting `I`-branching trees out of `Raw`: the greatest fixpoint of the
one-step operator. -/
def IsITree (t : Raw I α) : Prop :=
  ∃ a c, t = rawNode a c ∧ ∀ i, IsITree (c i)
coinductive_fixpoint

end ITree

/-- Infinite trees branching over `I` with labels in `α`. -/
def ITree (I : Type u) (α : Type v) : Type (max u v) := {t : Raw I α // ITree.IsITree t}

namespace ITree

variable {I : Type u} {α : Type v} {S : Type w}

/-- A node with an `I`-indexed family of subtrees. -/
def node (a : α) (c : I → ITree I α) : ITree I α :=
  ⟨rawNode a fun i => (c i).1, by rw [IsITree.eq_def]; exact ⟨a, _, rfl, fun i => (c i).2⟩⟩

/-! ### The corecursor -/

/-- The unfoldings of a coalgebra are trees. -/
theorem isITree_corec (f : S → α × (I → S)) (s : S) :
    IsITree (Raw.corec (fun s => (some (f s).1, (f s).2)) s) := by
  refine IsITree.coinduct (fun t => ∃ s, t = Raw.corec (fun s => (some (f s).1, (f s).2)) s) ?_ _
    ⟨s, rfl⟩
  rintro _ ⟨s, rfl⟩
  exact ⟨(f s).1, _, Raw.corec_eq _ s, fun i => ⟨(f s).2 i, rfl⟩⟩

/-- Corecursion into `I`-branching trees. -/
def corec (f : S → α × (I → S)) (s : S) : ITree I α :=
  ⟨Raw.corec (fun s => (some (f s).1, (f s).2)) s, isITree_corec f s⟩

/-- The specification of the corecursor. -/
theorem corec_eq (f : S → α × (I → S)) (s : S) :
    corec f s = node (f s).1 fun i => corec f ((f s).2 i) :=
  Subtype.ext (Raw.corec_eq _ s)

end ITree
