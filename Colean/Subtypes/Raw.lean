import Init.Internal.Order.Basic
import Mathlib.Data.Nat.Notation

/-!
# (Co)inductive types as subtypes of one general type

Lean's `inductive_fixpoint` and `coinductive_fixpoint` define predicates as least and greatest
fixpoints of monotone operators on `_ → Prop`. This folder tests the idea of getting *types* out
of them: fix once and for all a *general type* that is big enough to contain every tree-shaped
value, translate the constructors of a would-be `inductive`/`coinductive` into a monotone
operator on predicates over the general type, take its least or greatest fixpoint, and define the
type as the subtype cut out by that predicate.

## The general type

`Raw I L` is the type of *path-indexed trees* branching over `I` with node labels in `L`: a
function from paths (lists of child indices) to optional labels. It is a final coalgebra for
`X ↦ Option L × (I → X)`: a raw tree is exactly a root label and an `I`-indexed family of
children (`Raw.mk_root_child`, `Raw.ext_root_child`), and every coalgebra `S → Option L × (I → S)`
corecurses into it by structural recursion on paths (`Raw.corec`, `Raw.corec_eq`). Two trees
related by a bisimulation are equal (`Raw.eq_of_bisim`), again by induction on paths, so
bisimulation proofs on the subtypes come for free.

The index type `I` is the branching type, and nothing requires it to be countable (`ITree.lean`
branches over `ℝ`). Constructors with finitely many recursive arguments use `I = ℕ` and
`Raw.node l [t₁, …, tₖ]`: a `some` root carrying the constructor's non-recursive data `l`,
children `t₁, …, tₖ` for the recursive arguments, and `Raw.empty` at every other index (this last
convention is what makes `Raw.node` injective).

## Layout

The hand-written experiments live in `Sketch/`; the `codata` and `data` commands and their
generic theory live next to this file.

* `CoList.lean`, `Tree.lean`, `Str.lean`: three coinductive types, each file containing only the
  translation (raw constructors, the predicate by `coinductive_fixpoint`, the subtype, its
  constructors) and the corecursor with its specification.
* `CoListLemmas.lean`, `TreeLemmas.lean`, `StrLemmas.lean`: what else the types support —
  destructors, case analysis, bisimulation, examples, isomorphisms with Mathlib's `Seq` and with
  `ℕ → α`.
* `FinList.lean`, `FinTree.lean`: the inductive types defined by the same operators with
  `inductive_fixpoint` — induction, recursion into data, isomorphisms with the native inductives.
* `ITree.lean`, `ITreeLemmas.lean`: branching over an arbitrary type `I`, e.g. `ℝ`, and the
  isomorphism `ITree I α ≃ (List I → α)`.
* `Vec.lean`: an indexed family, `Vec α n`; the index is an argument of the predicate.
* `Mutual.lean`: mutual types (trees and forests) — both inductive, both coinductive, and the
  mixed one as a nested fixpoint.
* `StrArith.lean`: `Raw` carries the `CCPO` of `List I → Option L` for free, so
  `partial_fixpoint` definitions live on the general type and coinduction brings them back into
  the subtype.
-/

universe u v w

/-- A path-indexed tree branching over `I`: an optional label at every path `List I`. The label
of the root is `t.get []`, and `t.get (i :: p)` is the label at path `p` of the `i`-th child. -/
structure Raw (I : Type u) (L : Type v) where ofFun ::
  /-- The label at a path, or `none` if the path is absent. -/
  get : List I → Option L

namespace Raw

variable {I : Type u} {L : Type v} {S : Type w}

theorem ext {t₁ t₂ : Raw I L} (h : ∀ p, t₁.get p = t₂.get p) : t₁ = t₂ := by
  cases t₁; cases t₂; simp only [ofFun.injEq]; exact funext h

/-! ### Root, children, and the coalgebra structure -/

/-- The tree with no nodes at all. -/
def empty : Raw I L := ⟨fun _ => none⟩

/-- The label at the root. -/
def root (t : Raw I L) : Option L := t.get []

/-- The `i`-th child, a tree in its own right. -/
def child (t : Raw I L) (i : I) : Raw I L := ⟨fun p => t.get (i :: p)⟩

/-- Build a tree from a root label and a family of children. -/
def mk (r : Option L) (c : I → Raw I L) : Raw I L :=
  ⟨fun | [] => r | i :: p => (c i).get p⟩

@[simp] theorem get_nil (t : Raw I L) : t.get [] = t.root := rfl
@[simp] theorem get_cons (t : Raw I L) (i : I) (p : List I) : t.get (i :: p) = (t.child i).get p :=
  rfl

@[simp] theorem root_mk (r : Option L) (c : I → Raw I L) : (mk r c).root = r := rfl
@[simp] theorem child_mk (r : Option L) (c : I → Raw I L) (i : I) : (mk r c).child i = c i := rfl
@[simp] theorem root_empty : (empty : Raw I L).root = none := rfl
@[simp] theorem child_empty (i : I) : (empty : Raw I L).child i = empty := rfl

/-- A tree is its root together with its children: `Raw I L` is a fixpoint of
`X ↦ Option L × (I → X)`. -/
@[simp] theorem mk_root_child (t : Raw I L) : mk t.root t.child = t :=
  ext fun | [] => rfl | _ :: _ => rfl

theorem ext_root_child {t₁ t₂ : Raw I L} (hr : t₁.root = t₂.root)
    (hc : ∀ i, t₁.child i = t₂.child i) : t₁ = t₂ := by
  rw [← mk_root_child t₁, ← mk_root_child t₂, hr]
  exact congrArg _ (funext hc)

@[simp] theorem mk_inj {r r' : Option L} {c c' : I → Raw I L} :
    mk r c = mk r' c' ↔ r = r' ∧ c = c' :=
  ⟨fun h => ⟨congrArg root h, funext fun i => congrArg (child · i) h⟩,
    fun ⟨hr, hc⟩ => hr ▸ hc ▸ rfl⟩

theorem empty_eq : (empty : Raw I L) = mk none fun _ => empty := (mk_root_child _).symm

theorem eq_empty_iff {t : Raw I L} : t = empty ↔ t.root = none ∧ ∀ i, t.child i = empty :=
  ⟨by rintro rfl; simp, fun ⟨hr, hc⟩ => ext_root_child (by simpa using hr) (by simpa using hc)⟩

/-! ### Bisimulation

Two trees are equal as soon as they are related by a relation that matches roots and is
preserved by taking children. The proof is by induction on paths, which is the only place in
this development where paths are inspected. -/

/-- A bisimulation: related trees have equal roots and related children. -/
def IsBisim (R : Raw I L → Raw I L → Prop) : Prop :=
  ∀ t₁ t₂, R t₁ t₂ → t₁.root = t₂.root ∧ ∀ i, R (t₁.child i) (t₂.child i)

theorem eq_of_bisim {R : Raw I L → Raw I L → Prop} (hR : IsBisim R) {t₁ t₂ : Raw I L}
    (h : R t₁ t₂) : t₁ = t₂ := by
  refine ext fun p => ?_
  induction p generalizing t₁ t₂ with
  | nil => exact (hR _ _ h).1
  | cons i p ih => exact ih ((hR _ _ h).2 i)

/-- Equality itself is a bisimulation, so `Eq ⊔ R` is one whenever `R` is: this lets a
bisimulation on a subtype ignore the `empty` children shared by both sides. -/
theorem isBisim_eq_or {R : Raw I L → Raw I L → Prop} (hR : IsBisim R) :
    IsBisim fun t₁ t₂ => t₁ = t₂ ∨ R t₁ t₂ := fun t₁ t₂ h => by
  rcases h with rfl | h
  · exact ⟨rfl, fun _ => Or.inl rfl⟩
  · exact ⟨(hR _ _ h).1, fun i => Or.inr ((hR _ _ h).2 i)⟩

/-- Bisimulation up to equality: the children may be related or simply equal. -/
theorem eq_of_bisim' {R : Raw I L → Raw I L → Prop}
    (hR : ∀ t₁ t₂, R t₁ t₂ →
      t₁.root = t₂.root ∧ ∀ i, t₁.child i = t₂.child i ∨ R (t₁.child i) (t₂.child i))
    {t₁ t₂ : Raw I L} (h : R t₁ t₂) : t₁ = t₂ :=
  eq_of_bisim (R := fun t₁ t₂ => t₁ = t₂ ∨ R t₁ t₂)
    (fun t₁ t₂ h => by
      rcases h with rfl | h
      · exact ⟨rfl, fun _ => Or.inl rfl⟩
      · exact hR _ _ h)
    (Or.inr h)

/-! ### Corecursion

`Raw I L` is a final coalgebra: any coalgebra `f : S → Option L × (I → S)` gives a map
`corec f : S → Raw I L`, defined by structural recursion on paths, and it is the unique map
commuting with the coalgebra structure. -/

/-- The label at path `p` of the tree unfolded from state `s`. -/
def corecGet (f : S → Option L × (I → S)) : S → List I → Option L
  | s, [] => (f s).1
  | s, i :: p => corecGet f ((f s).2 i) p

/-- Corecursion into `Raw I L`. -/
def corec (f : S → Option L × (I → S)) (s : S) : Raw I L := ⟨corecGet f s⟩

@[simp] theorem root_corec (f : S → Option L × (I → S)) (s : S) : (corec f s).root = (f s).1 := rfl
@[simp] theorem child_corec (f : S → Option L × (I → S)) (s : S) (i : I) :
    (corec f s).child i = corec f ((f s).2 i) := rfl

theorem corec_eq (f : S → Option L × (I → S)) (s : S) :
    corec f s = mk (f s).1 fun i => corec f ((f s).2 i) :=
  (mk_root_child _).symm

/-- Uniqueness of corecursion (finality). -/
theorem corec_unique (f : S → Option L × (I → S)) (g : S → Raw I L)
    (hg : ∀ s, g s = mk (f s).1 fun i => g ((f s).2 i)) : g = corec f :=
  funext fun s =>
    eq_of_bisim (R := fun t₁ t₂ => ∃ s, t₁ = g s ∧ t₂ = corec f s)
      (by
        rintro _ _ ⟨s, rfl, rfl⟩
        exact ⟨by rw [hg s]; rfl, fun i => ⟨(f s).2 i, by rw [hg s]; rfl, rfl⟩⟩)
      ⟨s, rfl, rfl⟩

/-! ### Finitely many children, indexed by naturals

A constructor with non-recursive data `l` and recursive arguments `t₁, …, tₖ` is encoded as
`node l [t₁, …, tₖ]` in `Raw ℕ L`. -/

section Nat

variable {L : Type v} {S : Type w}

/-- A node with a label and a finite list of children; the remaining children are `empty`. -/
def node (l : L) (cs : List (Raw ℕ L)) : Raw ℕ L := mk (some l) fun i => cs.getD i empty

@[simp] theorem root_node (l : L) (cs : List (Raw ℕ L)) : (node l cs).root = some l := rfl
@[simp] theorem child_node (l : L) (cs : List (Raw ℕ L)) (i : ℕ) :
    (node l cs).child i = cs.getD i empty := rfl

@[simp] theorem node_ne_empty (l : L) (cs : List (Raw ℕ L)) : node l cs ≠ empty := by
  intro h; simpa using congrArg root h

theorem node_inj_left {l l' : L} {cs cs' : List (Raw ℕ L)} (h : node l cs = node l' cs') :
    l = l' := by
  simpa using congrArg root h

theorem node_inj_child {l l' : L} {cs cs' : List (Raw ℕ L)} (h : node l cs = node l' cs')
    (i : ℕ) : cs.getD i empty = cs'.getD i empty := by
  simpa using congrArg (child · i) h

/-- A tree whose root is `some l` is `node l` of its first `k` children, for any `k` such that
all later children are `empty`. -/
theorem eq_node_of_root {t : Raw ℕ L} {l : L} (hr : t.root = some l) (k : ℕ)
    (hk : ∀ i, k ≤ i → t.child i = empty) :
    t = node l ((List.range k).map t.child) := by
  refine ext_root_child (by simpa using hr) fun i => ?_
  simp only [child_node]
  by_cases hi : i < k
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hi)]
    exact hk i (by omega)

/-- The coalgebra on `Option S` underlying `corecList`: `none` is the state of `empty`. -/
def listCoalg (f : S → L × List S) : Option S → Option L × (ℕ → Option S)
  | none => (none, fun _ => none)
  | some s => (some (f s).1, fun i => (f s).2[i]?)

/-- Corecursion for user types: a coalgebra `S → L × List S` describes, for each state, the
constructor label and the states of its recursive arguments. The absent children are `empty`. -/
def corecList (f : S → L × List S) (s : S) : Raw ℕ L := corec (listCoalg f) (some s)

theorem corec_listCoalg_none (f : S → L × List S) : corec (listCoalg f) none = empty :=
  eq_of_bisim (R := fun t₁ t₂ => t₁ = corec (listCoalg f) none ∧ t₂ = empty)
    (by rintro _ _ ⟨rfl, rfl⟩; exact ⟨rfl, fun i => ⟨rfl, rfl⟩⟩) ⟨rfl, rfl⟩

theorem corecList_eq (f : S → L × List S) (s : S) :
    corecList f s = node (f s).1 ((f s).2.map (corecList f)) := by
  refine ext_root_child rfl fun i => ?_
  simp only [corecList, child_corec, child_node, List.getD_eq_getElem?_getD, List.getElem?_map,
    listCoalg]
  cases (f s).2[i]? with
  | none => exact corec_listCoalg_none f
  | some s' => rfl

@[simp] theorem root_corecList (f : S → L × List S) (s : S) :
    (corecList f s).root = some (f s).1 := rfl

end Nat

end Raw
