import Mathlib.Logic.Equiv.List
import Mathlib.Data.List.Basic
import Colean.Subtypes.Raw

-- Lean 4.34 compares implicit arguments and metavariable types without unfolding definitions.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Scratch: types as predicate transformers on an ambient raw type

The route where `inductive_fixpoint` and `coinductive_fixpoint` do the work. A type is not
given by a signature; it is given by its *predicate transformer* on an ambient raw type,
written by recursion on the syntax of its constructors:

* a constructor is a disjunct, its non-recursive data an `∃`, the encoding an equation;
* an occurrence of the type under a product is a conjunct, under a sum a disjunct, under a
  `Π` a `∀`, under a `Σ` an `∃`: each occurrence is handled where it is used;
* an occurrence under another type is that type's transformer applied to the predicate;
* a type parameter is a predicate on subtrees, and a value of the parameter is a leaf.

The commands take the fixpoint, prove monotonicity, and generate `eq_def`, `induct` and
`coinduct`. The one obligation per type is a registered monotonicity lemma for its
transformer, in each of the two orders, so that other types may recurse under it.

The ambient raw type is `Raw ℕ L` for a label type `L` chosen by the outer declaration; a type
is defined for every `L` that can host its labels (`HasList L`), which is what makes it
reusable inside other types. The file defines lists this way, then instantiates them as the
standalone `MyList α`, reuses them inside `Rose α` and `CoRose α`, and does `BinTree` with
`X × X` inline. -/

universe u v

namespace Ambient

open Raw

/-! ## The list transformer, once for every ambient raw type hosting its labels -/

/-- The labels a raw type must offer to host lists. -/
class HasList (L : Type v) where
  nil : L
  cons : L
  nil_ne_cons : nil ≠ cons

section ListLeaf

variable {L : Type v} [HasList L]

/-- Storage: `nil` is a node with no children, `cons h t` a node with children `h` and `t`. -/
def rawNil : Raw ℕ L := Raw.node HasList.nil []
def rawCons (h t : Raw ℕ L) : Raw ℕ L := Raw.node HasList.cons [h, t]

theorem rawNil_ne_rawCons (h t : Raw ℕ L) : rawNil ≠ rawCons h t := fun e =>
  HasList.nil_ne_cons (Option.some.inj (congrArg root e))

theorem rawCons_inj {h h' t t' : Raw ℕ L} :
    rawCons h t = rawCons h' t' ↔ h = h' ∧ t = t' := by
  constructor
  · intro e
    exact ⟨by simpa [rawCons] using congrArg (child · 0) e,
      by simpa [rawCons] using congrArg (child · 1) e⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The transformer: a raw list whose elements satisfy `P`. -/
def IsListOf (P : Raw ℕ L → Prop) (t : Raw ℕ L) : Prop :=
  t = rawNil ∨ ∃ h tl, t = rawCons h tl ∧ P h ∧ IsListOf P tl
inductive_fixpoint

section Monotone
open Lean.Order

/-- Registered monotonicity, for inductive types recursing under lists. -/
@[partial_fixpoint_monotone]
theorem IsListOf.monotone_ind {γ} [Lean.Order.PartialOrder γ] (f : γ → Raw ℕ L → ImplicationOrder)
    (t : Raw ℕ L) (hf : monotone f) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => IsListOf (f x) t) := by
  intro x y hxy hx
  refine IsListOf.induct (f x) (IsListOf (f y)) ?_ t hx
  rintro t (rfl | ⟨h, tl, rfl, hh, ih⟩) <;> rw [IsListOf.eq_def]
  · exact Or.inl rfl
  · exact Or.inr ⟨h, tl, rfl, monotone_apply h f hf x y hxy hh, ih⟩

/-- The same for coinductive types. -/
@[partial_fixpoint_monotone]
theorem IsListOf.monotone_coind {γ} [Lean.Order.PartialOrder γ]
    (f : γ → Raw ℕ L → ReverseImplicationOrder) (t : Raw ℕ L) (hf : monotone f) :
    @monotone _ _ _ ReverseImplicationOrder.instOrder (fun x => IsListOf (f x) t) := by
  intro x y hxy hy
  refine IsListOf.induct (f y) (IsListOf (f x)) ?_ t hy
  rintro t (rfl | ⟨h, tl, rfl, hh, ih⟩) <;> rw [IsListOf.eq_def]
  · exact Or.inl rfl
  · exact Or.inr ⟨h, tl, rfl, monotone_apply h f hf x y hxy hh, ih⟩

end Monotone

/-! ### Transport: raw lists over `P` are native lists of the subtype -/

variable {P : Raw ℕ L → Prop}

theorem isListOf_rawNil : IsListOf P rawNil := by
  rw [IsListOf.eq_def]; exact Or.inl rfl

theorem isListOf_rawCons {h t : Raw ℕ L} (hh : P h) (ht : IsListOf P t) :
    IsListOf P (rawCons h t) := by
  rw [IsListOf.eq_def]; exact Or.inr ⟨h, t, rfl, hh, ht⟩

def ofList : List (Raw ℕ L) → Raw ℕ L
  | [] => rawNil
  | h :: l => rawCons h (ofList l)

theorem isListOf_ofList {l : List (Raw ℕ L)} (hl : ∀ h ∈ l, P h) : IsListOf P (ofList l) := by
  induction l with
  | nil => exact isListOf_rawNil
  | cons h l ih =>
    exact isListOf_rawCons (hl h (by simp)) (ih fun h' hh' => hl h' (by simp [hh']))

theorem ofList_injective : Function.Injective (ofList (L := L)) := by
  intro l l' e
  induction l generalizing l' with
  | nil => cases l' with
    | nil => rfl
    | cons => exact absurd e (rawNil_ne_rawCons _ _)
  | cons h l ih => cases l' with
    | nil => exact absurd e.symm (rawNil_ne_rawCons _ _)
    | cons h' l' =>
      obtain ⟨rfl, e'⟩ := rawCons_inj.mp e
      rw [ih e']

theorem exists_list_of_isListOf {t : Raw ℕ L} (ht : IsListOf P t) :
    ∃ l : List (Raw ℕ L), t = ofList l ∧ ∀ h ∈ l, P h := by
  refine IsListOf.induct P (fun t => ∃ l, t = ofList l ∧ ∀ h ∈ l, P h) ?_ t ht
  rintro t (rfl | ⟨h, tl, rfl, hh, l, rfl, hl⟩)
  · exact ⟨[], rfl, by simp⟩
  · exact ⟨h :: l, rfl, List.forall_mem_cons.mpr ⟨hh, hl⟩⟩

omit [HasList L] in
theorem exists_list_subtype {Q : {t : Raw ℕ L // P t} → Prop} {l : List (Raw ℕ L)}
    (hl : ∀ h ∈ l, ∃ hp : P h, Q ⟨h, hp⟩) :
    ∃ cs : List {t // P t}, l = cs.map Subtype.val ∧ ∀ c ∈ cs, Q c := by
  induction l with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons h l ih =>
    obtain ⟨hp, hq⟩ := hl h (by simp)
    obtain ⟨cs, rfl, hcs⟩ := ih fun h' hh' => hl h' (by simp [hh'])
    exact ⟨⟨h, hp⟩ :: cs, rfl, List.forall_mem_cons.mpr ⟨hq, hcs⟩⟩

/-- The lists over `P`: the type the transformer cuts out. -/
def ListOf (P : Raw ℕ L → Prop) : Type v := {t : Raw ℕ L // IsListOf P t}

def ListOf.ofList (cs : List {t // P t}) : ListOf P :=
  ⟨Ambient.ofList (cs.map Subtype.val), isListOf_ofList (List.forall_mem_map.mpr fun c _ => c.2)⟩

theorem ListOf.exists_eq_ofList (l : ListOf P) : ∃ cs : List {t // P t}, l = ListOf.ofList cs := by
  obtain ⟨t, ht⟩ := l
  obtain ⟨l', rfl, hl'⟩ := exists_list_of_isListOf ht
  obtain ⟨cs, rfl, -⟩ := exists_list_subtype (Q := fun _ => True) fun h hh => ⟨hl' h hh, trivial⟩
  exact ⟨cs, rfl⟩

theorem ListOf.ofList_injective : Function.Injective (ListOf.ofList (P := P)) := by
  intro cs cs' e
  have h : Ambient.ofList (cs.map Subtype.val) = Ambient.ofList (cs'.map Subtype.val) :=
    congrArg Subtype.val e
  exact List.map_injective_iff.mpr Subtype.val_injective (Ambient.ofList_injective h)

/-- The user-facing interface of a list over `P`. -/
noncomputable def ListOf.equiv (P : Raw ℕ L → Prop) : ListOf P ≃ List {t // P t} :=
  (Equiv.ofBijective ListOf.ofList
    ⟨ListOf.ofList_injective, fun l => (ListOf.exists_eq_ofList l).imp fun _ h => h.symm⟩).symm

/-! ### Corecursion support: a list of states unfolds to the raw list of their trees -/

variable {S T : Type u}

/-- The step of a raw coalgebra on a list of states, given the injections of states and of
lists of states into the coalgebra's state type. -/
def listStep (ofS : S → T) (ofL : List S → T) : List S → L × List T
  | [] => (HasList.nil, [])
  | s :: l => (HasList.cons, [ofS s, ofL l])

theorem corecList_eq_ofList (g : T → L × List T) (ofS : S → T) (ofL : List S → T)
    (hg : ∀ l, g (ofL l) = listStep ofS ofL l) (l : List S) :
    corecList g (ofL l) = ofList (l.map fun s => corecList g (ofS s)) := by
  induction l with
  | nil => rw [corecList_eq, hg]; rfl
  | cons s l ih =>
    rw [corecList_eq, hg]; simp only [listStep, List.map_cons, List.map_nil]
    rw [ofList, ← ih]; rfl

end ListLeaf

/-! ## The standalone lists: the parameter is a predicate, its values are leaves -/

inductive ListLbl (α : Type u) : Type u
  | nil
  | cons
  | leaf (a : α)

instance {α : Type u} : HasList (ListLbl α) := ⟨.nil, .cons, nofun⟩

section MyList

variable {α : Type u}

def rawLeaf (a : α) : Raw ℕ (ListLbl α) := Raw.node (.leaf a) []

/-- The predicate of the parameter: a leaf carrying a value. -/
def IsLeaf (t : Raw ℕ (ListLbl α)) : Prop := ∃ a, t = rawLeaf a

noncomputable def IsLeaf.equiv : {t : Raw ℕ (ListLbl α) // IsLeaf t} ≃ α where
  toFun t := Classical.choose t.2
  invFun a := ⟨rawLeaf a, a, rfl⟩
  left_inv t := Subtype.ext (Classical.choose_spec t.2).symm
  right_inv a := by
    have h := Classical.choose_spec (⟨a, rfl⟩ : IsLeaf (rawLeaf a))
    exact (ListLbl.leaf.inj (Option.some.inj (congrArg root h))).symm

def MyList (α : Type u) : Type u := ListOf (IsLeaf (α := α))

noncomputable def MyList.equiv : MyList α ≃ List α :=
  (ListOf.equiv IsLeaf).trans (Equiv.listEquivOfEquiv IsLeaf.equiv)

end MyList

/-! ## Rose trees: `node (a : α) (children : List (Rose α))`, reusing the list transformer -/

inductive RoseLbl (α : Type u) : Type u
  | nil
  | cons
  | node (a : α)

instance {α : Type u} : HasList (RoseLbl α) := ⟨.nil, .cons, nofun⟩

section Rose

variable {α : Type u}

def rawNode (a : α) (l : Raw ℕ (RoseLbl α)) : Raw ℕ (RoseLbl α) := Raw.node (.node a) [l]

theorem rawNode_inj {a a' : α} {l l' : Raw ℕ (RoseLbl α)} :
    rawNode a l = rawNode a' l' ↔ a = a' ∧ l = l' := by
  constructor
  · intro e
    exact ⟨RoseLbl.node.inj (Option.some.inj (congrArg root e)),
      by simpa [rawNode] using congrArg (child · 0) e⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The transformer of rose trees, recursing under the list transformer. -/
def IsRose (t : Raw ℕ (RoseLbl α)) : Prop :=
  ∃ a l, t = rawNode a l ∧ IsListOf IsRose l
inductive_fixpoint

def Rose (α : Type u) : Type u := {t : Raw ℕ (RoseLbl α) // IsRose t}

namespace Rose

noncomputable def node (a : α) (cs : List (Rose α)) : Rose α :=
  ⟨rawNode a (ListOf.ofList (P := IsRose) cs).1, by
    rw [IsRose.eq_def]; exact ⟨a, _, rfl, (ListOf.ofList cs).2⟩⟩

@[simp] theorem node_inj {a a' : α} {cs cs' : List (Rose α)} :
    node a cs = node a' cs' ↔ a = a' ∧ cs = cs' := by
  constructor
  · intro e
    obtain ⟨ha, hl⟩ := rawNode_inj.mp (congrArg Subtype.val e)
    exact ⟨ha, ListOf.ofList_injective (Subtype.ext hl)⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem induction {motive : Rose α → Prop}
    (H : ∀ a (cs : List (Rose α)), (∀ c ∈ cs, motive c) → motive (node a cs)) (t : Rose α) :
    motive t := by
  obtain ⟨t, ht⟩ := t
  refine (IsRose.induct (fun t => ∃ h : IsRose t, motive ⟨t, h⟩) ?_ t ht).elim fun _ h => h
  rintro t ⟨a, l, rfl, hl⟩
  obtain ⟨l', rfl, hl'⟩ := exists_list_of_isListOf hl
  obtain ⟨cs, rfl, hcs⟩ := exists_list_subtype hl'
  exact ⟨(node a cs).2, H a cs hcs⟩

theorem cases (t : Rose α) : ∃ a cs, t = node a cs :=
  induction (motive := fun t => ∃ a cs, t = node a cs) (fun a cs _ => ⟨a, cs, rfl⟩) t

noncomputable def dest (t : Rose α) : α × List (Rose α) :=
  (Classical.choose (cases t), Classical.choose (Classical.choose_spec (cases t)))

@[simp] theorem dest_node (a : α) (cs : List (Rose α)) : dest (node a cs) = (a, cs) := by
  obtain ⟨ha, hcs⟩ :=
    node_inj.mp (Classical.choose_spec (Classical.choose_spec (cases (node a cs))))
  exact Prod.ext ha.symm hcs.symm

end Rose

/-! ### The coinductive rose trees -/

def IsCoRose (t : Raw ℕ (RoseLbl α)) : Prop :=
  ∃ a l, t = rawNode a l ∧ IsListOf IsCoRose l
coinductive_fixpoint

def CoRose (α : Type u) : Type u := {t : Raw ℕ (RoseLbl α) // IsCoRose t}

namespace CoRose

variable {S : Type u}

/-- The raw coalgebra: node states step to a node, list states step by the list's step. -/
def coalg (f : S → α × List S) : S ⊕ List S → RoseLbl α × List (S ⊕ List S)
  | .inl s => (.node (f s).1, [.inr (f s).2])
  | .inr l => listStep Sum.inl Sum.inr l

theorem corecList_coalg_inl (f : S → α × List S) (s : S) :
    corecList (coalg f) (.inl s) = rawNode (f s).1 (corecList (coalg f) (.inr (f s).2)) := by
  rw [corecList_eq]; rfl

theorem corecList_coalg_inr (f : S → α × List S) (l : List S) :
    corecList (coalg f) (.inr l) = ofList (l.map fun s => corecList (coalg f) (.inl s)) :=
  corecList_eq_ofList (coalg f) Sum.inl Sum.inr (fun _ => rfl) l

theorem isCoRose_corecList (f : S → α × List S) (s : S) :
    IsCoRose (corecList (coalg f) (.inl s)) := by
  refine IsCoRose.coinduct (fun t => ∃ s, t = corecList (coalg f) (.inl s)) ?_ _ ⟨s, rfl⟩
  rintro _ ⟨s, rfl⟩
  refine ⟨(f s).1, _, corecList_coalg_inl f s, ?_⟩
  rw [corecList_coalg_inr]
  exact isListOf_ofList (by simpa using fun s _ => ⟨s, rfl⟩)

def corec (f : S → α × List S) (s : S) : CoRose α :=
  ⟨corecList (coalg f) (.inl s), isCoRose_corecList f s⟩

def node (a : α) (cs : List (CoRose α)) : CoRose α :=
  ⟨rawNode a (ListOf.ofList (P := IsCoRose) cs).1, by
    rw [IsCoRose.eq_def]; exact ⟨a, _, rfl, (ListOf.ofList cs).2⟩⟩

theorem corec_eq (f : S → α × List S) (s : S) :
    corec f s = node (f s).1 ((f s).2.map (corec f)) := by
  refine Subtype.ext ?_
  show corecList (coalg f) (.inl s) = rawNode (f s).1 (ofList _)
  rw [corecList_coalg_inl, corecList_coalg_inr, List.map_map]
  rfl

def spine (a : α) : CoRose α := corec (fun _ : PUnit => (a, [PUnit.unit])) PUnit.unit

theorem spine_eq (a : α) : spine a = node a [spine a] := corec_eq _ _

end CoRose

end Rose

/-! ## Binary trees: `leaf | node (children : BinTree × BinTree)`, the occurrences inline -/

inductive BinLbl : Type
  | leaf
  | node

section Bin

def rawLeafB : Raw ℕ BinLbl := Raw.node .leaf []
def rawNodeB (l r : Raw ℕ BinLbl) : Raw ℕ BinLbl := Raw.node .node [l, r]

/-- Two occurrences under a product: two conjuncts. No registry, no lifting. -/
def IsBin (t : Raw ℕ BinLbl) : Prop :=
  t = rawLeafB ∨ ∃ l r, t = rawNodeB l r ∧ IsBin l ∧ IsBin r
inductive_fixpoint

def BinTree : Type := {t : Raw ℕ BinLbl // IsBin t}

namespace BinTree

def leaf : BinTree := ⟨rawLeafB, by rw [IsBin.eq_def]; exact Or.inl rfl⟩

def node (l r : BinTree) : BinTree :=
  ⟨rawNodeB l.1 r.1, by rw [IsBin.eq_def]; exact Or.inr ⟨_, _, rfl, l.2, r.2⟩⟩

theorem induction {motive : BinTree → Prop} (hleaf : motive leaf)
    (hnode : ∀ l r, motive l → motive r → motive (node l r)) (t : BinTree) : motive t := by
  obtain ⟨t, ht⟩ := t
  refine (IsBin.induct (fun t => ∃ h : IsBin t, motive ⟨t, h⟩) ?_ t ht).elim fun _ h => h
  rintro t (rfl | ⟨l, r, rfl, ⟨hl, ihl⟩, ⟨hr, ihr⟩⟩)
  · exact ⟨leaf.2, hleaf⟩
  · exact ⟨(node ⟨l, hl⟩ ⟨r, hr⟩).2, hnode _ _ ihl ihr⟩

end BinTree

end Bin

end Ambient
