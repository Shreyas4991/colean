import Mathlib.Logic.Equiv.List
import Mathlib.Data.List.Basic
import Colean.Raw

-- Lean 4.34 compares implicit arguments and metavariable types without unfolding definitions.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Scratch: a nested type by hand, through Lean's nested fixpoints

`Rose α`, with constructor `node (a : α) (children : List (Rose α))`, defined without the
container reduction: the children are a list *inside the same `Raw`*, and the predicate of rose
trees mentions itself under the predicate of lists. `inductive_fixpoint` accepts the nested
occurrence once the list predicate is registered as monotone (`partial_fixpoint_monotone`), and
so does `coinductive_fixpoint` (`CoRose`, at the end).

What the inner type provides, once, for use by any outer type:

* its lifting to predicates, `IsListOf P`: a raw list whose elements satisfy `P`;
* monotonicity of the lifting in `P`, in the implication order (for inductive outer types) and
  in the reverse one (for coinductive outer types);
* the transport between `{l // IsListOf P l}` and native lists of `{t // P t}`, which gives the
  outer type its user-facing constructor and induction principle.

The standalone type `MyList α` is the instance `IsListOf (IsLeaf α)`: a list of leaves. -/

universe u

namespace NestedRose

/-- The labels: the constructors of lists, leaves carrying a value, and rose nodes. -/
inductive Lbl (α : Type u) : Type u
  | nil
  | cons
  | leaf (a : α)
  | node (a : α)

/-- The shared raw type. -/
abbrev R (α : Type u) : Type u := Raw ℕ (Lbl α)

variable {α : Type u}

open Raw

/-! ## The raw constructors -/

def rawNil : R α := Raw.node .nil []
def rawCons (h t : R α) : R α := Raw.node .cons [h, t]
def rawLeaf (a : α) : R α := Raw.node (.leaf a) []
def rawNode (a : α) (l : R α) : R α := Raw.node (.node a) [l]

@[simp] theorem rawNil_ne_rawCons (h t : R α) : rawNil ≠ rawCons h t := by
  intro e; simpa [rawNil, rawCons] using congrArg root e

@[simp] theorem rawCons_inj {h h' t t' : R α} :
    rawCons h t = rawCons h' t' ↔ h = h' ∧ t = t' := by
  constructor
  · intro e
    exact ⟨by simpa [rawCons] using congrArg (child · 0) e,
      by simpa [rawCons] using congrArg (child · 1) e⟩
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] theorem rawLeaf_inj {a a' : α} : rawLeaf a = rawLeaf a' ↔ a = a' :=
  ⟨fun e => by simpa [rawLeaf] using congrArg root e, fun e => e ▸ rfl⟩

@[simp] theorem rawNode_inj {a a' : α} {l l' : R α} :
    rawNode a l = rawNode a' l' ↔ a = a' ∧ l = l' := by
  constructor
  · intro e
    exact ⟨by simpa [rawNode] using congrArg root e,
      by simpa [rawNode] using congrArg (child · 0) e⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-! ## Lists over the raw type: the lifting of a predicate through the list functor -/

/-- A raw list whose elements satisfy `P`. The least fixpoint in the tail; `P` is a parameter. -/
def IsListOf (P : R α → Prop) (t : R α) : Prop :=
  t = rawNil ∨ ∃ h tl, t = rawCons h tl ∧ P h ∧ IsListOf P tl
inductive_fixpoint

section Monotone
open Lean.Order

/-- `IsListOf` is monotone in `P`, in the order of inductive predicates: registered so that an
`inductive_fixpoint` may recurse under it. -/
@[partial_fixpoint_monotone]
theorem IsListOf.monotone_ind {γ} [Lean.Order.PartialOrder γ] (f : γ → R α → ImplicationOrder) (t : R α)
    (hf : monotone f) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => IsListOf (f x) t) := by
  intro x y hxy hx
  refine IsListOf.induct (f x) (IsListOf (f y)) ?_ t hx
  rintro t (rfl | ⟨h, tl, rfl, hh, ih⟩) <;> rw [IsListOf.eq_def]
  · exact Or.inl rfl
  · exact Or.inr ⟨h, tl, rfl, monotone_apply h f hf x y hxy hh, ih⟩

/-- The same in the order of coinductive predicates, for `coinductive_fixpoint`. -/
@[partial_fixpoint_monotone]
theorem IsListOf.monotone_coind {γ} [Lean.Order.PartialOrder γ] (f : γ → R α → ReverseImplicationOrder)
    (t : R α) (hf : monotone f) :
    @monotone _ _ _ ReverseImplicationOrder.instOrder (fun x => IsListOf (f x) t) := by
  intro x y hxy hy
  refine IsListOf.induct (f y) (IsListOf (f x)) ?_ t hy
  rintro t (rfl | ⟨h, tl, rfl, hh, ih⟩) <;> rw [IsListOf.eq_def]
  · exact Or.inl rfl
  · exact Or.inr ⟨h, tl, rfl, monotone_apply h f hf x y hxy hh, ih⟩

end Monotone

/-! ### Transport to native lists -/

variable {P : R α → Prop}

theorem isListOf_rawNil : IsListOf P rawNil := by
  rw [IsListOf.eq_def]; exact Or.inl rfl

theorem isListOf_rawCons {h t : R α} (hh : P h) (ht : IsListOf P t) :
    IsListOf P (rawCons h t) := by
  rw [IsListOf.eq_def]; exact Or.inr ⟨h, t, rfl, hh, ht⟩

/-- The raw list of a native list of raw trees. -/
def ofList : List (R α) → R α
  | [] => rawNil
  | h :: l => rawCons h (ofList l)

theorem isListOf_ofList {l : List (R α)} (hl : ∀ h ∈ l, P h) : IsListOf P (ofList l) := by
  induction l with
  | nil => exact isListOf_rawNil
  | cons h l ih =>
    exact isListOf_rawCons (hl h (by simp)) (ih fun h' hh' => hl h' (by simp [hh']))

theorem ofList_injective : Function.Injective (ofList (α := α)) := by
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

/-- A raw list over `P` is the raw list of a native list of elements satisfying `P`. -/
theorem exists_list_of_isListOf {t : R α} (ht : IsListOf P t) :
    ∃ l : List (R α), t = ofList l ∧ ∀ h ∈ l, P h := by
  refine IsListOf.induct P (fun t => ∃ l, t = ofList l ∧ ∀ h ∈ l, P h) ?_ t ht
  rintro t (rfl | ⟨h, tl, rfl, hh, l, rfl, hl⟩)
  · exact ⟨[], rfl, by simp⟩
  · exact ⟨h :: l, rfl, List.forall_mem_cons.mpr ⟨hh, hl⟩⟩

/-- A native list whose elements satisfy `P`, and something about each element as a member of
the subtype, is the image of a native list of the subtype. -/
theorem exists_list_subtype {Q : {t : R α // P t} → Prop} {l : List (R α)}
    (hl : ∀ h ∈ l, ∃ hp : P h, Q ⟨h, hp⟩) :
    ∃ cs : List {t // P t}, l = cs.map Subtype.val ∧ ∀ c ∈ cs, Q c := by
  induction l with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons h l ih =>
    obtain ⟨hp, hq⟩ := hl h (by simp)
    obtain ⟨cs, rfl, hcs⟩ := ih fun h' hh' => hl h' (by simp [hh'])
    exact ⟨⟨h, hp⟩ :: cs, rfl, List.forall_mem_cons.mpr ⟨hq, hcs⟩⟩

/-- The lists over `P`. -/
def ListOf (P : R α → Prop) : Type u := {t : R α // IsListOf P t}

/-- From a native list of the subtype. -/
def ListOf.ofList (cs : List {t // P t}) : ListOf P :=
  ⟨NestedRose.ofList (cs.map Subtype.val),
    isListOf_ofList (List.forall_mem_map.mpr fun c _ => c.2)⟩

/-- Every list over `P` is `ListOf.ofList` of a native list of the subtype. -/
theorem ListOf.exists_eq_ofList (l : ListOf P) : ∃ cs : List {t // P t}, l = ListOf.ofList cs := by
  obtain ⟨t, ht⟩ := l
  obtain ⟨l', rfl, hl'⟩ := exists_list_of_isListOf ht
  obtain ⟨cs, rfl, -⟩ := exists_list_subtype (Q := fun _ => True) fun h hh => ⟨hl' h hh, trivial⟩
  exact ⟨cs, rfl⟩

theorem ListOf.ofList_injective : Function.Injective (ListOf.ofList (P := P)) := by
  intro cs cs' e
  have h : NestedRose.ofList (cs.map Subtype.val) = NestedRose.ofList (cs'.map Subtype.val) :=
    congrArg Subtype.val e
  exact List.map_injective_iff.mpr Subtype.val_injective (NestedRose.ofList_injective h)

/-- The transport to native lists of the subtype. -/
noncomputable def ListOf.equiv (P : R α → Prop) : ListOf P ≃ List {t // P t} :=
  (Equiv.ofBijective ListOf.ofList
    ⟨ListOf.ofList_injective, fun l => (ListOf.exists_eq_ofList l).imp fun _ h => h.symm⟩).symm

/-! ## The standalone list type: the instance at leaves -/

/-- A leaf carrying a value. -/
def IsLeaf (t : R α) : Prop := ∃ a, t = rawLeaf a

/-- Lists of values, as lists over leaves. -/
def MyList (α : Type u) : Type u := ListOf (IsLeaf (α := α))

/-- Leaves are the values. -/
noncomputable def IsLeaf.equiv : {t : R α // IsLeaf t} ≃ α where
  toFun t := Classical.choose t.2
  invFun a := ⟨rawLeaf a, a, rfl⟩
  left_inv t := Subtype.ext (Classical.choose_spec t.2).symm
  right_inv a := rawLeaf_inj.mp (Classical.choose_spec (⟨a, rfl⟩ : IsLeaf (rawLeaf a))).symm

/-- `MyList α` is the native `List α`. -/
noncomputable def MyList.equiv : MyList α ≃ List α :=
  (ListOf.equiv IsLeaf).trans (Equiv.listEquivOfEquiv IsLeaf.equiv)

/-! ## Rose trees: the recursive occurrence under `IsListOf` -/

/-- A node with a value and a list of rose trees. The recursive occurrence is under `IsListOf`,
accepted by the command through `IsListOf.monotone_ind`. -/
def IsRose (t : R α) : Prop :=
  ∃ a l, t = rawNode a l ∧ IsListOf IsRose l
inductive_fixpoint

#check @IsRose.induct

/-- Rose trees, as the subtype. -/
def Rose (α : Type u) : Type u := {t : R α // IsRose t}

namespace Rose

/-- The constructor, through the transport of the children. -/
def node (a : α) (cs : List (Rose α)) : Rose α :=
  ⟨rawNode a (ListOf.ofList (P := IsRose) cs).1, by
    rw [IsRose.eq_def]; exact ⟨a, _, rfl, (ListOf.ofList cs).2⟩⟩

@[simp] theorem node_inj {a a' : α} {cs cs' : List (Rose α)} :
    node a cs = node a' cs' ↔ a = a' ∧ cs = cs' := by
  constructor
  · intro e
    obtain ⟨ha, hl⟩ := rawNode_inj.mp (congrArg Subtype.val e)
    exact ⟨ha, ListOf.ofList_injective (Subtype.ext hl)⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- Induction, from the generated `IsRose.induct`: the hypothesis on the children is the list
predicate at the motive, transported to a native list. -/
theorem induction {motive : Rose α → Prop}
    (H : ∀ a (cs : List (Rose α)), (∀ c ∈ cs, motive c) → motive (node a cs)) (t : Rose α) :
    motive t := by
  obtain ⟨t, ht⟩ := t
  refine (IsRose.induct (fun t => ∃ h : IsRose t, motive ⟨t, h⟩) ?_ t ht).elim fun _ h => h
  rintro t ⟨a, l, rfl, hl⟩
  obtain ⟨l', rfl, hl'⟩ := exists_list_of_isListOf hl
  obtain ⟨cs, rfl, hcs⟩ := exists_list_subtype hl'
  exact ⟨(node a cs).2, H a cs hcs⟩

/-- Every rose tree is a node. -/
theorem cases (t : Rose α) : ∃ a cs, t = node a cs :=
  induction (motive := fun t => ∃ a cs, t = node a cs) (fun a cs _ => ⟨a, cs, rfl⟩) t

/-- The destructor. -/
noncomputable def dest (t : Rose α) : α × List (Rose α) :=
  (Classical.choose (cases t), Classical.choose (Classical.choose_spec (cases t)))

@[simp] theorem dest_node (a : α) (cs : List (Rose α)) : dest (node a cs) = (a, cs) := by
  obtain ⟨ha, hcs⟩ :=
    node_inj.mp (Classical.choose_spec (Classical.choose_spec (cases (node a cs))))
  exact Prod.ext ha.symm hcs.symm

end Rose

/-! ## The coinductive rose trees: the same, with `coinductive_fixpoint` -/

/-- Possibly infinite rose trees, finitely branching. The recursive occurrence is under
`IsListOf`, accepted through `IsListOf.monotone_coind`. -/
def IsCoRose (t : R α) : Prop :=
  ∃ a l, t = rawNode a l ∧ IsListOf IsCoRose l
coinductive_fixpoint

#check @IsCoRose.coinduct

def CoRose (α : Type u) : Type u := {t : R α // IsCoRose t}

namespace CoRose

variable {S : Type u}

/-- The states of the raw corecursion: a node state or a list of node states. -/
def coalg (f : S → α × List S) : S ⊕ List S → Lbl α × List (S ⊕ List S)
  | .inl s => (.node (f s).1, [.inr (f s).2])
  | .inr [] => (.nil, [])
  | .inr (s :: l) => (.cons, [.inl s, .inr l])

theorem corecList_coalg_inl (f : S → α × List S) (s : S) :
    corecList (coalg f) (.inl s) = rawNode (f s).1 (corecList (coalg f) (.inr (f s).2)) := by
  rw [corecList_eq]; rfl

theorem corecList_coalg_inr (f : S → α × List S) (l : List S) :
    corecList (coalg f) (.inr l) = ofList (l.map fun s => corecList (coalg f) (.inl s)) := by
  induction l with
  | nil => rw [corecList_eq]; rfl
  | cons s l ih =>
    rw [corecList_eq]; simp only [coalg, List.map_cons, List.map_nil]; rw [ofList, ← ih]; rfl

/-- The corecursion lands in the subtype, by coinduction with the image of the corecursion as
the relation; the children are a raw list over that image. -/
theorem isCoRose_corecList (f : S → α × List S) (s : S) :
    IsCoRose (corecList (coalg f) (.inl s)) := by
  refine IsCoRose.coinduct (fun t => ∃ s, t = corecList (coalg f) (.inl s)) ?_ _ ⟨s, rfl⟩
  rintro _ ⟨s, rfl⟩
  refine ⟨(f s).1, _, corecList_coalg_inl f s, ?_⟩
  rw [corecList_coalg_inr]
  exact isListOf_ofList (by simpa using fun s _ => ⟨s, rfl⟩)

/-- The corecursor. -/
def corec (f : S → α × List S) (s : S) : CoRose α :=
  ⟨corecList (coalg f) (.inl s), isCoRose_corecList f s⟩

/-- The constructor. -/
def node (a : α) (cs : List (CoRose α)) : CoRose α :=
  ⟨rawNode a (ListOf.ofList (P := IsCoRose) cs).1, by
    rw [IsCoRose.eq_def]; exact ⟨a, _, rfl, (ListOf.ofList cs).2⟩⟩

theorem corec_eq (f : S → α × List S) (s : S) :
    corec f s = node (f s).1 ((f s).2.map (corec f)) := by
  refine Subtype.ext ?_
  show corecList (coalg f) (.inl s) = rawNode (f s).1 (ofList _)
  rw [corecList_coalg_inl, corecList_coalg_inr, List.map_map]
  rfl

/-- An infinite tree: every node carries `a` and has one child, itself. -/
def spine (a : α) : CoRose α := corec (fun _ : PUnit => (a, [PUnit.unit])) PUnit.unit

theorem spine_eq (a : α) : spine a = node a [spine a] := corec_eq _ _

end CoRose

end NestedRose
