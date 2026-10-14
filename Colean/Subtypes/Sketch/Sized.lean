import Colean.Subtypes.CodataCmd
import Mathlib.SetTheory.Ordinal.Family

-- Lean 4.34 compares implicit arguments and metavariable types without unfolding definitions.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Scratch: inductive types as coinductive families with sizes

The observation from `Test/FinVec.lean`: when every recursive argument has a strictly smaller
index, a `codata` family is finite, and `corec`/`bisim` are recursion and induction on the
index in disguise. So an inductive type could be presented as a coinductive family indexed by
a *size bound*: each constructor at `n + 1` with its recursive arguments at `n` (sized types).
Then

* `fold`, `rec`, `induction` are recursion on the size;
* a mixed inductive/coinductive block becomes one uniform `codata` block, where the order of
  the nested fixpoints is expressed by which occurrences decrease the size;
* the inductive type itself is `Σ n, T n` modulo weakening, a quotient.

The file does this for lists (`SList`, sizes in `ℕ`) and shows the limit with the example
`NatTree`: an infinitely branching inductive type has well-founded elements of no finite depth
(`inf`), so with `ℕ` as sizes the union over all sizes misses elements of the least fixpoint.
Sizes have to be ordinals (`ω` for `inf`; up to `ω₁` in general), where the native
`inductive_fixpoint` needs nothing; the last section does this: `ONatTree : Ordinal → Type 1`
with every child at a strictly smaller ordinal, and `NatTree` is the union over all sizes
modulo the size (`ONatTree.equivNatTree`), the size of a tree being its rank. Also noted: in our encoding the index is stored in every
label, so the sized families at different sizes are not subtypes of one another on `Raw`; the
union is the quotient `Σ n, SList α n` modulo weakening, not a subtype. -/

universe u

namespace Sized

noncomputable section

/-! ## Lists, sized: every `cons` decreases the bound, `nil` lives at every size -/

codata SList (α : Type u) : ℕ → Type u
  | nil {n : ℕ} : SList α n
  | cons {n : ℕ} (a : α) (l : SList α n) : SList α (n + 1)

#check @SList.corec
#check @SList.bisim

/-- Corecursion into a sized family is recursion on the size: the elements. -/
def SList.toList {α : Type u} : ∀ {n : ℕ}, SList α n → List α
  | 0, _ => []
  | _ + 1, l => match l.dtor with
    | .nil => []
    | .cons a l' => a :: SList.toList l'

@[simp] theorem SList.toList_nil {α : Type u} {n : ℕ} : (SList.nil : SList α n).toList = [] := by
  cases n <;> simp [SList.toList]

@[simp] theorem SList.toList_cons {α : Type u} {n : ℕ} (a : α) (l : SList α n) :
    (SList.cons a l).toList = a :: l.toList := by
  simp [SList.toList]

/-- Weakening, by recursion on the size: the same list at a larger bound. -/
def SList.weaken {α : Type u} : ∀ {n : ℕ}, SList α n → SList α (n + 1)
  | 0, _ => .nil
  | _ + 1, l => match l.dtor with
    | .nil => .nil
    | .cons a l' => .cons a (SList.weaken l')

@[simp] theorem SList.weaken_nil {α : Type u} {n : ℕ} :
    (SList.nil : SList α n).weaken = SList.nil := by
  cases n <;> simp [SList.weaken]

@[simp] theorem SList.weaken_cons {α : Type u} {n : ℕ} (a : α) (l : SList α n) :
    (SList.cons a l).weaken = SList.cons a l.weaken := by
  simp [SList.weaken]

theorem SList.toList_weaken {α : Type u} : ∀ {n : ℕ} (l : SList α n),
    l.weaken.toList = l.toList
  | 0, l => by cases l with | nil => simp
  | n + 1, l => by
    cases l with
    | nil => simp
    | cons a l' => simp [SList.toList_weaken l']

/-- A list at its own length: the sized family reaches every list. -/
def SList.ofList {α : Type u} : (l : List α) → SList α l.length
  | [] => .nil
  | a :: l => .cons a (SList.ofList l)

theorem SList.toList_ofList {α : Type u} (l : List α) : (SList.ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [SList.ofList, ih]

/-- Induction on the inductive type, from recursion on the size: a property of lists holds
once it holds at every size, and the size steps are the constructors. -/
theorem SList.induction {α : Type u} {motive : List α → Prop} (nil : motive [])
    (cons : ∀ a l, motive l → motive (a :: l)) : ∀ {n : ℕ} (l : SList α n), motive l.toList
  | 0, l => by cases l with | nil => simpa using nil
  | n + 1, l => by
    cases l with
    | nil => simpa using nil
    | cons a l' => simpa using cons a _ (SList.induction nil cons l')

/-! ## The inductive type: `Σ n, SList α n` modulo weakening

The bound is not part of the data, so a sized list is identified with its weakening. Then
`fold` is `Quot.lift` of the recursion on the size, which respects weakening; `induction` is
`Quot.ind`; and the dependent recursor is derived from `fold` and `induction` exactly as it
would be from the contract: fold into `Σ' l, motive l`, show by induction that the first
component is the identity, and transport. Its computation rules are propositional. -/

/-- Weakening as a relation: the generator of the quotient. -/
def Weaken {α : Type u} (p q : Σ n, SList α n) : Prop := q = ⟨p.1 + 1, p.2.weaken⟩

/-- The inductive type. -/
def SizedList (α : Type u) : Type u := Quot (Weaken (α := α))

namespace SizedList

variable {α : Type u}

def mk {n : ℕ} (l : SList α n) : SizedList α := Quot.mk _ ⟨n, l⟩

theorem mk_weaken {n : ℕ} (l : SList α n) : mk l.weaken = mk l :=
  (Quot.sound (r := Weaken) (a := ⟨n, l⟩) (b := ⟨n + 1, l.weaken⟩) rfl).symm

def nil : SizedList α := mk (n := 0) .nil

theorem mk_nil : ∀ {n : ℕ}, mk (SList.nil : SList α n) = nil
  | 0 => rfl
  | n + 1 => by rw [← SList.weaken_nil (n := n), mk_weaken, mk_nil]

def cons (a : α) (l : SizedList α) : SizedList α :=
  Quot.lift (fun p => mk (SList.cons a p.2)) (by
    rintro p _ rfl
    show mk (SList.cons a p.2) = mk (SList.cons a p.2.weaken)
    rw [← SList.weaken_cons, mk_weaken]) l

theorem cons_mk {n : ℕ} (a : α) (l : SList α n) : cons a (mk l) = mk (SList.cons a l) := rfl

/-! ### The fold: recursion on the size, which respects weakening -/

def foldS {S : Sort v} (nil : S) (cons : α → S → S) : ∀ {n : ℕ}, SList α n → S
  | 0, _ => nil
  | _ + 1, l => match l.dtor with
    | .nil => nil
    | .cons a l' => cons a (foldS nil cons l')

@[simp] theorem foldS_nil {S : Sort v} (nil : S) (cons : α → S → S) {n : ℕ} :
    foldS nil cons (SList.nil : SList α n) = nil := by
  cases n <;> simp [foldS]

@[simp] theorem foldS_cons {S : Sort v} (nil : S) (cons : α → S → S) {n : ℕ} (a : α)
    (l : SList α n) : foldS nil cons (SList.cons a l) = cons a (foldS nil cons l) := by
  simp [foldS]

theorem foldS_weaken {S : Sort v} (nil : S) (cons : α → S → S) :
    ∀ {n : ℕ} (l : SList α n), foldS nil cons l.weaken = foldS nil cons l
  | 0, l => by cases l with | nil => simp
  | n + 1, l => by
    cases l with
    | nil => simp
    | cons a l' => simp [foldS_weaken nil cons l']

def fold {S : Sort v} (nil : S) (cons : α → S → S) : SizedList α → S :=
  Quot.lift (fun p => foldS nil cons p.2) (by rintro p _ rfl; exact (foldS_weaken nil cons p.2).symm)

@[simp] theorem fold_nil {S : Sort v} (nil : S) (cons : α → S → S) :
    fold nil cons SizedList.nil = nil := foldS_nil nil cons

@[simp] theorem fold_cons {S : Sort v} (nil : S) (cons : α → S → S) (a : α) (l : SizedList α) :
    fold nil cons (SizedList.cons a l) = cons a (fold nil cons l) := by
  induction l using Quot.ind with
  | mk p => exact foldS_cons nil cons a p.2

/-! ### Induction: `Quot.ind` and recursion on the size -/

theorem induction_go {motive : SizedList α → Prop} (hnil : motive nil)
    (hcons : ∀ a l, motive l → motive (cons a l)) : ∀ (n : ℕ) (l : SList α n), motive (mk l)
  | 0, l => by cases l with | nil => exact hnil
  | n + 1, l => by
    cases l with
    | nil => rw [mk_nil]; exact hnil
    | cons a l' => exact hcons a (mk l') (induction_go hnil hcons n l')

theorem induction {motive : SizedList α → Prop} (hnil : motive nil)
    (hcons : ∀ a l, motive l → motive (cons a l)) (l : SizedList α) : motive l :=
  Quot.ind (fun p => induction_go hnil hcons p.1 p.2) l

/-! ### The dependent recursor, from `fold` and `induction` -/

/-- The algebra on the total space of the motive. -/
def recAlg {motive : SizedList α → Sort v} (hcons : ∀ a l, motive l → motive (cons a l))
    (a : α) (p : Σ' l, motive l) : Σ' l, motive l :=
  ⟨cons a p.1, hcons a p.1 p.2⟩

/-- The fold into the total space of the motive. -/
def recF {motive : SizedList α → Sort v} (hnil : motive nil)
    (hcons : ∀ a l, motive l → motive (cons a l)) : SizedList α → Σ' l, motive l :=
  fold ⟨nil, hnil⟩ (recAlg hcons)

theorem recF_fst {motive : SizedList α → Sort v} (hnil : motive nil)
    (hcons : ∀ a l, motive l → motive (cons a l)) (l : SizedList α) : (recF hnil hcons l).1 = l := by
  refine induction (motive := fun l => (recF hnil hcons l).1 = l) ?_ ?_ l
  · show (recF hnil hcons nil).1 = nil
    rw [recF, fold_nil]
  · intro a l ih
    show (recF hnil hcons (cons a l)).1 = cons a l
    rw [recF, fold_cons]
    exact congrArg (cons a) ih

def rec' {motive : SizedList α → Sort v} (hnil : motive nil)
    (hcons : ∀ a l, motive l → motive (cons a l)) (l : SizedList α) : motive l :=
  recF_fst hnil hcons l ▸ (recF hnil hcons l).2

/-- Transport out of a total space whose value is known. -/
theorem psigma_cast {β : Sort w} {motive : β → Sort v} {z : Σ' x, motive x} {x : β}
    {m : motive x} (hz : z = ⟨x, m⟩) (h : z.1 = x) : h ▸ z.2 = m := by
  subst hz
  rfl

/-- The algebra on a total-space element whose first component is known. -/
theorem recAlg_eq {motive : SizedList α → Sort v} (hcons : ∀ a l, motive l → motive (cons a l))
    (a : α) (z : Σ' l, motive l) {l : SizedList α} (h : z.1 = l) :
    recAlg hcons a z = ⟨cons a l, hcons a l (h ▸ z.2)⟩ := by
  obtain ⟨z₁, z₂⟩ := z
  subst h
  rfl

theorem rec'_nil {motive : SizedList α → Sort v} (hnil : motive nil)
    (hcons : ∀ a l, motive l → motive (cons a l)) : rec' hnil hcons nil = hnil := by
  show recF_fst hnil hcons nil ▸ (recF hnil hcons nil).2 = hnil
  exact psigma_cast (fold_nil ⟨nil, hnil⟩ (recAlg hcons)) (recF_fst hnil hcons nil)

theorem rec'_cons {motive : SizedList α → Sort v} (hnil : motive nil)
    (hcons : ∀ a l, motive l → motive (cons a l)) (a : α) (l : SizedList α) :
    rec' hnil hcons (cons a l) = hcons a l (rec' hnil hcons l) := by
  show recF_fst hnil hcons (cons a l) ▸ (recF hnil hcons (cons a l)).2 =
    hcons a l (recF_fst hnil hcons l ▸ (recF hnil hcons l).2)
  have h₁ : recF hnil hcons (cons a l) = recAlg hcons a (recF hnil hcons l) := by
    unfold recF; exact fold_cons _ _ a l
  exact psigma_cast (h₁.trans (recAlg_eq hcons a (recF hnil hcons l) (recF_fst hnil hcons l)))
    (recF_fst hnil hcons (cons a l))

/-! ### Checks: the length, and the equivalence with `List α` -/

def length (l : SizedList α) : ℕ := fold 0 (fun _ n => n + 1) l

def toList (l : SizedList α) : List α := fold [] (fun a t => a :: t) l

@[simp] theorem toList_nil : (nil : SizedList α).toList = [] := fold_nil _ _

@[simp] theorem toList_cons (a : α) (l : SizedList α) : (cons a l).toList = a :: l.toList :=
  fold_cons _ _ a l

def ofList : List α → SizedList α
  | [] => nil
  | a :: l => cons a (ofList l)

theorem toList_ofList (l : List α) : (ofList l).toList = l := by
  induction l with
  | nil => simp [ofList]
  | cons a l ih => simp [ofList, ih]

theorem ofList_toList (l : SizedList α) : ofList l.toList = l := by
  refine induction (motive := fun l => ofList l.toList = l) ?_ ?_ l
  · simp [ofList]
  · intro a l ih
    show ofList (cons a l).toList = cons a l
    simp [ofList, ih]

def equivList : SizedList α ≃ List α := ⟨toList, ofList, ofList_toList, toList_ofList⟩

end SizedList

/-! ## The limit: infinitely branching trees need ordinal sizes

`NatTree` is inductive, so every element is well-founded, but `inf` has children of every
finite depth: no natural number bounds its depth. -/

inductive NatTree
  | leaf
  | node (children : ℕ → NatTree)

def ofDepth (n : ℕ) : NatTree :=
  match n with
  | 0 => .leaf
  | m + 1 => .node (fun _ => ofDepth m)

def inf : NatTree :=
  .node (fun i => ofDepth i)

-- The sized version: every element of `SNatTree n` has depth at most `n`.
codata SNatTree : ℕ → Type
  | leaf {n : ℕ} : SNatTree n
  | node {n : ℕ} (children : ℕ → SNatTree n) : SNatTree (n + 1)

def SNatTree.toNatTree : ∀ {n : ℕ}, SNatTree n → NatTree
  | 0, _ => .leaf
  | _ + 1, t => match t.dtor with
    | .leaf => .leaf
    | .node k => .node fun i => SNatTree.toNatTree (k i)

/-- Depth at most `n`. -/
inductive NatTree.DepthLE : NatTree → ℕ → Prop
  | leaf (n : ℕ) : DepthLE .leaf n
  | node (k : ℕ → NatTree) (n : ℕ) (h : ∀ i, DepthLE (k i) n) : DepthLE (.node k) (n + 1)

theorem SNatTree.depthLE_toNatTree : ∀ {n : ℕ} (t : SNatTree n), t.toNatTree.DepthLE n
  | 0, _ => .leaf 0
  | n + 1, t => by
    cases t with
    | leaf => exact .leaf _
    | node k =>
      simp only [SNatTree.toNatTree, SNatTree.dtor_node]
      exact .node _ _ fun i => SNatTree.depthLE_toNatTree (k i)

theorem NatTree.le_of_depthLE_ofDepth : ∀ {n m : ℕ}, (ofDepth n).DepthLE m → n ≤ m
  | 0, _, _ => Nat.zero_le _
  | n + 1, m, h => by
    cases h with
    | node _ m h => exact Nat.succ_le_succ (NatTree.le_of_depthLE_ofDepth (h 0))

/-- `inf` has no finite depth bound. -/
theorem NatTree.not_depthLE_inf (m : ℕ) : ¬ inf.DepthLE m := by
  intro h
  cases h with
  | node _ m h => exact Nat.lt_irrefl _ (NatTree.le_of_depthLE_ofDepth (h (m + 1)))

/-- So `inf`, an element of the inductive type, is in no `SNatTree n`: sizes in `ℕ` are not
enough for an infinitely branching signature. -/
theorem SNatTree.toNatTree_ne_inf {n : ℕ} (t : SNatTree n) : t.toNatTree ≠ inf := fun h =>
  NatTree.not_depthLE_inf n (h ▸ SNatTree.depthLE_toNatTree t)

/-! ## Ordinal sizes: `NatTree`, faithfully

The size is a bound on the *rank*: a `node` at `o` has each child at some ordinal below `o`,
carried in the child. So `leaf` and `node` live at every `o`, there is no successor in the
index, and a limit ordinal bounds an infinitely branching node whose children have unbounded
ranks (`inf` at `ω`). The index lives in `Type 1`, so the family does too. -/

-- Every child at a strictly smaller ordinal.
codata ONatTree : Ordinal.{0} → Type 1
  | leaf {o : Ordinal.{0}} : ONatTree o
  | node {o : Ordinal.{0}} (children : ℕ → (p : Set.Iio o) × ONatTree p.1) : ONatTree o

#check @ONatTree.node
#check @ONatTree.corec

/-- The underlying tree, by well-founded recursion on the size. -/
def ONatTree.toNatTree {o : Ordinal.{0}} (t : ONatTree o) : NatTree :=
  match t.dtor with
  | .leaf => .leaf
  | .node k => .node fun i => ONatTree.toNatTree (k i).2
termination_by o
decreasing_by exact (k i).1.2

@[simp] theorem ONatTree.toNatTree_leaf {o : Ordinal.{0}} :
    (ONatTree.leaf : ONatTree o).toNatTree = .leaf := by
  rw [ONatTree.toNatTree, ONatTree.dtor_leaf]

@[simp] theorem ONatTree.toNatTree_node {o : Ordinal.{0}}
    (k : ℕ → (p : Set.Iio o) × ONatTree p.1) :
    (ONatTree.node k).toNatTree = .node fun i => (k i).2.toNatTree := by
  rw [ONatTree.toNatTree, ONatTree.dtor_node]

/-- The rank of a tree: the least ordinal above the ranks of the children. -/
def NatTree.rank : NatTree → Ordinal.{0}
  | .leaf => 0
  | .node c => ⨆ i, Order.succ (rank (c i))

theorem NatTree.rank_lt_rank_node (c : ℕ → NatTree) (i : ℕ) : (c i).rank < (NatTree.node c).rank :=
  (Order.lt_succ _).trans_le (Ordinal.le_iSup (fun i => Order.succ (c i).rank) i)

/-- Every tree is sized, at its rank. -/
def NatTree.toO : (t : NatTree) → ONatTree t.rank
  | .leaf => .leaf
  | .node c => .node fun i => ⟨⟨(c i).rank, NatTree.rank_lt_rank_node c i⟩, (c i).toO⟩

theorem NatTree.toNatTree_toO : ∀ (t : NatTree), t.toO.toNatTree = t
  | .leaf => by simp [NatTree.toO]
  | .node c => by
    simp only [NatTree.toO, ONatTree.toNatTree_node]
    exact congrArg _ (funext fun i => NatTree.toNatTree_toO (c i))

/-- The size of a sized tree bounds the rank of its tree: the rank is the least size. -/
theorem ONatTree.rank_toNatTree_le {o : Ordinal.{0}} (t : ONatTree o) : t.toNatTree.rank ≤ o := by
  induction o using WellFoundedLT.induction with
  | _ o ih =>
    cases t with
    | leaf => simp [NatTree.rank]
    | node k =>
      simp only [ONatTree.toNatTree_node, NatTree.rank]
      exact Ordinal.iSup_le fun i =>
        Order.succ_le_of_lt ((ih _ (k i).1.2 (k i).2).trans_lt (k i).1.2)

/-- So `NatTree` is the union of the sized families, modulo the size: the quotient of
`Σ o, ONatTree o` by "the same tree". With `ℕ` as sizes the map from the union was not
surjective (`SNatTree.toNatTree_ne_inf`). -/
def ONatTree.Same (p q : Σ o : Ordinal.{0}, ONatTree o) : Prop := p.2.toNatTree = q.2.toNatTree

def ONatTree.union : Quot ONatTree.Same → NatTree :=
  Quot.lift (fun p => p.2.toNatTree) fun _ _ h => h

def ONatTree.equivNatTree : Quot ONatTree.Same ≃ NatTree where
  toFun := ONatTree.union
  invFun t := Quot.mk _ ⟨t.rank, t.toO⟩
  left_inv := by
    rintro ⟨o, t⟩
    exact Quot.sound (NatTree.toNatTree_toO t.toNatTree)
  right_inv := NatTree.toNatTree_toO

/-- `inf` is sized, at rank `ω`. -/
theorem NatTree.rank_ofDepth : ∀ n : ℕ, (ofDepth n).rank = n
  | 0 => rfl
  | n + 1 => by
    simp only [ofDepth, NatTree.rank, NatTree.rank_ofDepth n, ciSup_const, Nat.cast_succ,
      Order.succ_eq_add_one]

theorem NatTree.rank_inf : inf.rank = Ordinal.omega0 := by
  simp only [inf, NatTree.rank, NatTree.rank_ofDepth]
  refine le_antisymm (Ordinal.iSup_le fun i => ?_) ?_
  · rw [Order.succ_eq_add_one, ← Nat.cast_succ]
    exact (Ordinal.lt_omega0.mpr ⟨_, rfl⟩).le
  · rw [← Ordinal.iSup_natCast]
    exact Ordinal.iSup_le fun i => (Ordinal.le_iSup (fun i : ℕ => Order.succ (i : Ordinal.{0})) i).trans'
      (Order.le_succ _)

end

end Sized
