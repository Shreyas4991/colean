import Colean.MutualCmd

/-! # Test: one step of the lifting by `simp`, equality by the destructor, coinduction up to
equality

The generated `T.F.rel_cᵢ_cⱼ` (one step of `T.F.Rel` at two constructors, `simp`), with the lemmas
of `Model/Occ.lean` for the relation of a nested argument (`Occ.rel_list`, `Occ.rel_prod`, …);
`T.dtor_injective`, `T.dtor_inj` and `T.dtor_eq_cᵢ_iff`; `T.F.Rel.mono`, `T.F.rel_refl` and
`T.coinduct`. For a single type, a family (with a result index that is not a pattern), the types
of a `mutual` block and the outer type of a mixed block. The proofs are those of
`Sketch/RelHelp.lean`, Part III. -/

namespace RelSimpTest

universe u v

noncomputable section

open Codata

/-! ### A colist -/

codatatype CoList (α : Type u)
  | nil
  | cons (head : α) (tail : CoList α)

/-- info: @CoList.F.rel_cons_cons : ∀ {α : Type u_1} {X : Type u_2} {Y : Type u_3} {R : X → Y → Prop} (head : α) (tail : X)
  (head' : α) (tail' : Y),
  CoList.F.Rel R (CoList.F.cons head tail) (CoList.F.cons head' tail') ↔ head = head' ∧ R tail tail' -/
#guard_msgs in #check @CoList.F.rel_cons_cons

/-- info: @CoList.F.rel_nil_cons : ∀ {α : Type u_1} {X : Type u_2} {Y : Type u_3} {R : X → Y → Prop} (head' : α) (tail' : Y),
  CoList.F.Rel R CoList.F.nil (CoList.F.cons head' tail') ↔ False -/
#guard_msgs in #check @CoList.F.rel_nil_cons

/-- info: @CoList.F.rel_nil_nil : ∀ {α : Type u_1} {X : Type u_2} {Y : Type u_3} {R : X → Y → Prop},
  CoList.F.Rel R CoList.F.nil CoList.F.nil ↔ True -/
#guard_msgs in #check @CoList.F.rel_nil_nil

/-- info: @CoList.dtor_injective : ∀ {α : Type u_1}, Function.Injective CoList.dtor -/
#guard_msgs in #check @CoList.dtor_injective

/-- info: @CoList.dtor_inj : ∀ {α : Type u_1} {x y : CoList α}, x.dtor = y.dtor ↔ x = y -/
#guard_msgs in #check @CoList.dtor_inj

/-- info: @CoList.dtor_eq_cons_iff : ∀ {α : Type u_1} {head : α} {tail t : CoList α},
  t.dtor = CoList.F.cons head tail ↔ t = CoList.cons head tail -/
#guard_msgs in #check @CoList.dtor_eq_cons_iff

/-- info: @CoList.F.Rel.mono : ∀ {α : Type u_1} {X : Type u_2} {Y : Type u_3} {R S : X → Y → Prop},
  (∀ (x : X) (y : Y), R x y → S x y) → ∀ {a : CoList.F α X} {b : CoList.F α Y}, CoList.F.Rel R a b → CoList.F.Rel S a b -/
#guard_msgs in #check @CoList.F.Rel.mono

/-- info: @CoList.F.rel_refl : ∀ {α : Type u_1} {X : Type u_2} {R : X → X → Prop},
  (∀ (x : X), R x x) → ∀ (a : CoList.F α X), CoList.F.Rel R a a -/
#guard_msgs in #check @CoList.F.rel_refl

/-- info: @CoList.coinduct : ∀ {α : Type u_1} (R : CoList α → CoList α → Prop),
  (∀ (x y : CoList α), R x y → CoList.F.Rel (fun x y => R x y ∨ x = y) x.dtor y.dtor) →
    ∀ {x y : CoList α}, R x y → x = y -/
#guard_msgs in #check @CoList.coinduct

def CoList.map {α : Type u} {β : Type v} (f : α → β) : CoList α → CoList β :=
  CoList.corec fun s => match s.dtor with
    | .nil => .nil
    | .cons a t => .cons (f a) t

-- Unfolding equations through the destructor, by `simp`: no `conv`, no final `rfl`.
@[simp] theorem CoList.map_nil {α : Type u} {β : Type v} (f : α → β) :
    (CoList.nil : CoList α).map f = .nil := by
  apply CoList.dtor_injective
  simp [CoList.map, CoList.dtor_corec]

@[simp] theorem CoList.map_cons {α : Type u} {β : Type v} (f : α → β) (a : α) (s : CoList α) :
    (CoList.cons a s).map f = .cons (f a) (s.map f) := by
  apply CoList.dtor_injective
  simp [CoList.map, CoList.dtor_corec]

-- The bisimulation step: `simp` leaves the relation at the tails.
theorem CoList.map_map {α β γ : Type u} (f : α → β) (g : β → γ) (s : CoList α) :
    (s.map f).map g = s.map (g ∘ f) := by
  refine CoList.bisim (fun x y => ∃ s, x = (s.map f).map g ∧ y = s.map (g ∘ f)) ?_ ⟨s, rfl, rfl⟩
  rintro _ _ ⟨s, rfl, rfl⟩
  cases s with
  | nil => simp
  | cons a s =>
    simp
    exact ⟨s, rfl, rfl⟩

-- Hypotheses too.
example {α : Type u} {X Y : Type v} (R : X → Y → Prop) (a b : α) (x : X) (y : Y)
    (h : CoList.F.Rel R (.cons a x) (.cons b y)) : a = b ∧ R x y := by
  simpa using h

example {α : Type u} {X Y : Type v} (R : X → Y → Prop) (b : α) (y : Y)
    (h : CoList.F.Rel R .nil (.cons b y)) : False := by
  simp at h

-- An equation of layers is one of values.
example {α : Type u} (s t : CoList α) (a : α) (h : s.dtor = .cons a t) : s = .cons a t := by
  simpa using h

example {α : Type u} (s t : CoList α) (h : s.dtor = t.dtor) : s = t := by
  simpa using h

/-! Coinduction up to equality: once the first colist is exhausted, both sides are the same
colist, which the relation need not contain. -/

attribute [with_ccpo] CoList

def CoList.append {α : Type u} (s t : CoList α) : CoList α :=
  match s.dtor with
  | .nil => t
  | .cons a s' => .cons a (s'.append t)
partial_fixpoint

@[simp] theorem CoList.nil_append {α : Type u} (t : CoList α) : CoList.nil.append t = t := by
  rw [CoList.append]; simp

@[simp] theorem CoList.cons_append {α : Type u} (a : α) (s t : CoList α) :
    (CoList.cons a s).append t = .cons a (s.append t) := by
  rw [CoList.append]; simp

theorem CoList.append_assoc {α : Type u} (s t r : CoList α) :
    (s.append t).append r = s.append (t.append r) := by
  refine CoList.coinduct (fun x y => ∃ s, x = (s.append t).append r ∧ y = s.append (t.append r))
    ?_ ⟨s, rfl, rfl⟩
  rintro _ _ ⟨s, rfl, rfl⟩
  cases s with
  | nil => simpa using CoList.F.rel_refl (fun _ => .inr rfl) _
  | cons a s => simpa using .inl ⟨s, rfl, rfl⟩

/-! ### Interaction trees: a function argument, at one type of its domain

The two sides share the data in the types of the recursive arguments: `rel_vis_vis` is at one `X`.
-/

codatatype ITree (E : Type → Type) (R : Type)
  | ret (r : R)
  | tau (t : ITree E R)
  | vis {X : Type} (e : E X) (k : X → ITree E R)

/-- info: @ITree.F.rel_vis_vis : ∀ {E : Type → Type} {R : Type} {X : Type u_1} {Y : Type u_2} {R_1 : X → Y → Prop} {X_1 : Type}
  (e : E X_1) (k : X_1 → X) (e' : E X_1) (k' : X_1 → Y),
  ITree.F.Rel R_1 (ITree.F.vis e k) (ITree.F.vis e' k') ↔ e = e' ∧ ∀ (a : X_1), R_1 (k a) (k' a) -/
#guard_msgs in #check @ITree.F.rel_vis_vis

/-- info: @ITree.F.rel_tau_vis : ∀ {E : Type → Type} {R : Type} {X : Type u_1} {Y : Type u_2} {R_1 : X → Y → Prop} (t : X)
  {X' : Type} (e' : E X') (k' : X' → Y), ITree.F.Rel R_1 (ITree.F.tau t) (ITree.F.vis e' k') ↔ False -/
#guard_msgs in #check @ITree.F.rel_tau_vis

/-! ### Families: a result index that is a pattern, and one that is not -/

codatatype Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

/-- info: @Vec.F.rel_cons_cons : ∀ {α : Type u_1} {X : ℕ → Type u_2} {Y : ℕ → Type u_3} {R : (j₁ : ℕ) → X j₁ → Y j₁ → Prop}
  {n : ℕ} (a : α) (v : X n) (a' : α) (v' : Y n), Vec.F.Rel R (Vec.F.cons a v) (Vec.F.cons a' v') ↔ a = a' ∧ R n v v' -/
#guard_msgs in #check @Vec.F.rel_cons_cons

-- `nil` and `cons` never meet: no lemma for them.
/-- error: Unknown constant `RelSimpTest.Vec.F.rel_nil_cons` -/
#guard_msgs in #check @Vec.F.rel_nil_cons

/-- info: @Vec.dtor_eq_cons_iff : ∀ {α : Type u_1} {n : ℕ} {a : α} {v : Vec α n} {t : Vec α (n + 1)},
  t.dtor = Vec.F.cons a v ↔ t = Vec.cons a v -/
#guard_msgs in #check @Vec.dtor_eq_cons_iff

codatatype P : Nat → Type
  | mk (n : Nat) (t : P n) : P (n * 2)

/-- info: @P.F.rel_mk_mk : ∀ {X : ℕ → Type u_1} {Y : ℕ → Type u_2} {R : (j₁ : ℕ) → X j₁ → Y j₁ → Prop} (n : ℕ) (t : X n)
  (t' : Y n), P.F.Rel R (P.F.mk n t) (P.F.mk n t') ↔ R n t t' -/
#guard_msgs in #check @P.F.rel_mk_mk

example {X Y : Nat → Type} (R : ∀ n, X n → Y n → Prop) (n : Nat) (t : X n) (t' : Y n)
    (h : R n t t') : P.F.Rel R (.mk n t) (.mk n t') := by
  simpa using h

/-! Constructors whose results meet only one way round: `stop n` is at any index, `step` at a
successor. The lemma is stated where they meet, either way. -/

codatatype Lad : Nat → Type
  | stop (n : Nat) : Lad n
  | step {n : Nat} (t : Lad n) : Lad (n + 1)

/-- info: @Lad.F.rel_stop_step : ∀ {X : ℕ → Type u_1} {Y : ℕ → Type u_2} {R : (j₁ : ℕ) → X j₁ → Y j₁ → Prop} {n' : ℕ} (t' : Y n'),
  Lad.F.Rel R (Lad.F.stop (n' + 1)) (Lad.F.step t') ↔ False -/
#guard_msgs in #check @Lad.F.rel_stop_step

/-- info: @Lad.F.rel_step_stop : ∀ {X : ℕ → Type u_1} {Y : ℕ → Type u_2} {R : (j₁ : ℕ) → X j₁ → Y j₁ → Prop} {n : ℕ} (t : X n),
  Lad.F.Rel R (Lad.F.step t) (Lad.F.stop (n + 1)) ↔ False -/
#guard_msgs in #check @Lad.F.rel_step_stop

/-! ### Nested through `List`, `Option` and a product -/

codatatype Rose (α : Type u)
  | node (a : α) (cs : List (Rose α))

/-- info: @Rose.F.rel_node_node : ∀ {α : Type u_1} {X : Type u_2} {Y : Type u_3} {R : X → Y → Prop} (a : α) (cs : List X) (a' : α)
  (cs' : List Y),
  Rose.F.Rel R (Rose.F.node a cs) (Rose.F.node a' cs') ↔ a = a' ∧ (Occ.ofIso List).Rel (Occ.ofIso List) R cs cs' -/
#guard_msgs in #check @Rose.F.rel_node_node

def Rose.map {α : Type u} {β : Type v} (f : α → β) : Rose α → Rose β :=
  Rose.corec fun t => match t.dtor with
    | .node a cs => .node (f a) cs

theorem Rose.map_node {α : Type u} {β : Type v} (f : α → β) (a : α) (cs : List (Rose α)) :
    (Rose.node a cs).map f = .node (f a) (cs.map (Rose.map f)) := by
  apply Rose.dtor_injective
  simp [Rose.map, Rose.dtor_corec]

-- The premise of the step becomes `List.Forall₂`, and Mathlib's lemmas about it finish.
example {α β γ : Type u} (f : α → β) (g : β → γ) (t : Rose α) :
    (t.map f).map g = t.map (g ∘ f) := by
  refine Rose.bisim (fun x y => ∃ t, x = (t.map f).map g ∧ y = t.map (g ∘ f)) ?_ ⟨t, rfl, rfl⟩
  rintro _ _ ⟨t, rfl, rfl⟩
  cases t with
  | node a cs =>
    simp [Rose.map_node]
    exact fun t _ => ⟨t, rfl, rfl⟩

codatatype OStr (α : Type u)
  | cons (a : α) (t : Option (OStr α))

example {α : Type u} {X Y : Type v} (R : X → Y → Prop) (a : α) (x : X) (y : Y) (h : R x y) :
    OStr.F.Rel R (.cons a (some x)) (.cons a (some y)) := by
  simpa using h

example {α : Type u} {X Y : Type v} (R : X → Y → Prop) (a : α) (x : X) :
    ¬ OStr.F.Rel (Y := Y) R (.cons a (some x)) (.cons a none) := by
  simp

codatatype Bin (α : Type u)
  | leaf
  | node (a : α) (p : Bin α × Bin α)

/-- info: @Bin.F.rel_node_node : ∀ {α : Type u_1} {X : Type u_2} {Y : Type u_3} {R : X → Y → Prop} (a : α) (p : X × X) (a' : α)
  (p' : Y × Y),
  Bin.F.Rel R (Bin.F.node a p) (Bin.F.node a' p') ↔
    a = a' ∧ (Occ.hole.prod Occ.hole).Rel (Occ.hole.prod Occ.hole) R p p' -/
#guard_msgs in #check @Bin.F.rel_node_node

example {α : Type u} {X Y : Type v} (R : X → Y → Prop) (a : α) (x₁ x₂ : X) (y₁ y₂ : Y)
    (h₁ : R x₁ y₁) (h₂ : R x₂ y₂) :
    Bin.F.Rel R (.node a (x₁, x₂)) (.node a (y₁, y₂)) := by
  simp [h₁, h₂]

/-! ### Nested through a declared type

The premise is the relation of `CoList`'s structure as a leaf. On a variable, a map on either side
moves into the relation, and a value related to itself is a relation at its members: `simp` closes
the step of `map id`. -/

codatatype NRose (α : Type u)
  | node (a : α) (cs : CoList (NRose α))

/-- info: @NRose.F.rel_node_node : ∀ {α : Type u_1} {X : Type u_2} {Y : Type u_3} {R : X → Y → Prop} (a : α) (cs : CoList X)
  (a' : α) (cs' : CoList Y),
  NRose.F.Rel R (NRose.F.node a cs) (NRose.F.node a' cs') ↔ a = a' ∧ (Occ.ofIso CoList).Rel (Occ.ofIso CoList) R cs cs' -/
#guard_msgs in #check @NRose.F.rel_node_node

def NRose.map {α : Type u} {β : Type u} (f : α → β) : NRose α → NRose β :=
  NRose.corec fun t => match t.dtor with
    | .node a cs => .node (f a) cs

example {α : Type u} (t : NRose α) : t.map id = t := by
  refine NRose.bisim (fun x y => x = y.map id) ?_ rfl
  rintro _ y rfl
  cases y with
  | node a cs => simp [NRose.map, NRose.dtor_corec]

/-! ### A `mutual` block: per type, with a relation per type -/

namespace Mutual

mutual
codatatype Tree (α : Type u)
  | node (a : α) (children : Forest α)
codatatype Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

/-- info: @Tree.F.rel_node_node : ∀ {α : Type u_1} {X₁ X₂ : Type u_2} {Y₁ Y₂ : Type u_3} {R₁ : X₁ → Y₁ → Prop}
  {R₂ : X₂ → Y₂ → Prop} (a : α) (children : X₂) (a' : α) (children' : Y₂),
  Tree.F.Rel R₁ R₂ (Tree_Forest.F.node a children) (Tree_Forest.F.node a' children') ↔ a = a' ∧ R₂ children children' -/
#guard_msgs in #check @Tree.F.rel_node_node

/-- info: @Forest.F.rel_cons_cons : ∀ {α : Type u_1} {X₁ X₂ : Type u_2} {Y₁ Y₂ : Type u_3} {R₁ : X₁ → Y₁ → Prop}
  {R₂ : X₂ → Y₂ → Prop} (t : X₁) (f : X₂) (t' : Y₁) (f' : Y₂),
  Forest.F.Rel R₁ R₂ (Tree_Forest.F.cons t f) (Tree_Forest.F.cons t' f') ↔ R₁ t t' ∧ R₂ f f' -/
#guard_msgs in #check @Forest.F.rel_cons_cons

/-- info: @Forest.F.Rel.mono : ∀ {α : Type u_1} {X₁ X₂ : Type u_2} {Y₁ Y₂ : Type u_3} {R₁ : X₁ → Y₁ → Prop} {R₂ : X₂ → Y₂ → Prop}
  {S₁ : X₁ → Y₁ → Prop} {S₂ : X₂ → Y₂ → Prop},
  (∀ (x : X₁) (y : Y₁), R₁ x y → S₁ x y) →
    (∀ (x : X₂) (y : Y₂), R₂ x y → S₂ x y) →
      ∀ {a : Forest.F α X₁ X₂} {b : Forest.F α Y₁ Y₂}, Forest.F.Rel R₁ R₂ a b → Forest.F.Rel S₁ S₂ a b -/
#guard_msgs in #check @Forest.F.Rel.mono

/-- info: @Tree.coinduct : ∀ {α : Type u_1} (R₁ : Tree α → Tree α → Prop) (R₂ : Forest α → Forest α → Prop),
  (∀ (x y : Tree α), R₁ x y → Tree.F.Rel (fun x y => R₁ x y ∨ x = y) (fun x y => R₂ x y ∨ x = y) x.dtor y.dtor) →
    (∀ (x y : Forest α), R₂ x y → Forest.F.Rel (fun x y => R₁ x y ∨ x = y) (fun x y => R₂ x y ∨ x = y) x.dtor y.dtor) →
      ∀ {x y : Tree α}, R₁ x y → x = y -/
#guard_msgs in #check @Tree.coinduct

/-- info: @Forest.dtor_inj : ∀ {α : Type u_1} {x y : Forest α}, x.dtor = y.dtor ↔ x = y -/
#guard_msgs in #check @Forest.dtor_inj

def Tree.full {α : Type u} (a : α) : Tree α :=
  Tree.corec (fun () => .node a ()) (fun () => .cons () ()) ()
def Forest.full {α : Type u} (a : α) : Forest α :=
  Forest.corec (fun () => .node a ()) (fun () => .cons () ()) ()

/-- The same trees, with a counter in the states. -/
def Tree.count {α : Type u} (a : α) (n : Nat) : Tree α :=
  Tree.corec (fun n => .node a (n + 1)) (fun n => .cons (n + 1) (n + 1)) n
def Forest.count {α : Type u} (a : α) (n : Nat) : Forest α :=
  Forest.corec (fun n => .node a (n + 1)) (fun n => .cons (n + 1) (n + 1)) n

-- `simp` closes both steps.
example {α : Type u} (a : α) (n : Nat) : Tree.full a = Tree.count a n := by
  refine Tree.bisim (fun x y => x = Tree.full a ∧ ∃ k, y = Tree.count a k)
    (fun x y => x = Forest.full a ∧ ∃ k, y = Forest.count a k) ?_ ?_ ⟨rfl, n, rfl⟩
  · rintro _ _ ⟨rfl, k, rfl⟩
    simp [Tree.full, Tree.count, Forest.full, Forest.count, Tree.dtor_corec]
  · rintro _ _ ⟨rfl, k, rfl⟩
    simp [Tree.full, Tree.count, Forest.full, Forest.count, Forest.dtor_corec]

-- Unfolding through the destructor per type.
example {α : Type u} (a : α) : Forest.full a = .cons (Tree.full a) (Forest.full a) := by
  apply Forest.dtor_injective
  simp [Tree.full, Forest.full, Forest.dtor_corec]

/-! A nested argument in a block: its premise is the block's indexed structure at the relations
packed by cases, which `simp` takes back to the relation of its type (`IOcc.rel_ofOcc`). -/

mutual
codatatype LTree (α : Type u)
  | node (a : α) (cs : List (LTree α)) (f : LForest α)
codatatype LForest (α : Type u)
  | nil
  | cons (t : LTree α) (f : LForest α)
end

example {α : Type u} {X₁ X₂ Y₁ Y₂ : Type} (R₁ : X₁ → Y₁ → Prop) (R₂ : X₂ → Y₂ → Prop) (a : α)
    (x : X₁) (y : Y₁) (f : X₂) (g : Y₂) :
    LTree.F.Rel R₁ R₂ (.node a [x] f) (.node a [y] g) ↔ R₁ x y ∧ R₂ f g := by
  simp

end Mutual

/-! ### A family with two indices, nested through `List` and a product -/

codatatype G : Nat → Bool → Type
  | mk (n : Nat) (b : Bool) (ts : List (G n b)) (p : G n b × G (n + 1) b) : G n b

example {X Y : Nat → Bool → Type} (R : ∀ n b, X n b → Y n b → Prop) (n : Nat) (b : Bool)
    (x : X n b) (y : Y n b) (x₂ : X (n + 1) b) (y₂ : Y (n + 1) b) :
    G.F.Rel R (.mk n b [x] (x, x₂)) (.mk n b [y] (y, y₂)) ↔
      R n b x y ∧ R n b x y ∧ R (n + 1) b x₂ y₂ := by
  simp

/-! ### The outer type of a mixed block: at the open forests -/

namespace Mixed

mixed_mutual
codatatype Tree (α : Type u)
  | node (a : α) (children : Forest α)
datatype Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

/-- info: @Tree.F.rel_node_node : ∀ {α : Type u_1} {X : Type u_2} {Y : Type u_3} {R : X → Y → Prop} (a : α)
  (children : Forest.Open α X) (a' : α) (children' : Forest.Open α Y),
  Tree.F.Rel R (Tree.F.node a children) (Tree.F.node a' children') ↔
    a = a' ∧ (Occ.ofIso (Forest.Open α)).Rel (Occ.ofIso (Forest.Open α)) R children children' -/
#guard_msgs in #check @Tree.F.rel_node_node

/-- info: @Forest.dtor_eq_cons_iff : ∀ {α : Type u_1} {t : Tree α} {f x : Forest α},
  x.dtor = Forest.F.cons t f ↔ x = Forest.cons t f -/
#guard_msgs in #check @Forest.dtor_eq_cons_iff

def Tree.relabel {α : Type u} (h : α → α) : Tree α → Tree α :=
  Tree.corec fun t => match t.dtor with | .node a cs => .node (h a) cs

example {α : Type u} (t : Tree α) : Tree.relabel id t = t := by
  refine Tree.bisim (fun x y => x = Tree.relabel id y) ?_ rfl
  rintro _ y rfl
  cases y with
  | node a cs => simp [Tree.relabel, Tree.dtor_corec]

end Mixed

/-! ### The relation of the occurrence structures -/

example {X Y : Type u} (R : X → Y → Prop) (x : X) (y : Y) (l : List X) (l' : List Y) :
    (Occ.ofIso List).Rel (Occ.ofIso List) R (x :: l) (y :: l') ↔
      R x y ∧ (Occ.ofIso List).Rel (Occ.ofIso List) R l l' := by
  simp

example {X : Type u} (R : X → X → Prop) (f g : X → X) (l : List X) :
    (Occ.ofIso List).Rel (Occ.ofIso List) R (l.map f) (l.map g) ↔ ∀ x ∈ l, R (f x) (g x) := by
  simp [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]

example {X Y : Type u} (R : X → Y → Prop) (k : Nat → Option X) (k' : Nat → Option Y) :
    (Occ.pi Nat fun _ => Occ.ofIso Option).Rel (Occ.pi Nat fun _ => Occ.ofIso Option) R k k' ↔
      ∀ n, Option.Rel R (k n) (k' n) := by
  simp

end

end RelSimpTest
