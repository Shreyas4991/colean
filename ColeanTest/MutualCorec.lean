import Colean.MutualCmd

/-! # Test: corecursion and coinduction per type in a `codatatype` block

Each type of a `mutual` block of `codatatype` gets the interface of a single type, with the shape of
Lean's mutual recursors: a state, a step, a morphism and a relation per type, and nothing about
the block's index `Blk.Ix` (`ctor`, `dtor`, Lambek's lemma, `corec`, `dtor_corec`, `corec_eq`,
`corec_unique`, `bisim`, the laws of the layer). The layer of a type at a family per type is
`Tₘ.F params S₁ … Sₖ idx`, the block's functor at the families packed by cases on `Blk.Ix`
(`Blk.Colean.St`), with a constructor `Tₘ.F.c` per constructor of the type, the block functor's
under the type's own name (`CEven.F.succ` for `CEven_COdd.F.CEven_succ`), for dot notation and
patterns, and shown so. -/

universe u

open Codata

namespace MutualCorecTest

noncomputable section

/-! ### Trees and forests -/

mutual
codatatype Tree (α : Type)
  | node (a : α) (children : Forest α)
codatatype Forest (α : Type)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

/--
info: @Tree.corec : {α : Type} → {S₁ S₂ : Type u_1} → (S₁ → Tree.F α S₁ S₂) → (S₂ → Forest.F α S₁ S₂) → S₁ → Tree α
-/
#guard_msgs in #check @Tree.corec

/--
info: @Tree.dtor_corec : ∀ {α : Type} {S₁ S₂ : Type u_1} (c₁ : S₁ → Tree.F α S₁ S₂) (c₂ : S₂ → Forest.F α S₁ S₂) (s : S₁),
  (Tree.corec c₁ c₂ s).dtor = Tree.F.fmap (Tree.corec c₁ c₂) (Forest.corec c₁ c₂) (c₁ s)
-/
#guard_msgs in #check @Tree.dtor_corec

/--
info: @Tree.bisim : ∀ {α : Type} (R₁ : Tree α → Tree α → Prop) (R₂ : Forest α → Forest α → Prop),
  (∀ (x y : Tree α), R₁ x y → Tree.F.Rel R₁ R₂ x.dtor y.dtor) →
    (∀ (x y : Forest α), R₂ x y → Forest.F.Rel R₁ R₂ x.dtor y.dtor) → ∀ {x y : Tree α}, R₁ x y → x = y
-/
#guard_msgs in #check @Tree.bisim

/-- info: @Tree.dtor : {α : Type} → Tree α → Tree.F α (Tree α) (Forest α) -/
#guard_msgs in #check @Tree.dtor

/--
info: @Tree.F.fmap_node : ∀ {α : Type} {X₁ X₂ : Type u_1} {Y₁ Y₂ : Type u_2} (f₁ : X₁ → Y₁) (f₂ : X₂ → Y₂) (a : α)
  (children : X₂), Tree.F.fmap f₁ f₂ (Tree.F.node a children) = Tree.F.node a (f₂ children)
-/
#guard_msgs in #check @Tree.F.fmap_node

/--
info: @Forest.dtor_cons : ∀ {α : Type} (t : Tree α) (f : Forest α), (Forest.cons t f).dtor = Forest.F.cons t f
-/
#guard_msgs in #check @Forest.dtor_cons

-- The block-level rules of the block's `dtor`, which `Tₘ.dtor` maps to the layer per type.
/--
info: @Tree_Forest.dtor_cons : ∀ {α : Type} (t : Tree α) (f : Forest α),
  Tree_Forest.dtor (Forest.cons t f) = Tree_Forest.F.cons t f
-/
#guard_msgs in #check @Tree_Forest.dtor_cons

/-- Every node labelled `a`, with one child. -/
def Tree.full {α : Type} (a : α) : Tree α :=
  Tree.corec (fun () => .node a ()) (fun () => .cons () ()) ()

def Forest.full {α : Type} (a : α) : Forest α :=
  Forest.corec (fun () => .node a ()) (fun () => .cons () ()) ()

/-- The labels count up from `0` along the first children. -/
def Tree.count : Tree Nat :=
  Tree.corec (fun n => .node n n) (fun n => .cons n (n + 1)) 0

-- The rule of `corec`, by `simp`.
@[simp] theorem Tree.dtor_full {α : Type} (a : α) :
    (Tree.full a).dtor = .node a (Forest.full a) := by
  simp [Tree.full, Forest.full]

@[simp] theorem Forest.dtor_full {α : Type} (a : α) :
    (Forest.full a).dtor = .cons (Tree.full a) (Forest.full a) := by
  simp [Tree.full, Forest.full]

example :
    Tree.count.dtor = .node 0 (Forest.corec (fun n => .node n n) (fun n => .cons n (n + 1)) 0) := by
  simp [Tree.count]

-- The destructor per type gives the layer at the types: a match takes the block functor's
-- constructors, and the fields are trees and forests (by definition).
def Tree.label {α : Type} (t : Tree α) : α :=
  match t.dtor with
  | .node a _ => a

def Forest.head? {α : Type} (f : Forest α) : Option (Tree α) :=
  match f.dtor with
  | .nil => none
  | .cons t _ => some t

example {α : Type} (a : α) : (Tree.full a).label = a := by simp [Tree.label]

-- The fields are shown as the types they are by definition (`Gen/Pack.lean`), not as the block's
-- packing `Tree_Forest.Colean.St (Tree α) (Forest α) .Forest`.
/--
trace: α : Type
t : Tree α
a : α
cs : Forest α
⊢ True
-/
#guard_msgs in
example {α : Type} (t : Tree α) : True := by
  match t.dtor with
  | .node a cs =>
    trace_state
    trivial

example {α : Type} (a : α) : (Forest.full a).head? = some (Tree.full a) := by simp [Forest.head?]

example {α : Type} (a : α) (cs : Forest α) : (Tree.node a cs).dtor = .node a cs := by simp

-- Coinduction with a relation per type: two definitions of the same trees.
def Tree.full' {α : Type} (a : α) : Tree α :=
  Tree.corec (fun n : Nat => .node a (n + 1)) (fun n : Nat => .cons (n + 1) (n + 2)) 0

theorem Tree.full'_eq {α : Type} (a : α) : Tree.full' a = Tree.full a := by
  refine Tree.bisim
    (fun x y => ∃ n, x = Tree.corec (fun n : Nat => .node a (n + 1))
      (fun n : Nat => .cons (n + 1) (n + 2)) n ∧ y = Tree.full a)
    (fun x y => ∃ n, x = Forest.corec (fun n : Nat => .node a (n + 1))
      (fun n : Nat => .cons (n + 1) (n + 2)) n ∧ y = Forest.full a) ?_ ?_ ⟨0, rfl, rfl⟩
  · rintro _ _ ⟨n, rfl, rfl⟩
    simp only [Tree.dtor_corec, Tree.dtor_full, Tree.F.fmap_node]
    exact .node _ _ _ ⟨_, rfl, rfl⟩
  · rintro _ _ ⟨n, rfl, rfl⟩
    simp only [Forest.dtor_corec, Forest.dtor_full, Forest.F.fmap_cons]
    exact .cons _ _ _ _ ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩

/-! The constructor per type, Lambek's lemma, the unfolding equation and uniqueness, as for a
single type, with one step and one morphism per type. -/

/-- info: @Tree.ctor : {α : Type} → Tree.F α (Tree α) (Forest α) → Tree α -/
#guard_msgs in #check @Tree.ctor

/-- info: @Tree.ctor_dtor : ∀ {α : Type} (t : Tree α), Tree.ctor t.dtor = t -/
#guard_msgs in #check @Tree.ctor_dtor

/-- info: @Forest.dtor_ctor : ∀ {α : Type} (y : Forest.F α (Tree α) (Forest α)), (Forest.ctor y).dtor = y -/
#guard_msgs in #check @Forest.dtor_ctor

/-- info: @Tree.ctor_injective : ∀ {α : Type}, Function.Injective Tree.ctor -/
#guard_msgs in #check @Tree.ctor_injective

/--
info: @Tree.ctor_node : ∀ {α : Type} (a : α) (children : Forest α), Tree.ctor (Tree.F.node a children) = Tree.node a children
-/
#guard_msgs in #check @Tree.ctor_node

/--
info: @Tree.corec_eq : ∀ {α : Type} {S₁ S₂ : Type u_1} (c₁ : S₁ → Tree.F α S₁ S₂) (c₂ : S₂ → Forest.F α S₁ S₂) (s : S₁),
  Tree.corec c₁ c₂ s = Tree.ctor (Tree.F.fmap (Tree.corec c₁ c₂) (Forest.corec c₁ c₂) (c₁ s))
-/
#guard_msgs in #check @Tree.corec_eq

/--
info: @Tree.corec_unique : ∀ {α : Type} {S₁ S₂ : Type u_1} (c₁ : S₁ → Tree.F α S₁ S₂) (c₂ : S₂ → Forest.F α S₁ S₂)
  (h₁ : S₁ → Tree α) (h₂ : S₂ → Forest α),
  (∀ (s : S₁), (h₁ s).dtor = Tree.F.fmap h₁ h₂ (c₁ s)) →
    (∀ (s : S₂), (h₂ s).dtor = Forest.F.fmap h₁ h₂ (c₂ s)) → ∀ (s : S₁), h₁ s = Tree.corec c₁ c₂ s
-/
#guard_msgs in #check @Tree.corec_unique

/--
info: @Forest.F.rel_fmap : ∀ {α : Type} {X₁ X₂ : Type u_1} {Y₁ Y₂ : Type u_2} {Z₁ Z₂ : Type u_3} (R₁ : Y₁ → Z₁ → Prop)
  (R₂ : Y₂ → Z₂ → Prop) (f₁ : X₁ → Y₁) (f₂ : X₂ → Y₂) (g₁ : X₁ → Z₁) (g₂ : X₂ → Z₂) (a : Forest.F α X₁ X₂),
  (∀ (x : X₁), R₁ (f₁ x) (g₁ x)) →
    (∀ (x : X₂), R₂ (f₂ x) (g₂ x)) → Forest.F.Rel R₁ R₂ (Forest.F.fmap f₁ f₂ a) (Forest.F.fmap g₁ g₂ a)
-/
#guard_msgs in #check @Forest.F.rel_fmap

-- Round trips through the constructor per type.
example {α : Type} (t : Tree α) : Tree.ctor t.dtor = t := Tree.ctor_dtor t

example {α : Type} (y : Forest.F α (Tree α) (Forest α)) : (Forest.ctor y).dtor = y :=
  Forest.dtor_ctor y

example {α : Type} (a : α) (cs : Forest α) : Tree.ctor (.node a cs) = Tree.node a cs := by simp

example {α : Type} (t : Tree α) (f : Forest α) : (Forest.ctor (.cons t f)).dtor = .cons t f := by
  simp

example {α : Type} (x y : Forest.F α (Tree α) (Forest α)) (h : Forest.ctor x = Forest.ctor y) :
    x = y :=
  Forest.ctor_injective h

/-- The unfolding equation, by `corec_eq` (not a `simp` lemma: it loops). -/
theorem Tree.full_eq {α : Type} (a : α) : Tree.full a = Tree.node a (Forest.full a) := by
  conv => lhs; rw [Tree.full, Tree.corec_eq]
  simp [Forest.full]

/-- `Tree.full'_eq` again, by uniqueness of the corecursor: the constant functions into
`Tree.full a` and `Forest.full a` satisfy the equations of the steps of `Tree.full'`. -/
example {α : Type} (a : α) : Tree.full a = Tree.full' a :=
  Tree.corec_unique (fun n : Nat => .node a (n + 1)) (fun n : Nat => .cons (n + 1) (n + 2))
    (fun _ => Tree.full a) (fun _ => Forest.full a) (fun _ => by simp) (fun _ => by simp) 0

-- The laws of the layer per type.
example {α : Type} (a : Tree.F α Nat Nat) :
    Tree.F.Rel (fun m n => m ≤ n) (fun m n => m ≤ n) (Tree.F.fmap id id a)
      (Tree.F.fmap (· + 1) (· + 1) a) :=
  Tree.F.rel_fmap _ _ _ _ _ _ a (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _)

example {α : Type} (a : Forest.F α Nat Nat) : Forest.F.fmap id id a = a := Forest.F.fmap_id a

example {α : Type} (a : Forest.F α Nat Nat) :
    Forest.F.fmap ((· * 2) ∘ (· + 1)) ((· * 2) ∘ (· + 1)) a =
      Forest.F.fmap (· * 2) (· * 2) (Forest.F.fmap (· + 1) (· + 1) a) :=
  Forest.F.fmap_comp _ _ _ _ a

-- The states may live in another universe, the same for all types.
example {α : Type} (a : α) : Tree α :=
  Tree.corec (S₁ := ULift.{2} Unit) (S₂ := ULift.{2} Unit)
    (fun _ => .node a ⟨()⟩) (fun _ => .cons ⟨()⟩ ⟨()⟩) ⟨()⟩

/-! ### Indices: even and odd streams of labels -/

mutual
codatatype Even : Nat → Type
  | succ {n : Nat} (a : Nat) (o : Odd (n + 1)) : Even n
codatatype Odd : Nat → Type
  | succ {n : Nat} (e : Even (n + 1)) : Odd n
end

-- The index binders are unnamed in the declaration, hence `i₁`.
/--
info: @Even.corec : {S₁ S₂ : Nat → Type u_1} →
  ((i₁ : Nat) → S₁ i₁ → Even.F S₁ S₂ i₁) → ((i₁ : Nat) → S₂ i₁ → Odd.F S₁ S₂ i₁) → {i₁ : Nat} → S₁ i₁ → Even i₁
-/
#guard_msgs in #check @Even.corec

/--
info: @Even.dtor_corec : ∀ {S₁ S₂ : Nat → Type u_1} (c₁ : (i₁ : Nat) → S₁ i₁ → Even.F S₁ S₂ i₁)
  (c₂ : (i₁ : Nat) → S₂ i₁ → Odd.F S₁ S₂ i₁) {i₁ : Nat} (s : S₁ i₁),
  (Even.corec c₁ c₂ s).dtor = Even.F.fmap (fun i₁ s => Even.corec c₁ c₂ s) (fun i₁ s => Odd.corec c₁ c₂ s) (c₁ i₁ s)
-/
#guard_msgs in #check @Even.dtor_corec

/-- The label at depth `n` is `n`; the state is the index. The constructors of the layer per type
are those of the type, `Even.F.succ` and `Odd.F.succ`, though the block functor qualifies the name
the two types share (`Even_Odd.F.Even_succ`). -/
def Even.nat (n : Nat) : Even n :=
  Even.corec (S₁ := fun _ => Unit) (S₂ := fun _ => Unit)
    (fun n _ => .succ n ()) (fun _ _ => .succ ()) ()

example (n : Nat) : (Even.nat n).dtor = .succ n (Odd.corec (S₁ := fun _ => Unit)
    (S₂ := fun _ => Unit) (fun n _ => .succ n ()) (fun _ _ => .succ ()) ()) := by
  simp [Even.nat]

-- Coinduction at every index: the relations are families over the indices.
example (n : Nat) : Even.nat n = Even.corec (S₁ := fun _ => Nat) (S₂ := fun _ => Nat)
    (fun n k => .succ n (k + 1)) (fun _ k => .succ (k + 1)) 0 := by
  refine Even.bisim
    (fun n x y => x = Even.nat n ∧ ∃ k, y = Even.corec (S₁ := fun _ => Nat) (S₂ := fun _ => Nat)
      (fun n k => .succ n (k + 1)) (fun _ k => .succ (k + 1)) k)
    (fun n x y => x = Odd.corec (S₁ := fun _ => Unit) (S₂ := fun _ => Unit)
      (fun n _ => .succ n ()) (fun _ _ => .succ ()) () ∧
      ∃ k, y = Odd.corec (S₁ := fun _ => Nat) (S₂ := fun _ => Nat)
        (fun n k => .succ n (k + 1)) (fun _ k => .succ (k + 1)) k) ?_ ?_ ⟨rfl, 0, rfl⟩
  · rintro n _ _ ⟨rfl, k, rfl⟩
    simp only [Even.nat, Even.dtor_corec, Even.F.fmap_succ]
    exact .Even_succ _ _ _ ⟨rfl, _, rfl⟩
  · rintro n _ _ ⟨rfl, k, rfl⟩
    simp only [Odd.dtor_corec, Odd.F.fmap_succ]
    exact .Odd_succ _ _ ⟨rfl, _, rfl⟩

/--
info: @Even.corec_unique : ∀ {S₁ S₂ : Nat → Type u_1} (c₁ : (i₁ : Nat) → S₁ i₁ → Even.F S₁ S₂ i₁)
  (c₂ : (i₁ : Nat) → S₂ i₁ → Odd.F S₁ S₂ i₁) (h₁ : (i₁ : Nat) → S₁ i₁ → Even i₁) (h₂ : (i₁ : Nat) → S₂ i₁ → Odd i₁),
  (∀ (i₁ : Nat) (s : S₁ i₁), (h₁ i₁ s).dtor = Even.F.fmap h₁ h₂ (c₁ i₁ s)) →
    (∀ (i₁ : Nat) (s : S₂ i₁), (h₂ i₁ s).dtor = Odd.F.fmap h₁ h₂ (c₂ i₁ s)) →
      ∀ {i₁ : Nat} (s : S₁ i₁), h₁ i₁ s = Even.corec c₁ c₂ s
-/
#guard_msgs in #check @Even.corec_unique

/-- info: @Odd.ctor : {i₁ : Nat} → Odd.F Even Odd i₁ → Odd i₁ -/
#guard_msgs in #check @Odd.ctor

-- Uniqueness at every index: the morphisms are families over the indices.
example (n : Nat) : Even.nat n = Even.corec (S₁ := fun _ => Nat) (S₂ := fun _ => Nat)
    (fun n k => .succ n (k + 1)) (fun _ k => .succ (k + 1)) 0 := by
  refine Even.corec_unique (S₁ := fun _ => Nat) (S₂ := fun _ => Nat)
    (fun n k => .succ n (k + 1)) (fun _ k => .succ (k + 1))
    (fun n _ => Even.nat n) (fun n _ => Odd.corec (S₁ := fun _ => Unit) (S₂ := fun _ => Unit)
      (fun n _ => .succ n ()) (fun _ _ => .succ ()) ()) ?_ ?_ 0
  · intro n k
    simp [Even.nat]
  · intro n k
    simp [Even.nat]

-- A match on the destructor, by the constructors of the layer per type.
def Even.head {n : Nat} (e : Even n) : Nat :=
  match e.dtor with
  | .succ a _ => a

def Odd.next {n : Nat} (o : Odd n) : Even (n + 1) :=
  match o.dtor with
  | .succ e => e

example (n : Nat) : (Even.nat n).head = n := by
  simp [Even.head, Even.nat]

-- The block functor's names still work.
example (n : Nat) : (Even.nat n).dtor = .Even_succ n (Odd.corec (S₁ := fun _ => Unit)
    (S₂ := fun _ => Unit) (fun n _ => .Even_succ n ()) (fun _ _ => .Odd_succ ()) ()) := by
  simp [Even.nat]

-- Goals show the constructors of the layer per type.
/--
trace: n : Nat
⊢ (Even.nat n).dtor = Even.F.succ n (Odd.corec (fun n x => Even.F.succ n ()) (fun x x_1 => Odd.F.succ ()) ())
-/
#guard_msgs in
example (n : Nat) : (Even.nat n).dtor = .succ n (Odd.corec (S₁ := fun _ => Unit)
    (S₂ := fun _ => Unit) (fun n _ => .succ n ()) (fun _ _ => .succ ()) ()) := by
  trace_state
  simp [Even.nat]

/-! ### Constructors that two types share, without indices -/

mutual
codatatype CEven
  | zero
  | succ (o : COdd)
codatatype COdd
  | succ (e : CEven)
end

/-- info: @CEven.F.succ : {S₁ S₂ : Type u_1} → S₂ → CEven.F S₁ S₂ -/
#guard_msgs in #check @CEven.F.succ

def CEven.inf : CEven := CEven.corec (fun _ => .succ ()) (fun _ => .succ ()) ()

def CEven.isZero (e : CEven) : Bool :=
  match e.dtor with
  | .zero => true
  | .succ _ => false

def COdd.pred (o : COdd) : CEven :=
  match o.dtor with
  | .succ e => e

example : CEven.inf.isZero = false := by
  simp [CEven.isZero, CEven.inf]

/-- info: CEven.dtor_succ : ∀ (o : COdd), (CEven.succ o).dtor = CEven.F.succ o -/
#guard_msgs in #check @CEven.dtor_succ

/-! ### Three types, one without constructors of its own -/

mutual
codatatype X1
  | mk (y : X2)
codatatype X2
  | mk (z : X3)
codatatype X3
  | stop
  | mk (x : X1)
end

/--
info: @X1.corec : {S₁ S₂ S₃ : Type u_1} → (S₁ → X1.F S₁ S₂ S₃) → (S₂ → X2.F S₁ S₂ S₃) → (S₃ → X3.F S₁ S₂ S₃) → S₁ → X1
-/
#guard_msgs in #check @X1.corec

/-- info: X3.ctor_dtor : ∀ (t : X3), X3.ctor t.dtor = t -/
#guard_msgs in #check @X3.ctor_dtor

example : X3.ctor .stop = X3.stop := by simp

/-- Around the cycle `n` times, then stop. -/
def X1.around (n : Nat) : X1 :=
  X1.corec (fun k => .mk k) (fun k => .mk k)
    (fun k => match k with | 0 => .stop | k + 1 => .mk k) n

example : (X1.around 0).dtor = .mk (X2.corec (fun k => .mk k) (fun k => .mk k)
    (fun k => match k with | 0 => .stop | k + 1 => .mk k) 0) := by
  simp [X1.around]

/-! ### Nesting through a list -/

mutual
codatatype Rose (α : Type)
  | node (a : α) (children : List (Rose α)) (rest : Bush α)
codatatype Bush (α : Type)
  | leaf
  | grow (b : Bush α)
end

/-- Every rose has two children, and a bush that grows forever. -/
def Rose.two {α : Type} (a : α) : Rose α :=
  Rose.corec (fun () => .node a [(), ()] ()) (fun () => .grow ()) ()

example {α : Type} (a : α) (cs : List (Rose α)) (b : Bush α) :
    (Rose.node a cs b).dtor = .node a cs b := by
  simp

example {α : Type} (a : α) : (Rose.two a).dtor = .node a [Rose.two a, Rose.two a]
    (Bush.corec (fun () => .node a [(), ()] ()) (fun () => .grow ()) ()) := by
  simp [Rose.two]

/-! ### A run of a `mixed_mutual` block that is a block: the closed types get the same
interface -/

mixed_mutual
datatype D (α : Type)
  | leaf (a : α)
  | node (s : S α)
codatatype S (α : Type)
  | cons (d : D α) (s : S α) (o : O α)
codatatype O (α : Type)
  | none
  | some (d : D α)
end

/--
info: @S.corec : {α : Type} → {S₁ S₂ : Type u_1} → (S₁ → S.F α S₁ S₂) → (S₂ → O.F α S₁ S₂) → S₁ → S α
-/
#guard_msgs in #check @S.corec

/-- Leaves labelled `a` forever. -/
def S.leaves {α : Type} (a : α) : S α :=
  S.corec (fun () => .cons (.leaf a) () ()) (fun () => .none) ()

example {α : Type} (a : α) : (S.leaves a).dtor = .cons (.leaf a) (S.leaves a)
    (O.corec (fun () => .cons (.leaf a) () ()) (fun () => .none) ()) := by
  simp [S.leaves]

end

end MutualCorecTest
