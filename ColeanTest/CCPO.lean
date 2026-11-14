import Colean.MutualCmd

/-! `with_ccpo`: the order of approximation on a `codata` type, for definitions by
`partial_fixpoint`. -/

namespace CCPOTest

open Lean.Order

noncomputable section

/-! ### Colists: the generated declarations -/

codata CoList (α : Type u)
  | nil
  | cons (a : α) (t : CoList α)

attribute [with_ccpo] CoList

/-- info: @CoList.instCCPO : {α : Type u_1} → CCPO (CoList α) -/
#guard_msgs in #check @CoList.instCCPO

/--
info: @CoList.approx_iff : ∀ {α : Type u_1} {x y : CoList α},
  x ⊑ y ↔ x = CoList.nil ∨ CoList.F.Rel (fun x y => x ⊑ y) x.dtor y.dtor
-/
#guard_msgs in #check @CoList.approx_iff

/-- info: @CoList.bot_eq : ∀ {α : Type u_1}, ⊥ = CoList.nil -/
#guard_msgs in #check @CoList.bot_eq

/--
info: @CoList.approx_coind : ∀ {α : Type u_1} (R : CoList α → CoList α → Prop),
  (∀ (x y : CoList α), R x y → x ⊑ y ∨ CoList.F.Rel (fun x y => R x y ∨ x ⊑ y) x.dtor y.dtor) →
    ∀ {x y : CoList α}, R x y → x ⊑ y
-/
#guard_msgs in #check @CoList.approx_coind

/--
info: @CoList.monotone_cons : ∀ {α : Type u_1} {γ : Sort u_2} [inst : Lean.Order.PartialOrder γ] (a : α) {t : γ → CoList α},
  monotone t → monotone fun x => CoList.cons a (t x)
-/
#guard_msgs in #check @CoList.monotone_cons

/-! ### Definitions by `partial_fixpoint` -/

namespace CoList

variable {α β : Type u}

def ones : CoList Nat := .cons 1 ones
partial_fixpoint

def iterate (f : α → α) (a : α) : CoList α := .cons a (iterate f (f a))
partial_fixpoint

def map (f : α → β) (s : CoList α) : CoList β :=
  match s.dtor with
  | .nil => .nil
  | .cons a t => .cons (f a) (map f t)
partial_fixpoint

def append (s t : CoList α) : CoList α :=
  match s.dtor with
  | .nil => t
  | .cons a s' => .cons a (append s' t)
partial_fixpoint

/-- Not productive in general: the bottom where no element is left. -/
def filter (p : α → Bool) (s : CoList α) : CoList α :=
  match s.dtor with
  | .nil => .nil
  | .cons a t => if p a then .cons a (filter p t) else filter p t
partial_fixpoint

/-- Not productive at all: the bottom. -/
def bad : CoList Nat := bad
partial_fixpoint

/-! ### Their fixpoint equations -/

theorem dtor_ones : ones.dtor = .cons 1 ones := by
  conv => lhs; rw [ones.eq_1]
  rw [dtor_cons]

theorem iterate_eq (f : α → α) (a : α) : iterate f a = .cons a (iterate f (f a)) := by
  rw [iterate.eq_1]

theorem map_nil (f : α → β) : map f nil = nil := by
  rw [map.eq_1, dtor_nil]

theorem map_cons (f : α → β) (a : α) (t : CoList α) :
    map f (.cons a t) = .cons (f a) (map f t) := by
  rw [map.eq_1, dtor_cons]

theorem append_cons (a : α) (s t : CoList α) :
    append (.cons a s) t = .cons a (append s t) := by
  rw [append.eq_1, dtor_cons]

theorem filter_cons (p : α → Bool) (a : α) (t : CoList α) :
    filter p (.cons a t) = if p a then .cons a (filter p t) else filter p t := by
  rw [filter.eq_1, dtor_cons]

/-- The map of a constant colist, by uniqueness of corecursion. -/
theorem map_ones (f : Nat → Nat) : map f ones = iterate id (f 1) := by
  have h : ∀ s : Unit, map f ones = corec (fun _ => .cons (f 1) ()) s := fun s =>
    corec_unique (fun _ => .cons (f 1) ()) (fun _ => map f ones) (fun _ => by
      conv => lhs; rw [ones.eq_1]
      rw [map_cons, dtor_cons, F.map_cons]) s
  have h' : ∀ s : Unit, iterate id (f 1) = corec (fun _ => .cons (f 1) ()) s := fun s =>
    corec_unique (fun _ => .cons (f 1) ()) (fun _ => iterate id (f 1)) (fun _ => by
      conv => lhs; rw [iterate_eq]
      rw [dtor_cons, F.map_cons]; rfl) s
  rw [h (), h' ()]

/-- A definition that is not productive is the bottom: below `nil` by fixpoint induction. -/
theorem bad_eq : bad = nil := by
  have h : bad ⊑ nil := bad.fixpoint_induct _ (Codata.admissible_rel _) fun _ h => h
  exact PartialOrder.rel_antisymm h (bot_eq (α := Nat) ▸ bot_le _)

/-- Filtering out everything gives the bottom, on any colist. -/
theorem filter_false (s : CoList α) : filter (fun _ => false) s = nil := by
  have h : ∀ s : CoList α, filter (fun _ => false) s ⊑ nil := by
    refine filter.fixpoint_induct (fun _ => false) (fun f => ∀ s, f s ⊑ nil)
      (admissible_pi_apply _ fun _ => Codata.admissible_rel _) fun f hf s => ?_
    dsimp only
    split
    · exact PartialOrder.rel_refl
    · exact hf _
  exact PartialOrder.rel_antisymm (h s) (bot_eq (α := α) ▸ bot_le _)

/-- The order on constructors, through `approx_iff`. -/
example (a : α) (s t : CoList α) (h : s ⊑ t) : cons a s ⊑ cons a t :=
  monotone_cons a monotone_id s t h

example (a : α) (s : CoList α) : ¬ cons a s ⊑ nil := by
  rw [approx_iff, dtor_cons, dtor_nil]
  rintro (h | h)
  · exact cons_ne_nil a s h
  · cases h

end CoList

/-! ### The bottom chosen among several constructors without arguments -/

codata Res (α : Type)
  | fail
  | done
  | ret (a : α)
  | step (r : Res α)

attribute [with_ccpo (bot := done)] Res

/-- info: @Res.bot_eq : ∀ {α : Type}, ⊥ = Res.done -/
#guard_msgs in #check @Res.bot_eq

-- The bottom written qualified.
codata Two
  | a
  | b
  | next (t : Two)

attribute [with_ccpo (bot := Two.b)] Two

/-- info: Two.bot_eq : ⊥ = Two.b -/
#guard_msgs in #check @Two.bot_eq

def Res.loop : Res Nat := .step loop
partial_fixpoint

def Res.spin : Res Nat := spin
partial_fixpoint

example : Res.spin = .done := by
  have h : Res.spin ⊑ .done := Res.spin.fixpoint_induct _ (Codata.admissible_rel _) fun _ h => h
  exact PartialOrder.rel_antisymm h (Res.bot_eq ▸ bot_le _)

/-! ### Written before the declaration -/

@[with_ccpo]
codata Stream'' (α : Type u)
  | stop
  | cons (a : α) (t : Stream'' α)

def Stream''.const (a : Nat) : Stream'' Nat := .cons a (const a)
partial_fixpoint

/-! ### Arguments under a function, and nested ones

A nested argument is ordered through its occurrence structure (`Codata.Occ.order`), and
`partial_fixpoint` goes through the maps of the leaves (`Codata.Occ.monotone_list_map`, …). -/

codata Tree (α : Type)
  | leaf
  | node (a : α) (k : Nat → Tree α)
  | rose (cs : List (Tree α)) (next : Tree α)

attribute [with_ccpo] Tree

/--
info: @Tree.monotone_node : ∀ {α : Type} {γ : Sort u_1} [inst : Lean.Order.PartialOrder γ] (a : α) {k : γ → ℕ → Tree α},
  monotone k → monotone fun x => Tree.node a (k x)
-/
#guard_msgs in #check @Tree.monotone_node

/--
info: @Tree.monotone_rose : ∀ {α : Type} {γ : Sort u_1} [inst : Lean.Order.PartialOrder γ] {cs : γ → List (Tree α)}
  {next : γ → Tree α}, monotone cs → monotone next → monotone fun x => Tree.rose (cs x) (next x)
-/
#guard_msgs in #check @Tree.monotone_rose

/-- The full tree of depth `ω` labelled by the path length. -/
def Tree.full (n : Nat) : Tree Nat := .node n fun i => full (n + i + 1)
partial_fixpoint

def Tree.chain : Tree Nat := .rose [] chain
partial_fixpoint

def Tree.map {α β : Type} (f : α → β) (t : Tree α) : Tree β :=
  match t.dtor with
  | .leaf => .leaf
  | .node a k => .node (f a) fun i => map f (k i)
  | .rose cs next => .rose (cs.map (map f)) (map f next)
partial_fixpoint

theorem Tree.map_rose {α β : Type} (f : α → β) (cs : List (Tree α)) (next : Tree α) :
    map f (.rose cs next) = .rose (cs.map (map f)) (map f next) := by
  rw [map.eq_1, dtor_rose]

-- Binary trees with optional children: through `Option.map`.
codata ORose (α : Type)
  | leaf
  | node (a : α) (l r : Option (ORose α))

attribute [with_ccpo] ORose

def ORose.map {α β : Type} (f : α → β) (t : ORose α) : ORose β :=
  match t.dtor with
  | .leaf => .leaf
  | .node a l r => .node (f a) (l.map (map f)) (r.map (map f))
partial_fixpoint

/-! ### A family, with the bottom at every index -/

codata Delay : Nat → Type
  | stop {n : Nat} : Delay n
  | now {n : Nat} (v : Fin (n + 1)) : Delay n
  | later {n : Nat} (d : Delay (n + 1)) : Delay n

attribute [with_ccpo] Delay

/-- info: @Delay.instCCPO : {i₁ : ℕ} → CCPO (Delay i₁) -/
#guard_msgs in #check @Delay.instCCPO

/--
info: @Delay.monotone_later : ∀ {γ : Sort u_1} [inst : Lean.Order.PartialOrder γ] {n : ℕ} {d : γ → Delay (n + 1)},
  monotone d → monotone fun x => (d x).later
-/
#guard_msgs in #check @Delay.monotone_later

def Delay.wait (n : Nat) (k : Nat) : Delay n :=
  if k = 0 then .now 0 else .later (wait (n + 1) (k - 1))
partial_fixpoint

def Delay.never (n : Nat) : Delay n := .later (never (n + 1))
partial_fixpoint

example (n : Nat) : Delay.never n = .later (Delay.never (n + 1)) := by
  rw [Delay.never.eq_1]

-- Nested at one index of the family.
codata DTree : Nat → Type
  | stop {n : Nat} : DTree n
  | kids {n : Nat} (cs : List (DTree (n + 1))) : DTree n

attribute [with_ccpo] DTree

/--
info: @DTree.monotone_kids : ∀ {γ : Sort u_1} [inst : Lean.Order.PartialOrder γ] {n : ℕ} {cs : γ → List (DTree (n + 1))},
  monotone cs → monotone fun x => DTree.kids (cs x)
-/
#guard_msgs in #check @DTree.monotone_kids

def DTree.wide (n : Nat) : DTree n := .kids ((List.range n).map fun _ => wide (n + 1))
partial_fixpoint

/-! ### Interaction trees: monotonicity beyond the constructors

The monotonicity of a user's function in a function argument, here `bind` in its continuation,
is proved by coinduction for the order (`approx_coind`) and registered for `partial_fixpoint`,
which then accepts recursion through it: `iter`, which need not be productive. -/

codata ITree (E : Type → Type) (R : Type)
  | spin
  | ret (r : R)
  | tau (t : ITree E R)
  | vis {X : Type} (e : E X) (k : X → ITree E R)

attribute [with_ccpo] ITree

/--
info: @ITree.monotone_vis : ∀ {E : Type → Type} {R : Type} {γ : Sort u_1} [inst : Lean.Order.PartialOrder γ] {X : Type}
  (e : E X) {k : γ → X → ITree E R}, monotone k → monotone fun x => ITree.vis e (k x)
-/
#guard_msgs in #check @ITree.monotone_vis

namespace ITree

variable {E : Type → Type} {A B C : Type}

def bind (t : ITree E A) (k : A → ITree E B) : ITree E B :=
  match t.dtor with
  | .spin => .spin
  | .ret r => k r
  | .tau t => .tau (bind t k)
  | .vis e f => .vis e fun x => bind (f x) k
partial_fixpoint

@[partial_fixpoint_monotone]
theorem monotone_bind {γ : Sort v} [PartialOrder γ] (t : ITree E A) {k : γ → A → ITree E B}
    (hk : monotone k) : monotone fun x => bind t (k x) := by
  intro x y hxy
  refine approx_coind (fun a b => ∃ t, a = bind t (k x) ∧ b = bind t (k y)) ?_ ⟨t, rfl, rfl⟩
  rintro _ _ ⟨t, rfl, rfl⟩
  rw [bind.eq_1, bind.eq_1]
  split
  · exact Or.inl (bot_eq (E := E) ▸ bot_le _)
  · exact Or.inl (hk x y hxy _)
  · rw [dtor_tau, dtor_tau]
    exact Or.inr (.tau _ _ (Or.inl ⟨_, rfl, rfl⟩))
  · rw [dtor_vis, dtor_vis]
    exact Or.inr (.vis _ _ _ fun _ => Or.inl ⟨_, rfl, rfl⟩)

/-- Iteration: recursion inside the continuation of `bind`. -/
def iter (body : A → ITree E (A ⊕ B)) (a : A) : ITree E B :=
  bind (body a) fun
    | .inl a => iter body a
    | .inr b => .ret b
partial_fixpoint

theorem iter_eq (body : A → ITree E (A ⊕ B)) (a : A) :
    iter body a = bind (body a) (Sum.elim (iter body) .ret) := by
  rw [iter.eq_1]
  congr
  funext x
  cases x <;> rfl

end ITree

/-! ### Errors -/

/-- error: with_ccpo: the order of `CoList` is already declared -/
#guard_msgs in attribute [with_ccpo] CoList

mutual
codata A
  | nilA
  | a (b : B)
codata B
  | nilB
  | b (a : A)
end

/--
error: with_ccpo: `A` is not a type declared by a single `codata` declaration (the types of `mutual` and `mixed_mutual` blocks are not supported)
-/
#guard_msgs in attribute [with_ccpo] A

mixed_mutual
data Box (α : Type)
  | mk (s : Strm α)
codata Strm (α : Type)
  | stop
  | cons (a : α) (b : Box α)
end

/--
error: with_ccpo: `Strm` is a type of an inner run of a `mixed_mutual` block, which is not supported
-/
#guard_msgs in attribute [with_ccpo] Strm

codata Grid : Nat → Nat → Type
  | stop {m n : Nat} : Grid m n

/-- error: with_ccpo: `Grid` has several indices, which are not supported yet -/
#guard_msgs in attribute [with_ccpo] Grid

/-- error: with_ccpo: the attribute is global only -/
#guard_msgs in attribute [local with_ccpo] Grid

codata Str
  | cons (a : Nat) (t : Str)

/--
error: with_ccpo: `Str` has no constructor without arguments, which the order takes as its bottom
-/
#guard_msgs in attribute [with_ccpo] Str

codata Bin
  | leaf
  | node (l r : Bin)

/--
error: with_ccpo: the bottom `Bin.node` must be a constructor without arguments
-/
#guard_msgs in attribute [with_ccpo (bot := node)] Bin

/-- error: with_ccpo: `none` is not a constructor of `Bin` -/
#guard_msgs in attribute [with_ccpo (bot := none)] Bin

-- The bottom is a named argument: the positional form does not parse.
/-- info: <input>:1:21: expected ']' -/
#guard_msgs in
run_cmd
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command "attribute [with_ccpo nil] Bin" with
  | .ok _ => Lean.logInfo "parsed"
  | .error e => Lean.logInfo e

codata Vec (α : Type) : Nat → Type
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

/--
error: with_ccpo: `Vec` has no constructor without arguments at every index, which the order takes as its bottom
-/
#guard_msgs in attribute [with_ccpo] Vec

data N
  | zero
  | succ (n : N)

/-- error: with_ccpo: `N` is a `data` type: the order is for `codata` types -/
#guard_msgs in attribute [with_ccpo] N

/--
error: with_ccpo: `Nat` is not a type declared by a single `codata` declaration (the types of `mutual` and `mixed_mutual` blocks are not supported)
-/
#guard_msgs in attribute [with_ccpo] Nat

end

end CCPOTest
