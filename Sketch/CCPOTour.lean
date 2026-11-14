import Colean.MutualCmd

/-!
# A tour of `partial_fixpoint` on `codata` types

What the attribute `with_ccpo` gives a `codata` type, and how Lean's `partial_fixpoint` then
defines corecursive functions into it, productive or not. Read it top to bottom. Part I (sections 1
to 8) is what works, Part II (sections 9 to 13) what does not work yet but could.

How the file is checked:

* an example without an error on it works;
* the failures of Part II are left as they are, so they show as errors in the infoview;
* a failed attribute declares nothing, and a failed definition by `partial_fixpoint` is not
  declared either.

The attribute is off by default: a type without it is declared as always, and `partial_fixpoint`
into it fails: there is no order on it (Lean's fallback, the flat order of a type it can show
nonempty, makes no constructor monotone).
-/

universe u v

namespace CCPOTour

open Lean.Order

noncomputable section

/-! ## Part I: what works -/

/-! ### 1. The attribute

`with_ccpo` takes the first constructor without arguments as the bottom, `with_ccpo (bot := c)`
the constructor `c`. It orders the type by *approximation*: `x ⊑ y` when `x` is the bottom, or `x` and
`y` have the same constructor and data and related recursive arguments, coinductively. This is a
chain-complete partial order, Lean's `Lean.Order.CCPO`, which is what `partial_fixpoint` needs on
the result type of a definition. -/

codata CoList (α : Type u)
  | nil
  | cons (a : α) (t : CoList α)

attribute [with_ccpo] CoList

-- The instance, the order unfolded once, coinduction for it, the bottom.
#check @CoList.instCCPO
#check @CoList.approx_iff
#check @CoList.approx_coind
#check @CoList.bot_eq

-- A constructor is monotone in its recursive arguments: `partial_fixpoint` finds this lemma.
#check @CoList.monotone_cons

/-! ### 2. Productive definitions

A definition by `partial_fixpoint` is the least fixpoint of its equation, `f.eq_1`. Cases are by
`match` on `dtor`, which `partial_fixpoint` splits (the constructors of a `codata` type are not
those of an inductive type). -/

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

def zipWith {γ : Type u} (f : α → β → γ) (s : CoList α) (t : CoList β) : CoList γ :=
  match s.dtor, t.dtor with
  | .cons a s, .cons b t => .cons (f a b) (zipWith f s t)
  | _, _ => .nil
partial_fixpoint

theorem dtor_ones : ones.dtor = .cons 1 ones := by
  conv => lhs; rw [ones.eq_1]
  rw [dtor_cons]

theorem map_cons (f : α → β) (a : α) (t : CoList α) :
    map f (.cons a t) = .cons (f a) (map f t) := by
  rw [map.eq_1, dtor_cons]

/-! A definition by `partial_fixpoint` and one by `corec` agree when they satisfy the same
equation, by `corec_unique`. -/

theorem ones_eq_corec : ones = corec (fun _ => .cons 1 ()) () :=
  corec_unique (fun _ => .cons 1 ()) (fun _ => ones) (fun _ => by
    conv => lhs; rw [ones.eq_1]
    rw [dtor_cons, F.map_cons]) ()

/-! ### 3. Definitions that are not productive

No guard is needed: where a definition does not produce, it is the bottom. Fixpoint induction
(`f.fixpoint_induct`) with an admissible property, here being below the bottom
(`Codata.admissible_rel`), shows it. -/

def bad : CoList Nat := bad
partial_fixpoint

theorem bad_eq : bad = nil := by
  have h : bad ⊑ nil := bad.fixpoint_induct _ (Codata.admissible_rel _) fun _ h => h
  exact PartialOrder.rel_antisymm h (bot_eq (α := Nat) ▸ bot_le _)

def filter (p : α → Bool) (s : CoList α) : CoList α :=
  match s.dtor with
  | .nil => .nil
  | .cons a t => if p a then .cons a (filter p t) else filter p t
partial_fixpoint

theorem filter_false (s : CoList α) : filter (fun _ => false) s = nil := by
  have h : ∀ s : CoList α, filter (fun _ => false) s ⊑ nil := by
    refine filter.fixpoint_induct (fun _ => false) (fun f => ∀ s, f s ⊑ nil)
      (admissible_pi_apply _ fun _ => Codata.admissible_rel _) fun f hf s => ?_
    dsimp only
    split
    · exact PartialOrder.rel_refl
    · exact hf _
  exact PartialOrder.rel_antisymm (h s) (bot_eq (α := α) ▸ bot_le _)

end CoList

/-! ### 4. Choosing the bottom, and writing the attribute first

With several constructors without arguments, the bottom is named. `@[with_ccpo] codata …` is the
declaration followed by `attribute [with_ccpo] …`. -/

codata Res (α : Type)
  | fail
  | done
  | step (r : Res α)

attribute [with_ccpo (bot := done)] Res

#check @Res.bot_eq

@[with_ccpo]
codata Stream' (α : Type u)
  | stop
  | cons (a : α) (t : Stream' α)

def Stream'.const (a : Nat) : Stream' Nat := .cons a (const a)
partial_fixpoint

/-! ### 5. Arguments under a function, and nested through a leaf

Under a function the order is Lean's, pointwise. A nested argument through a leaf (`List T`,
`Option T`, `Array T`, a declared type) is ordered through the leaf's structure
(`Codata.Occ.order`: the same shape, the contents ordered), and the maps of the library's leaves
are monotone for it (`Codata.Occ.monotone_list_map`, …). -/

codata Tree (α : Type)
  | leaf
  | node (a : α) (k : Nat → Tree α)
  | rose (a : α) (cs : List (Tree α))

attribute [with_ccpo] Tree

#check @Tree.monotone_node
#check @Tree.monotone_rose

def Tree.full (n : Nat) : Tree Nat := .node n fun i => full (n + i + 1)
partial_fixpoint

def Tree.map {α β : Type} (f : α → β) (t : Tree α) : Tree β :=
  match t.dtor with
  | .leaf => .leaf
  | .node a k => .node (f a) fun i => map f (k i)
  | .rose a cs => .rose (f a) (cs.map (map f))
partial_fixpoint

/-! ### 6. Families

The bottom of a family is a constructor at every index: its result index is a variable and it has
no other argument. The order is at every index, and so is `partial_fixpoint` on a dependent
result. -/

codata Delay : Nat → Type
  | stop {n : Nat} : Delay n
  | now {n : Nat} (v : Fin (n + 1)) : Delay n
  | later {n : Nat} (d : Delay (n + 1)) : Delay n
  | fork {n : Nat} (ds : List (Delay (n + 1))) : Delay n

attribute [with_ccpo] Delay

def Delay.wait (n : Nat) (k : Nat) : Delay n :=
  if k = 0 then .now 0 else .later (wait (n + 1) (k - 1))
partial_fixpoint

def Delay.wide (n : Nat) : Delay n := .fork ((List.range 2).map fun _ => wide (n + 1))
partial_fixpoint

/-! ### 7. Monotonicity beyond the constructors

A function of the user's that a recursive call goes through needs its own monotonicity lemma;
`approx_coind` (coinduction up to the order) proves it. Here `bind` of interaction trees in its
continuation, after which `iter` is accepted: it need not be productive (`iter` of a body that
never returns is `spin`, the bottom). -/

codata ITree (E : Type → Type) (R : Type)
  | spin
  | ret (r : R)
  | tau (t : ITree E R)
  | vis {X : Type} (e : E X) (k : X → ITree E R)

attribute [with_ccpo] ITree

namespace ITree

variable {E : Type → Type} {A B : Type}

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

def iter (body : A → ITree E (A ⊕ B)) (a : A) : ITree E B :=
  bind (body a) fun
    | .inl a => iter body a
    | .inr b => .ret b
partial_fixpoint

end ITree

/-! ### 8. The outer `codata` of a mixed block

It is a single type, whose functor has the open type of the run inside: the attribute applies, and
the argument through the run inside, a declared type, is nested through a leaf. -/

namespace Mixed

mixed_mutual
codata Tree (α : Type)
  | leaf
  | node (a : α) (children : Forest α)
  | single (t : Tree α)
data Forest (α : Type)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

attribute [with_ccpo] Tree

def Tree.line : Tree Nat := .single line
partial_fixpoint

end Mixed

/-! ## Part II: what does not work yet

Everything here could be supported. -/

/-! ### 9. Several indices

The contract of a family with several indices is over their packed index (`T.Ix`), and the
instance and the lemmas would be stated curried, as the command states its own. -/

codata Grid : Nat → Nat → Type
  | stop {m n : Nat} : Grid m n
  | right {m n : Nat} (g : Grid (m + 1) n) : Grid m n

attribute [with_ccpo] Grid

/-! ### 10. Mutual blocks

A block is one family over `Blk.Ix`, so the theory applies as for a family: it needs a bottom at
every index, a constructor without arguments in every type of the block, and the instances and
lemmas per type, the attribute on one type acting for the block. -/

mutual
codata A
  | nilA
  | a (b : B)
codata B
  | nilB
  | b (a : A)
end

attribute [with_ccpo] A

/-! ### 11. The inner runs of a mixed block

The closed type is the open one at the outer types; its order would be the open type's, which is
declared with the outer types as parameters. -/

namespace Inner

mixed_mutual
data Box (α : Type)
  | mk (s : Strm α)
codata Strm (α : Type)
  | stop
  | cons (a : α) (b : Box α)
end

attribute [with_ccpo] Strm

end Inner

/-! ### 12. Recursion through a nested argument other than by a map

The order of a nested argument is that of its occurrence structure, which is not Lean's order on
products and functions, and the only monotone functions into it are the maps of the leaves. A
list built by `List.cons`, a product, a composite (`Option (List T)`), and a function into a list
need their own orders and lemmas: an order per structure, defined structurally to be Lean's where
Lean has one (functions, `PProd`), and the monotonicity of the constructors of the leaves
(`List.cons`, `Option.some`). -/

namespace Nested

codata Rose
  | leaf
  | node (cs : List Rose)
  | pair (p : Rose × Rose)
  | opt (o : Option (List Rose))
  | fan (k : Nat → List Rose)

attribute [with_ccpo] Rose

def twins : Rose := .node [twins, twins]
partial_fixpoint

def pairs : Rose := .pair (pairs, pairs)
partial_fixpoint

def opts : Rose := .opt (some [opts])
partial_fixpoint

def fans : Rose := .fan fun _ => [fans].map id
partial_fixpoint

end Nested

/-! ### 13. Cases by `T.casesOn`

`partial_fixpoint` splits the `match`es of the body, and `T.casesOn` is not one: a definition by
`T.casesOn` needs a monotonicity lemma for it, which could be generated per type (the minor
premises monotone, by cases on the value). -/

def CoList.map' {α β : Type u} (f : α → β) (s : CoList α) : CoList β :=
  CoList.casesOn (motive := fun _ => CoList β) s .nil fun a t => .cons (f a) (map' f t)
partial_fixpoint

end

end CCPOTour
