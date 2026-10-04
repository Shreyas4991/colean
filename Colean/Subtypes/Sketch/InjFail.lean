import Colean.Subtypes.DataCmd

/-!
# Failing example: injectivity for constructors with dependent or implicit binders

Lean's `inductive` generates `injEq` for every constructor: heterogeneous equality for a field
whose type depends on an earlier field, and the binders that occur in the result index shared by
both sides. The `data` command skips such constructors, so the last two examples fail (and the
two `#check`s before them report unknown constants). Not imported by `Subtypes.lean`.
-/

namespace InjFail

/-! ### Lean's `inductive` -/

inductive W (α : Type) (β : α → Type)
  | sup (a : α) (f : β a → W α β)

inductive Vec (α : Type) : Nat → Type
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

#check @W.sup.injEq
#check @Vec.cons.injEq

example (α : Type) (β : α → Type) (a a' : α) (f : β a → W α β) (f' : β a' → W α β)
    (h : W.sup a f = W.sup a' f') : a = a' ∧ HEq f f' := by
  simpa using h

example (α : Type) (n : Nat) (a a' : α) (v v' : Vec α n) (h : Vec.cons a v = Vec.cons a' v') :
    a = a' ∧ v = v' := by
  simpa using h

/-! ### Our `data` -/

noncomputable section

data W' (α : Type) (β : α → Type)
  | sup (a : α) (f : β a → W' α β)

data Vec' (α : Type) : Nat → Type
  | nil : Vec' α 0
  | cons {n : Nat} (a : α) (v : Vec' α n) : Vec' α (n + 1)

-- The generated functor is a Lean `inductive`, so it has the lemmas in the right shape.
#check @W'.F.sup.injEq
#check @Vec'.F.cons.injEq

-- Not generated for `T` itself.
#check @W'.sup_inj
#check @Vec'.cons_inj

-- So these fail: nothing rewrites `W'.sup a f = W'.sup a' f'`.
example (α : Type) (β : α → Type) (a a' : α) (f : β a → W' α β) (f' : β a' → W' α β)
    (h : W'.sup a f = W'.sup a' f') : a = a' ∧ HEq f f' := by
  simpa using h

example (α : Type) (n : Nat) (a a' : α) (v v' : Vec' α n)
    (h : Vec'.cons a v = Vec'.cons a' v') : a = a' ∧ v = v' := by
  simpa using h

-- What works today, by hand: `ctor` is injective and `F`'s `injEq` finishes.
example (α : Type) (β : α → Type) (a a' : α) (f : β a → W' α β) (f' : β a' → W' α β)
    (h : W'.sup a f = W'.sup a' f') : a = a' ∧ HEq f f' := by
  simpa using W'.ctor_injective h

example (α : Type) (n : Nat) (a a' : α) (v v' : Vec' α n)
    (h : Vec'.cons a v = Vec'.cons a' v') : a = a' ∧ v = v' := by
  simpa using Vec'.ctor_injective h

end

end InjFail
