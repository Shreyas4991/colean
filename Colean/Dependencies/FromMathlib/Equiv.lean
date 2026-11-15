import Lean.Meta.CoeAttr

/-!
# Equivalences, from Mathlib

`Colean.Equiv` and the part of its API that Colean uses, from Mathlib's `Mathlib.Logic.Equiv.Defs`.
The names, the arguments and the statements are Mathlib's, in the namespace `Colean`, so that
Colean does not depend on Mathlib. The proofs are rewritten for core.

The notation `α ≃ β` is scoped: it is available after `open Colean` (or `open scoped Colean`), so
that it does not clash with Mathlib's when both are imported.

The coercion to functions differs from Mathlib's. Mathlib coerces through the classes `EquivLike`
and `DFunLike`, so that `e x` is `DFunLike.coe e x`. Here a `CoeFun` instance coerces by the
projection, so that `e x` is `Equiv.toFun e x`, registered as a function coercion so that it
prints as `e x` (and `⇑e` unapplied). `simp` reduces `(Equiv.mk f g l r) x` to `f x` by projection,
without lemmas.

The attributes are Mathlib's where core has them. `coe_fn_mk` is not a `grind` rule, as its
left-hand side is a projection of a constructor, which `grind` reduces itself; `Equiv.trans` has
no `@[trans]`, a Mathlib attribute.
-/

open Function

universe u v w

namespace Colean

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure Equiv (α : Sort u) (β : Sort v) where
  /-- The forward map of an equivalence. Use the coercion instead. -/
  protected toFun : α → β
  /-- The backward map of an equivalence. Use the coercion of `e.symm` instead. -/
  protected invFun : β → α
  protected left_inv : LeftInverse invFun toFun := by intro; first | rfl | ext <;> rfl
  protected right_inv : RightInverse invFun toFun := by intro; first | rfl | ext <;> rfl

@[inherit_doc]
scoped infixl:25 " ≃ " => Equiv

namespace Equiv

variable {α : Sort u} {β : Sort v} {γ : Sort w}

/-- An equivalence is applied as its forward map. -/
instance : CoeFun (α ≃ β) fun _ => α → β := ⟨Equiv.toFun⟩

open Lean Meta in
run_meta registerCoercion ``Equiv.toFun (some { numArgs := 3, coercee := 2, type := .coeFun })

@[simp] theorem coe_fn_mk (f : α → β) (g l r) : (Equiv.mk f g l r : α → β) = f :=
  rfl

/-- Inverse of an equivalence `e : α ≃ β`. -/
@[symm, implicit_reducible]
protected def symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm,
    fun x => (congrArg e₁.invFun (e₂.left_inv (e₁ x))).trans (e₁.left_inv x),
    fun z => (congrArg e₂.toFun (e₁.right_inv (e₂.invFun z))).trans (e₂.right_inv z)⟩

@[simp, grind =] theorem apply_symm_apply (e : α ≃ β) (x : β) : e (e.symm x) = x := e.right_inv x

@[simp, grind =] theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x := e.left_inv x

protected theorem injective (e : α ≃ β) : Injective e := fun a b h => by
  rw [← e.symm_apply_apply a, h, e.symm_apply_apply]

theorem symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = y ↔ x = e y :=
  ⟨fun h => by rw [← h, apply_symm_apply], fun h => by rw [h, symm_apply_apply]⟩

end Equiv

end Colean
