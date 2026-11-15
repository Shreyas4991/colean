import Colean.Dependencies.FromMathlib.Equiv

/-!
# Lists as tuples, from Mathlib

`Colean.List.equivSigmaTuple`, from Mathlib's `Mathlib.Data.List.OfFn`: the name, the arguments
and the statement are Mathlib's, in the namespace `Colean`, so that Colean does not depend on
Mathlib. The proofs are rewritten for core. Mathlib generates `simp` lemmas for its components
(`@[simps]`); Colean does not use them, and they are not here.
-/

universe u

namespace Colean.List

variable {α : Type u}

/-- Lists are equivalent to the sigma type of tuples of a given length. -/
def equivSigmaTuple : List α ≃ Σ n, Fin n → α where
  toFun l := ⟨l.length, l.get⟩
  invFun f := List.ofFn f.2
  left_inv l := List.ext_getElem (by simp) fun _ _ _ => by simp
  right_inv := fun ⟨n, f⟩ => by
    suffices ∀ m (h : m = n) (g : Fin m → α), (∀ i, g i = f (Fin.cast h i)) →
        (⟨m, g⟩ : Σ n, Fin n → α) = ⟨n, f⟩ from
      this _ List.length_ofFn _ fun i => by simp; rfl
    intro m h g hg
    subst h
    exact congrArg (Sigma.mk m) (funext hg)

end Colean.List
