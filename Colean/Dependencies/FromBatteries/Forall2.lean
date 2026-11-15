/-!
# The relation of two lists elementwise, from Batteries

`Colean.List.Forall₂` and its `simp` lemma `forall₂_cons`, from Batteries'
`Batteries.Data.List.Basic`: the names, the arguments and the statements are Batteries', in the
namespace `Colean`, so that Colean does not depend on Batteries. Colean states the relation of
lists and arrays with it (`Occ.rel_list`, `Occ.rel_array`).
-/

namespace Colean.List

/--
`Forall₂ R l₁ l₂` means that `l₁` and `l₂` have the same length,
and whenever `a` is the nth element of `l₁`, and `b` is the nth element of `l₂`,
then `R a b` is satisfied.
-/
inductive Forall₂ (R : α → β → Prop) : List α → List β → Prop
  /-- Two nil lists are `Forall₂`-related -/
  | nil : Forall₂ R [] []
  /-- Two cons lists are related by `Forall₂ R`
  if the heads are related by `R` and the tails are related by `Forall₂ R` -/
  | cons {a b l₁ l₂} : R a b → Forall₂ R l₁ l₂ → Forall₂ R (a :: l₁) (b :: l₂)

attribute [simp] Forall₂.nil

@[simp] theorem forall₂_cons {R : α → β → Prop} {a b l₁ l₂} :
    Forall₂ R (a :: l₁) (b :: l₂) ↔ R a b ∧ Forall₂ R l₁ l₂ :=
  ⟨fun | .cons h tail => ⟨h, tail⟩, fun ⟨head, tail⟩ => .cons head tail⟩

end Colean.List
