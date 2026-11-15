import Colean.Dependencies.FromBatteries.Forall2

/-!
# Lemmas on `Forall₂`, from Mathlib

The `simp` lemmas on `Colean.List.Forall₂` that Colean's users rely on, with the lemmas their
proofs use, from Mathlib's `Mathlib.Data.List.Forall2`: the names, the arguments and the statements
are Mathlib's, in the namespace `Colean`, so that Colean does not depend on Mathlib. The proofs
are rewritten for core.
-/

universe u v w

namespace Colean.List

variable {α : Type u} {β : Type v} {γ : Type w} {R : α → β → Prop} {Rₐ : α → α → Prop}

@[simp]
theorem forall₂_same : ∀ {l : List α}, Forall₂ Rₐ l l ↔ ∀ x ∈ l, Rₐ x x
  | [] => by simp
  | a :: l => by simp [@forall₂_same l]

@[simp]
theorem forall₂_nil_left_iff {l} : Forall₂ R [] l ↔ l = [] :=
  ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

@[simp]
theorem forall₂_nil_right_iff {l} : Forall₂ R l [] ↔ l = [] :=
  ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

theorem forall₂_cons_left_iff {a l u} :
    Forall₂ R (a :: l) u ↔ ∃ b u', R a b ∧ Forall₂ R l u' ∧ u = b :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂

theorem forall₂_cons_right_iff {b l u} :
    Forall₂ R u (b :: l) ↔ ∃ a u', R a b ∧ Forall₂ R u' l ∧ u = a :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂

@[simp]
theorem forall₂_map_left_iff {f : γ → α} :
    ∀ {l u}, Forall₂ R (List.map f l) u ↔ Forall₂ (fun c b => R (f c) b) l u
  | [], _ => by simp only [List.map, forall₂_nil_left_iff]
  | a :: l, _ => by simp only [List.map, forall₂_cons_left_iff, forall₂_map_left_iff]

@[simp]
theorem forall₂_map_right_iff {f : γ → β} :
    ∀ {l u}, Forall₂ R l (List.map f u) ↔ Forall₂ (fun a c => R a (f c)) l u
  | _, [] => by simp only [List.map, forall₂_nil_right_iff]
  | _, b :: u => by simp only [List.map, forall₂_cons_right_iff, forall₂_map_right_iff]

end Colean.List
