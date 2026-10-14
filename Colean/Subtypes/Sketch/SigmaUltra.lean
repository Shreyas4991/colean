import Mathlib

/-! # Scratch: the initial algebra of `F X = 1 + U_σ X`

`U_σ X` is the set of countably complete ultrafilters on `X` (ultrafilters closed under countable
intersections), acting on maps by pushforward. This file defines the endofunctor
`F X = Unit ⊕ U_σ X` on `Type`, exhibits `ℕ` as an `F`-algebra, and proves it is initial.

The key fact is that every countably complete ultrafilter on a countable set is principal: if
no singleton `{n}` lies in `u`, then every complement `{n}ᶜ` does, so their countable intersection
`∅` does too. Hence `U_σ ℕ ≅ ℕ`, and `F ℕ = 1 + ℕ ≅ ℕ` with the familiar zero/successor structure.

Self-contained: uses only Mathlib.
-/

open CategoryTheory Filter

namespace SigmaUltra

/-- Countably complete ultrafilters on `X`. -/
def U (X : Type) : Type := {u : Ultrafilter X // CountableInterFilter (u : Filter X)}

namespace U

/-- Pushforward of a countably complete ultrafilter. -/
def map {X Y : Type} (f : X → Y) (u : U X) : U Y :=
  ⟨Ultrafilter.map f u.1, by
    have := u.2
    rw [Ultrafilter.coe_map]
    infer_instance⟩

/-- The principal ultrafilter at `x`. -/
def pure {X : Type} (x : X) : U X :=
  ⟨Pure.pure x, by
    rw [Ultrafilter.coe_pure, ← Filter.principal_singleton]
    infer_instance⟩

theorem map_id {X : Type} (u : U X) : map id u = u :=
  Subtype.ext (Ultrafilter.map_id u.1)

theorem map_map {X Y Z : Type} (g : Y → Z) (f : X → Y) (u : U X) :
    map g (map f u) = map (g ∘ f) u :=
  Subtype.ext (Ultrafilter.map_map u.1 f g)

theorem map_pure {X Y : Type} (f : X → Y) (x : X) : map f (pure x) = pure (f x) :=
  Subtype.ext (Ultrafilter.map_pure f x)

theorem pure_injective {X : Type} : Function.Injective (pure : X → U X) :=
  fun _ _ h ↦ Ultrafilter.pure_injective (congr_arg Subtype.val h)

/-- Every countably complete ultrafilter on a countable type is principal. -/
theorem exists_eq_pure {X : Type} [Countable X] (u : U X) : ∃ x, u = pure x := by
  by_contra h
  push_neg at h
  have hc : ∀ x : X, ({x} : Set X)ᶜ ∈ u.1 := fun x ↦ by
    rw [Ultrafilter.compl_mem_iff_notMem]
    intro hx
    obtain ⟨y, -, hu⟩ := Ultrafilter.eq_pure_of_finite_mem (Set.finite_singleton x) hx
    exact h y (Subtype.ext hu)
  have := u.2
  have hI : (⋂ x : X, ({x} : Set X)ᶜ) ∈ (u.1 : Filter X) := countable_iInter_mem.2 hc
  have hE : (⋂ x : X, ({x} : Set X)ᶜ) = ∅ := by ext y; simp
  exact Ultrafilter.empty_notMem (hE ▸ hI)

end U

/-- The endofunctor `F X = 1 + U_σ X` on `Type`. -/
def F : Type ⥤ Type where
  obj X := Unit ⊕ U X
  map f := Sum.map id (U.map f)
  map_id X := funext fun x ↦ by
    cases x with
    | inl _ => rfl
    | inr u => exact congrArg Sum.inr (U.map_id u)
  map_comp f g := funext fun x ↦ by
    cases x with
    | inl _ => rfl
    | inr u => exact congrArg Sum.inr (U.map_map g f u).symm

/-- The algebra structure on `ℕ`: `inl () ↦ 0` and `inr u ↦ n + 1` where `u = pure n`. -/
noncomputable def natStr : F.obj ℕ → ℕ
  | Sum.inl _ => 0
  | Sum.inr u => (U.exists_eq_pure u).choose + 1

theorem natStr_inl : natStr (Sum.inl ()) = 0 := rfl

theorem natStr_inr (n : ℕ) : natStr (Sum.inr (U.pure n)) = n + 1 := by
  show (U.exists_eq_pure (U.pure n)).choose + 1 = n + 1
  congr 1
  exact U.pure_injective (U.exists_eq_pure (U.pure n)).choose_spec.symm

/-- `ℕ` as an `F`-algebra. -/
noncomputable def natAlg : Endofunctor.Algebra F where
  a := ℕ
  str := natStr

/-- The recursor into an arbitrary `F`-algebra. -/
noncomputable def natRec (A : Endofunctor.Algebra F) : ℕ → A.a
  | 0 => A.str (Sum.inl ())
  | n + 1 => A.str (Sum.inr (U.pure (natRec A n)))

/-- The recursor is an algebra map. -/
noncomputable def fromNat (A : Endofunctor.Algebra F) : natAlg ⟶ A where
  f := natRec A
  h := by
    funext (x : Unit ⊕ U ℕ)
    rcases x with ⟨⟩ | u
    · rfl
    · obtain ⟨n, rfl⟩ := U.exists_eq_pure u
      change A.str (Sum.inr (U.map (natRec A) (U.pure n))) = natRec A (natStr (Sum.inr (U.pure n)))
      rw [U.map_pure, natStr_inr]
      rfl

/-- `ℕ` is the initial `F`-algebra. -/
noncomputable def natAlgIsInitial : Limits.IsInitial natAlg :=
  Limits.IsInitial.ofUniqueHom fromNat fun A g ↦ by
    ext n
    change g.f n = natRec A n
    induction n with
    | zero => exact (congr_fun g.h (Sum.inl ())).symm
    | succ n ih =>
      have := congr_fun g.h (Sum.inr (U.pure n))
      change A.str (Sum.inr (U.map g.f (U.pure n))) = g.f (natStr (Sum.inr (U.pure n))) at this
      rw [U.map_pure, natStr_inr, ih] at this
      exact this.symm

end SigmaUltra
