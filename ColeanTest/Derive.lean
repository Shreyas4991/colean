import Colean.MutualCmd

/-! # Test: `PolyIso` instances of declared types

Declaring a type generates its instances, in a separate step after the declaration. No instance
is written by hand here. -/

universe u v

namespace DeriveTest

open Codata

/-! ### One parameter -/

codatatype Str (α : Type u)
  | cons (a : α) (t : Str α)

datatype L (α : Type u)
  | nil
  | cons (a : α) (t : L α)

#synth PolyIso Str.{0} _ _
#synth PolyIso L.{0} _ _
#synth PolyIso (fun X : Type u => L (List X)) _ _
#synth PolyMap L.{0} L.{1}

/-! ### Nesting through them, in every combination of kinds -/

datatype Rose
  | node (cs : L Rose)

codatatype Inf
  | node (cs : L Inf)

-- Inductive through coinductive, which Lean's `inductive` has no counterpart of.
datatype Bush
  | leaf
  | node (c : Str Bush)

codatatype CoBush
  | node (c : Str CoBush)

-- A composite: the premise of the instance.
codatatype Mix
  | node (c : L (List Mix))

/-! ### Several parameters: one instance, composed with constants and with the identity -/

datatype E (α β : Type u)
  | l (a : α)
  | r (b : β)

#synth PolyIso (fun X : Type u => E X X) _ _
#synth PolyIso (fun X : Type => E X Nat) _ _
#synth PolyIso (E Nat) _ _
#synth PolyIso (fun X : Type u => E (List X) (Option X)) _ _

datatype T₁
  | leaf
  | mk (p : E T₁ T₁)

codatatype T₂
  | mk (p : List (E Nat T₂))

datatype T₃
  | leaf
  | mk (p : E (List T₃) (Option T₃))

/-! ### Other fields -/

-- A product in a field, and nesting inside the type.
datatype Two (α : Type u)
  | mk (p : α × α)

datatype Tw
  | leaf
  | mk (p : Two Tw)

datatype Rose₂ (α : Type u)
  | node (a : α) (cs : List (Rose₂ α))

datatype Rose₃
  | mk (r : Rose₂ Rose₃)

-- A constant parameter and a telescope.
datatype Fn (A : Type) (α : Type u)
  | leaf (a : α)
  | node (k : A → Fn A α)

datatype UseFn
  | mk (f : Fn Nat UseFn)

/-! ### Parameters that cannot vary: nothing is generated, silently -/

datatype Neg (α : Type u)
  | mk (f : α → Nat)

datatype Dep (α : Type)
  | mk (a : α) (h : a = a)

/--
error: no `Codata.PolyIso` instance for `Neg`; to nest through a type constructor, give it `Codata.PolyIso` and `Codata.PolyMap` instances (`Colean/PolyIso.lean`); products, sums, functions and dependent pairs over constant types need none
-/
#guard_msgs in
datatype NoNest
  | mk (x : Neg NoNest)

/-! ### The map is the structural one -/

noncomputable section

abbrev idH : Type → Type := fun X => X

example {X Y : Type} (f : X → Y) (a : Str X) :
    Str.Colean.Poly.toL idH ((Str.Colean.Poly.fix idH X).map (Str.Colean.Poly.fix idH Y) f a).dtor =
      ⟨(Str.Colean.Poly.toL idH a.dtor).1, fun q => f ((Str.Colean.Poly.toL idH a.dtor).2.1 q),
        fun i => (Str.Colean.Poly.fix idH X).map (Str.Colean.Poly.fix idH Y) f
          ((Str.Colean.Poly.toL idH a.dtor).2.2 i)⟩ :=
  (Str.Colean.Poly.fix idH X).d_map (Str.Colean.Poly.fix idH Y) f a

end

/-! ### A failed generation is a warning, and the type is untouched -/

section Failing

-- A name the step needs is taken.
def Bad.Colean.Poly.fix : Nat := 0

/--
warning: `Bad` cannot be nested through: no `Codata.PolyIso` instance was generated. The type itself is not affected.
generating the fixpoint `DeriveTest.Bad.Colean.Poly.fix` failed, an error of the generator (`set_option codata.deriveDetails true` shows it)
-/
#guard_msgs in
datatype Bad (α : Type)
  | nil
  | cons (a : α) (t : Bad α)

-- The type is complete, and nothing of the failed step is left.
noncomputable example : Bad Nat := .cons 0 .nil
#check @Bad.rec

run_cmd do
  if (← Lean.getEnv).contains `DeriveTest.Bad.Colean.Poly.S then
    Lean.logError "the failed step was not rolled back"

end Failing

end DeriveTest
