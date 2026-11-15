import Colean.MutualCmd

/-! # Test: failures and budgets

A failed command declares nothing, as `inductive`; each step of the pipeline has its own
heartbeat budget, as separate commands have; the derived instances (step 5) fail silently, or
with a warning only under `set_option codata.deriveDetails true`, whatever the exception; and an
error of instance search is reported as it is. -/

namespace FailureTest

/-! ### Heartbeats -/

-- Every step, the derived instances included, fits in the budget of one command.
set_option maxHeartbeats 3000 in
codatatype R (α : Type)
  | mk (a : α) (l : List (R α)) (o : Option (R α)) (f : Nat → R α)

#check @R.Colean.Poly.instPolyIso

-- A timeout in step 5 is silent, and the type stays.
#guard_msgs in
set_option maxHeartbeats 1000 in
codatatype R₀ (α : Type)
  | mk (a : α) (l : List (R₀ α)) (o : Option (R₀ α)) (f : Nat → R₀ α)

-- Under `codata.deriveDetails` it is a warning.
/--
warning: `R₁` cannot be nested through: no `Codata.PolyIso` instance was generated. The type itself is not affected.
(deterministic) timeout
-/
#guard_msgs (substring := true) in
set_option codata.deriveDetails true in
set_option maxHeartbeats 1000 in
codatatype R₁ (α : Type)
  | mk (a : α) (l : List (R₁ α)) (o : Option (R₁ α)) (f : Nat → R₁ α)

#check @R₁.mk_inj

/-- error: Unknown constant `FailureTest.R₁.Colean.Poly.S` -/
#guard_msgs in
#check R₁.Colean.Poly.S

/-! ### A failed command declares nothing -/

-- A timeout in the pipeline.
/-- error: (deterministic) timeout -/
#guard_msgs (substring := true) in
set_option maxHeartbeats 300 in
codatatype R₂ (α : Type)
  | mk (a : α) (l : List (R₂ α)) (o : Option (R₂ α)) (f : Nat → R₂ α)

/-- error: Unknown identifier `R₂` -/
#guard_msgs in
#check R₂

-- A constructor named like a generated declaration: refused before anything is declared.
/--
error: constructor `dtor` clashes with the generated declaration `FailureTest.P.dtor`; rename the constructor
-/
#guard_msgs in
datatype P | dtor (n : Nat) | nil

/-- error: Unknown identifier `P.F` -/
#guard_msgs in
#check P.F

datatype P | mk

-- A block, whose index `Blk.Ix` is declared before the constructors are checked.
/-- error: the result type must be `Q₁` applied to its parameters and indices -/
#guard_msgs in
mutual
datatype Q₁ | a (x : Q₂) : Q₂
datatype Q₂ | c (x : Q₁)
end

/-- error: Unknown identifier `Q₁_Q₂.Ix` -/
#guard_msgs in
#check Q₁_Q₂.Ix

-- A universe fixed by a nested type constructor, but not the model's.
structure MonoBox (X : Type) where
  val : X

instance : Codata.PolyIso MonoBox Unit (fun _ => Unit) where
  equiv := ⟨fun b => ⟨(), fun _ => b.val⟩, fun z => ⟨z.2 ()⟩, fun _ => rfl, fun _ => rfl⟩

instance : Codata.PolyMap MonoBox MonoBox where
  map f b := ⟨f b.val⟩
  equiv_map _ _ := rfl

/--
error: the constructors fix the universe of `FailureTest.U` to `0`, through a type constructor at one universe, but its model lives in `1`
-/
#guard_msgs in
codatatype U | mk (x : Type) (b : MonoBox U)

/-- error: Unknown identifier `U.F` -/
#guard_msgs in
#check U.F

/-! ### Errors of instance search -/

structure LBox (X : Type) where
  val : X

class Deep (n : Nat) : Prop

instance [Deep (n + 1)] : Deep n := ⟨⟩

-- An instance whose search does not terminate. Mathlib's linter for instance assumptions without
-- variables would search for `Deep 0` itself, and time out.
set_option linter.concreteInstances false in
instance [Deep 0] : Codata.PolyIso LBox Unit (fun _ => Unit) where
  equiv := ⟨fun b => ⟨(), fun _ => b.val⟩, fun z => ⟨z.2 ()⟩, fun _ => rfl, fun _ => rfl⟩

-- The timeout is reported, not a missing instance.
/--
error: failed to synthesize
  Codata.PolyIso LBox
-/
#guard_msgs (substring := true) in
set_option synthInstance.maxHeartbeats 200 in
codatatype LS | mk (t : LBox LS)

end FailureTest
