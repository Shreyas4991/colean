import Colean.MutualCmd

/-! # Test: failures and budgets

A failed command declares nothing, as `inductive`; each step of the pipeline has its own
heartbeat budget, as separate commands have; the derived instances (step 5) fail with a
warning only, whatever the exception; and an error of instance search is reported as it is. -/

namespace FailureTest

/-! ### Heartbeats -/

-- Every step, the derived instances included, fits in the budget of one command.
set_option maxHeartbeats 3000 in
codata R (α : Type)
  | mk (a : α) (l : List (R α)) (o : Option (R α)) (f : Nat → R α)

#check @R.Poly.instPolyIso

-- A timeout in step 5 is a warning, and the type stays.
/--
warning: `R₁` cannot be nested through: no `Codata.PolyIso` instance was generated. The type itself is not affected.
(deterministic) timeout
-/
#guard_msgs (substring := true) in
set_option maxHeartbeats 1000 in
codata R₁ (α : Type)
  | mk (a : α) (l : List (R₁ α)) (o : Option (R₁ α)) (f : Nat → R₁ α)

#check @R₁.mk_inj

/-- error: Unknown constant `FailureTest.R₁.Poly.S` -/
#guard_msgs in
#check R₁.Poly.S

/-! ### A failed command declares nothing -/

-- A timeout in the pipeline.
/-- error: (deterministic) timeout -/
#guard_msgs (substring := true) in
set_option maxHeartbeats 300 in
codata R₂ (α : Type)
  | mk (a : α) (l : List (R₂ α)) (o : Option (R₂ α)) (f : Nat → R₂ α)

/-- error: Unknown identifier `R₂` -/
#guard_msgs in
#check R₂

-- A constructor named like a generated declaration.
/-- error: (kernel) constant has already been declared 'FailureTest.P.dtor' -/
#guard_msgs in
data P | dtor (n : Nat) | nil

/-- error: Unknown identifier `P.F` -/
#guard_msgs in
#check P.F

data P | mk

-- A block, whose index `Blk.Ix` is declared before the constructors are checked.
/-- error: the result type must be `Q₁` applied to its parameters and indices -/
#guard_msgs in
mutual
data Q₁ | a (x : Q₂) : Q₂
data Q₂ | c (x : Q₁)
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
codata U | mk (x : Type) (b : MonoBox U)

/-- error: Unknown identifier `U.F` -/
#guard_msgs in
#check U.F

/-! ### Errors of instance search -/

structure LBox (X : Type) where
  val : X

class Deep (n : Nat) : Prop

instance [Deep (n + 1)] : Deep n := ⟨⟩

-- An instance whose search does not terminate.
instance [Deep 0] : Codata.PolyIso LBox Unit (fun _ => Unit) where
  equiv := ⟨fun b => ⟨(), fun _ => b.val⟩, fun z => ⟨z.2 ()⟩, fun _ => rfl, fun _ => rfl⟩

-- The timeout is reported, not a missing instance.
/--
error: failed to synthesize
  Codata.PolyIso LBox
-/
#guard_msgs (substring := true) in
set_option synthInstance.maxHeartbeats 200 in
codata LS | mk (t : LBox LS)

end FailureTest
