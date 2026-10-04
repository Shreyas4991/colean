import Colean.Subtypes.CodataCmd

/-! # Test: a coinductive family over `Int`, walks

`Walk n` is an infinite walk on the integers starting at `n`: each step goes up or down, and the
index tracks the current position. Every `Walk n` is infinite, so nothing here is an inductive
type in disguise. -/

namespace CodataTest

noncomputable section

codata Walk : Int → Type
  | up {n : Int} (w : Walk (n + 1)) : Walk n
  | down {n : Int} (w : Walk (n - 1)) : Walk n

#check @Walk.up
#check @Walk.corec
#check @Walk.casesOn
#check @Walk.F.Rel.up

/-- The walk that always goes up. -/
def Walk.alwaysUp (n : Int) : Walk n :=
  Walk.corec (S := fun _ => Unit) (fun _ _ => .up ()) ()

def Walk.upDown : Walk 0 :=
  .corec (S := fun _ => Bool) (fun _ b => if b then .up false else .down true) true

@[simp] theorem Walk.dtor_alwaysUp (n : Int) :
    (Walk.alwaysUp n).dtor = .up (Walk.alwaysUp (n + 1)) := by
  simp [Walk.alwaysUp, Walk.dtor_corec]

/-- Its unfolding equation. -/
theorem Walk.alwaysUp_eq (n : Int) : Walk.alwaysUp n = Walk.up (Walk.alwaysUp (n + 1)) := by
  rw [← Walk.ctor_dtor (Walk.alwaysUp n), Walk.dtor_alwaysUp, Walk.ctor_up]

/-- The position after `k` steps. -/
def Walk.position {n : Int} (w : Walk n) : Nat → Int
  | 0 => n
  | k + 1 =>
    match w.dtor with
    | .up w => w.position k
    | .down w => w.position k

theorem Walk.position_alwaysUp (n : Int) (k : Nat) : (Walk.alwaysUp n).position k = n + k := by
  induction k generalizing n with
  | zero => simp [Walk.position]
  | succ k ih =>
    simp [Walk.position, ih]
    omega

/-! ### A walk is determined by its steps -/

/-- The steps of a walk, `true` for up. -/
def Walk.steps {n : Int} (w : Walk n) : Nat → Bool
  | 0 =>
    match w.dtor with
    | .up _ => true
    | .down _ => false
  | k + 1 =>
    match w.dtor with
    | .up w => w.steps k
    | .down w => w.steps k

@[simp] theorem Walk.steps_up_zero {n : Int} (w : Walk (n + 1)) : (Walk.up w).steps 0 = true := by
  simp [Walk.steps]

@[simp] theorem Walk.steps_up_succ {n : Int} (w : Walk (n + 1)) (k : Nat) :
    (Walk.up w).steps (k + 1) = w.steps k := by
  simp [Walk.steps]

@[simp] theorem Walk.steps_down_zero {n : Int} (w : Walk (n - 1)) :
    (Walk.down w).steps 0 = false := by
  simp [Walk.steps]

@[simp] theorem Walk.steps_down_succ {n : Int} (w : Walk (n - 1)) (k : Nat) :
    (Walk.down w).steps (k + 1) = w.steps k := by
  simp [Walk.steps]

/-- The walk with the given steps, from any starting point. -/
def Walk.ofSteps (f : Nat → Bool) (n : Int) : Walk n :=
  Walk.corec (S := fun _ => Nat → Bool)
    (fun _ f => if f 0 then .up (fun k => f (k + 1)) else .down (fun k => f (k + 1))) f

theorem Walk.dtor_ofSteps_true (f : Nat → Bool) (n : Int) (h : f 0 = true) :
    (Walk.ofSteps f n).dtor = .up (Walk.ofSteps (fun k => f (k + 1)) (n + 1)) := by
  simp [Walk.ofSteps, Walk.dtor_corec, h]

theorem Walk.dtor_ofSteps_false (f : Nat → Bool) (n : Int) (h : f 0 = false) :
    (Walk.ofSteps f n).dtor = .down (Walk.ofSteps (fun k => f (k + 1)) (n - 1)) := by
  simp [Walk.ofSteps, Walk.dtor_corec, h]

theorem Walk.steps_ofSteps (f : Nat → Bool) (n : Int) : (Walk.ofSteps f n).steps = f := by
  funext k
  induction k generalizing f n with
  | zero =>
    cases h : f 0 with
    | true => simp [Walk.steps, Walk.dtor_ofSteps_true f n h]
    | false => simp [Walk.steps, Walk.dtor_ofSteps_false f n h]
  | succ k ih =>
    cases h : f 0 with
    | true => simp [Walk.steps, Walk.dtor_ofSteps_true f n h, ih]
    | false => simp [Walk.steps, Walk.dtor_ofSteps_false f n h, ih]

/-- The other direction, by bisimulation over the family. -/
theorem Walk.ofSteps_steps {n : Int} (w : Walk n) : Walk.ofSteps w.steps n = w := by
  refine Walk.bisim (fun n x y => x = Walk.ofSteps y.steps n) ?_ rfl
  rintro n x y rfl
  cases y with
  | up y =>
    rw [Walk.dtor_ofSteps_true _ _ (Walk.steps_up_zero y), Walk.dtor_up]
    exact .up _ _ (by simp)
  | down y =>
    rw [Walk.dtor_ofSteps_false _ _ (Walk.steps_down_zero y), Walk.dtor_down]
    exact .down _ _ (by simp)

end

end CodataTest
