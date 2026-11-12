import Colean.MutualCmd

/-! # Test: `mixed_mutual` with several runs

Three runs `Proc ⊃ Menu ⊃ Trace`: a process offers a finite menu and a trace, the entries of a
menu are a process and a trace, and a trace ticks forever through menus. The innermost run is
declared open in the menus (`Trace.Open α X`), the menus open in the processes and nesting
through `Trace.Open α (Menu.Open α X)`, the processes closed, nesting through `Menu.Open α (Proc α)`
and, two runs inside, through the composite `Trace.Open α (Menu.Open α (Proc α))`. Then
`Menu α := Menu.Open α (Proc α)` and `Trace α := Trace.Open α (Menu α)`. -/

universe u v

namespace RunsTest

open Codata

noncomputable section

mixed_mutual
codata Proc (α : Type u)
  | step (a : α) (menu : Menu α) (t : Trace α)
data Menu (α : Type u)
  | nil
  | cons (p : Proc α) (t : Trace α) (rest : Menu α)
codata Trace (α : Type u)
  | tick (m : Menu α) (next : Trace α)
end

/-- info: @Proc.step : {α : Type u_1} → α → Menu α → Trace α → Proc α -/
#guard_msgs in #check @Proc.step
/-- info: @Menu.cons : {α : Type u_1} → Proc α → Trace α → Menu α → Menu α -/
#guard_msgs in #check @Menu.cons
/-- info: @Trace.tick : {α : Type u_1} → Menu α → Trace α → Trace α -/
#guard_msgs in #check @Trace.tick
/--
info: @Menu.rec : {α : Type u_2} →
  {motive : Menu α → Sort u_1} →
    motive Menu.nil →
      ((p : Proc α) →
          (t : Trace α) →
            (rest : Menu α) → ((t_1 : Menu α) → t_1 ∈ t → motive t_1) → motive rest → motive (Menu.cons p t rest)) →
        (t : Menu α) → motive t
-/
#guard_msgs in #check @Menu.rec
/--
info: @Trace.corec : {α : Type u_1} → {S : Type u_2} → (S → Trace.F α S) → S → Trace α
-/
#guard_msgs in #check @Trace.corec
/--
info: @Trace.F.tick : {α : Type u_1} → {X : Type u_2} → Menu α → X → Trace.F α X
-/
#guard_msgs in #check @Trace.F.tick

-- The processes in a menu, directly or through its traces.
/--
info: @Menu.mem_cons : ∀ {α : Type u_1} (p : Proc α) (t : Trace α) (rest : Menu α) (x : Proc α),
  x ∈ Menu.cons p t rest ↔ x = p ∨ (∃ t₀, t₀ ∈ t ∧ x ∈ t₀) ∨ x ∈ rest
-/
#guard_msgs in #check @Menu.mem_cons

/-- A trace that ticks through the same menu forever. -/
def Trace.idle {α : Type u} (m : Menu α) : Trace α :=
  Trace.corec (S := Unit) (fun _ => .tick m ()) ()

theorem Trace.idle_eq {α : Type u} (m : Menu α) : Trace.idle m = .tick m (.idle m) := by
  conv_lhs => rw [← Trace.ctor_dtor (Trace.idle m), Trace.idle, Trace.dtor_corec]
  simp [Trace.idle]

/-- The open traces at any type of menus: what the processes' corecursion builds. -/
def Trace.idle' {α : Type u} {X : Type v} (m : X) : Trace.Open α X :=
  Trace.Open.corec (S := Unit) (fun _ => .tick m ()) ()

/-- The process whose menu offers itself and an idle trace, forever. -/
def Proc.loop {α : Type u} (a : α) : Proc α :=
  Proc.corec (S := Unit)
    (fun _ => .step a (.cons () (Trace.idle' .nil) .nil) (Trace.idle' .nil)) ()

/-- The processes of a menu, by its recursor: the trace of each entry is not looked into. -/
def Menu.procs {α : Type u} (m : Menu α) : List (Proc α) :=
  Menu.rec (motive := fun _ => List (Proc α)) [] (fun p _ _ _ l => p :: l) m

example {α : Type u} (p : Proc α) (t : Trace α) : (Menu.cons p t .nil).procs = [p] := by
  simp [Menu.procs]

-- A reference two runs inside, from the outermost run: through the composite of the open types.
mixed_mutual
codata Outer (α : Type u)
  | mk (m : Mid α) (i : Inner α)
data Mid (α : Type u)
  | nil
  | cons (o : Outer α) (i : Inner α) (m : Mid α)
codata Inner (α : Type u)
  | mk (a : α) (i : Inner α) (m : Mid α)
end

/-- info: @Outer.mk : {α : Type u_1} → Mid α → Inner α → Outer α -/
#guard_msgs in #check @Outer.mk
/-- info: @Inner.mk : {α : Type u_1} → α → Inner α → Mid α → Inner α -/
#guard_msgs in #check @Inner.mk
/--
info: @Outer.F.mk : {α : Type u_1} → {X : Type u_2} → Mid.Open α X → Inner.Open α (Mid.Open α X) → Outer.F α X
-/
#guard_msgs in #check @Outer.F.mk

end

end RunsTest
