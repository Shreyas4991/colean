import Colean.MutualCmd

/-! # Test: `mixed_mutual` with several runs, and the rejected forms

Three runs `Proc ⊃ Menu ⊃ Trace`: a process offers a finite menu and a trace, the entries of
a menu are a process and a trace, and a trace ticks forever through menus. The innermost run
`Trace` is declared with the menus as a parameter (`Trace α X`), `Menu` with the processes as
a parameter and nesting through `Trace α (Menu α X)`, and `Proc` closed, nesting through
`Menu α (Proc α)` and, two runs inside, through the composite `Trace α (Menu α (Proc α))`. -/

universe u v

namespace RunsTest

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

#check @Proc.step
#check @Menu.cons
#check @Trace.tick
#check @Proc.F.Rel.step
#check @Menu.rec
#check @Menu.occ
#check @Trace.occ

/-- A trace that ticks through the same menu forever. -/
def Trace.idle {α : Type u} {X : Type v} (m : X) : Trace α X :=
  Trace.corec (S := Unit) (fun _ => .tick m ()) ()

theorem Trace.dtor_idle {α : Type u} {X : Type v} (m : X) :
    (Trace.idle (α := α) m).dtor = .tick m (Trace.idle m) := by
  rw [Trace.idle, Trace.dtor_corec]
  rfl

/-- The process whose menu offers itself and an idle trace, forever. -/
def Proc.loop {α : Type u} (a : α) : Proc α :=
  Proc.corec (S := Unit)
    (fun _ => .step a (Menu.cons () (Trace.idle Menu.nil) Menu.nil) (Trace.idle Menu.nil)) ()

theorem Proc.dtor_loop {α : Type u} (a : α) :
    (Proc.loop a).dtor = .step a
      (Codata.Occ.map (Menu.occ α) (Menu.occ α) (fun _ => Proc.loop a)
        (Menu.cons () (Trace.idle Menu.nil) Menu.nil))
      (Codata.Occ.map (Codata.Occ.comp (Trace.occ α) (Menu.occ α))
        (Codata.Occ.comp (Trace.occ α) (Menu.occ α))
        (fun _ => Proc.loop a) (Trace.idle (X := Menu α Unit) Menu.nil)) := by
  rw [Proc.loop, Proc.dtor_corec]
  rfl

-- A reference two runs inside, from the outermost run: through the composite of the two
-- declared structures.
mixed_mutual
codata Outer (α : Type u)
  | mk (m : Mid α) (i : Inner α)
data Mid (α : Type u)
  | nil
  | cons (o : Outer α) (i : Inner α) (m : Mid α)
codata Inner (α : Type u)
  | mk (a : α) (i : Inner α) (m : Mid α)
end

#check @Outer.mk
#check @Outer.B.mk_i
#check @Outer.F.Rel.mk

/-! ### The rejected forms -/

/--
error: a `mutual` block may not mix `data` and `codata` declarations: the block is a nested fixpoint and the nesting order is a choice; use `mixed_mutual … end`, which nests the declarations in the order written, the first outermost
-/
#guard_msgs in
mutual
data A (α : Type u)
  | nil
  | cons (b : B α) (a : A α)
codata B (α : Type u)
  | mk (a : A α)
end

/--
error: in a `mixed_mutual` block, a declaration may mention, among the runs outside its own, only the adjacent one (`C'` mentions `A'`, two or more runs outside): a reference to a run further outside needs an occurrence structure in several parameters, which is not supported yet
-/
#guard_msgs in
mixed_mutual
codata A' (α : Type u)
  | mk (b : B' α)
data B' (α : Type u)
  | nil
  | cons (c : C' α) (b : B' α)
codata C' (α : Type u)
  | mk (a : A' α) (c : C' α)
end

/--
warning: all declarations of this `mixed_mutual` block are `codata`; use `mutual`
-/
#guard_msgs in
mixed_mutual
codata E (α : Type u)
  | mk (a : α) (f : F α)
codata F (α : Type u)
  | mk (e : E α)
end

#check @E.mk

end

end RunsTest
