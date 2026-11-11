import Colean.MutualCmd

/-! # Test: the two readings of a cyclic mixed system

Directories and entries: a directory is a finite list of entries; an entry has a name, its
contents (a directory) and its next version, forever. Each type mentions the other and itself,
so the system is cyclic and its two nested readings are different types:

* codata outer, the entries written first: `Dir X = μ D. 1 + X × D` and
  `Entry = ν E. α × Dir E × E`. The nesting of directories may be infinite: an entry may contain
  itself (`Entry.loop`).
* data outer, the directories written first: `EntryB X = ν E. α × X × E`, a version chain, and
  `DirB = μ D. 1 + EntryB D × D`. The nesting of directories is well-founded (`DirB.acc`); only
  the version chains are infinite.

The same two declarations in the two orders of a `mixed_mutual` block. -/

universe u

namespace OrderTest

open Codata

noncomputable section

/-! ### Codata outer -/

mixed_mutual
codata Entry (α : Type u)
  | mk (name : α) (contents : Dir α) (next : Entry α)
data Dir (α : Type u)
  | nil
  | cons (e : Entry α) (d : Dir α)
end

/-- info: @Dir.cons : {α : Type u_1} → Entry α → Dir α → Dir α -/
#guard_msgs in #check @Dir.cons
/-- info: @Entry.mk : {α : Type u_1} → α → Dir α → Entry α → Entry α -/
#guard_msgs in #check @Entry.mk

/-- An entry whose only content is itself, in every version: an infinite nesting. -/
def Entry.loop {α : Type u} (a : α) : Entry α :=
  Entry.corec (S := Unit) (fun _ => .mk a (.cons () .nil) ()) ()

theorem Entry.loop_eq {α : Type u} (a : α) :
    Entry.loop a = .mk a (.cons (.loop a) .nil) (.loop a) := by
  conv_lhs => rw [← Entry.ctor_dtor (Entry.loop a), Entry.loop, Entry.dtor_corec]
  simp [Entry.loop]

/-- The loop is a member of its own contents. -/
example {α : Type u} (a : α) : ∃ d e, Entry.loop a = .mk a d e ∧ Entry.loop a ∈ d :=
  ⟨_, _, Entry.loop_eq a, by simp⟩

/-! ### Data outer -/

mixed_mutual
data DirB (α : Type u)
  | nil
  | cons (e : EntryB α) (d : DirB α)
codata EntryB (α : Type u)
  | mk (name : α) (contents : DirB α) (next : EntryB α)
end

/-- info: @EntryB.mk : {α : Type u_1} → α → DirB α → EntryB α → EntryB α -/
#guard_msgs in #check @EntryB.mk
/-- info: @DirB.cons : {α : Type u_1} → EntryB α → DirB α → DirB α -/
#guard_msgs in #check @DirB.cons

/-! The induction hypothesis holds at every member of the entry: the contents of every version.
-/

/--
info: @DirB.rec : {α : Type u_1} →
  {motive : DirB α → Sort u_2} →
    motive DirB.nil →
      ((e : EntryB α) → (d : DirB α) → ((t : DirB α) → t ∈ e → motive t) → motive d → motive (DirB.cons e d)) →
        (t : DirB α) → motive t
-/
#guard_msgs in #check @DirB.rec
/--
info: @EntryB.mem_mk : ∀ {α : Type u_1} (name : α) (contents : DirB α) (next : EntryB α) (x : DirB α),
  x ∈ EntryB.mk name contents next ↔ x = contents ∨ x ∈ next
-/
#guard_msgs in #check @EntryB.mem_mk

/-- `d'` is the contents of some version of some entry of `d`. -/
inductive DirB.Below {α : Type u} : DirB α → DirB α → Prop
  | head (e : EntryB α) (d d' : DirB α) : d' ∈ e → DirB.Below d' (DirB.cons e d)
  | tail (e : EntryB α) (d d' : DirB α) : DirB.Below d' d → DirB.Below d' (DirB.cons e d)

/-- Every directory is accessible: the nesting of directories is well-founded, although the
entries are infinite objects. The constructors are not those of an inductive type, so the case
analysis on `Below` goes through the generated injectivity and disjointness lemmas. -/
theorem DirB.acc {α : Type u} (d : DirB α) : Acc DirB.Below d := by
  induction d with
  | nil =>
    refine Acc.intro _ fun d' h => ?_
    generalize hn : (DirB.nil : DirB α) = n at h
    cases h <;> simp at hn
  | cons e d ih_e ih_d =>
    refine Acc.intro _ fun d' h => ?_
    generalize hc : DirB.cons e d = c at h
    cases h with
    | head e' d'' _ hm =>
      obtain ⟨rfl, rfl⟩ := (DirB.cons_inj _ _ _ _).mp hc
      exact ih_e _ hm
    | tail e' d'' _ h' =>
      obtain ⟨rfl, rfl⟩ := (DirB.cons_inj _ _ _ _).mp hc
      exact ih_d.inv h'

/-! A fold of the directories through the entries: the step sees an entry of results, an open
entry, whose first version's contents is the result for the contents. -/

/-- The depth of the nesting along the first versions. -/
def DirB.depth {α : Type u} (d : DirB α) : Nat :=
  DirB.fold (S := Nat)
    (fun | .nil => 0 | .cons e n => max n (EntryB.Open.casesOn e fun _ c _ => c + 1)) d

/-- `simp` computes the fold through the codata entries: `EntryB.Open.Poly.map_mk` pushes the
map into the first version. -/
example {α : Type u} (a : α) (e : EntryB α) :
    (DirB.cons (EntryB.mk a (DirB.cons (EntryB.mk a .nil e) .nil) e) .nil).depth = 2 := by
  simp [DirB.depth]

end

end OrderTest
