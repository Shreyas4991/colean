import Colean.MutualCmd

/-! # Test: the two readings of a cyclic mixed system

Directories and entries: a directory is a finite list of entries; an entry has a name, its
contents (a directory) and its next version, forever. Each type mentions the other and itself,
so the system is cyclic and its two nested readings are different types:

* codata outer, the entries written first: `Dir X = List X` and `Entry = ν E. α × Dir E × E`.
  The nesting of directories may be infinite: an entry may contain itself (`Entry.loop`).
* data outer, the directories written first: `EntryB X = ν E. α × X × E`, a version chain, and
  `DirB = μ D. List (EntryB D)`. The nesting of directories is well-founded (`DirB.acc`); only
  the version chains are infinite.

The same two declarations in the two orders of a `mixed_mutual` block. -/

universe u

namespace OrderTest

noncomputable section

/-! ### Codata outer -/

mixed_mutual
codata Entry (α : Type u)
  | mk (name : α) (contents : Dir α) (next : Entry α)
data Dir (α : Type u)
  | nil
  | cons (e : Entry α) (d : Dir α)
end

#check @Dir.cons
#check @Entry.mk

/-- An entry whose only content is itself, in every version: an infinite nesting. -/
def Entry.loop {α : Type u} (a : α) : Entry α :=
  Entry.corec (S := Unit) (fun _ => .mk a (Dir.cons () Dir.nil) ()) ()

theorem Entry.dtor_loop {α : Type u} (a : α) :
    (Entry.loop a).dtor =
      .mk a (Codata.Occ.map (Dir.occ α) (Dir.occ α) (fun _ => Entry.loop a) (Dir.cons () Dir.nil))
        (Entry.loop a) := by
  rw [Entry.loop, Entry.dtor_corec]
  rfl

/-! ### Data outer -/

mixed_mutual
data DirB (α : Type u)
  | nil
  | cons (e : EntryB α) (d : DirB α)
codata EntryB (α : Type u)
  | mk (name : α) (contents : DirB α) (next : EntryB α)
end

-- Version chains with contents `X`: coinductive, with an occurrence structure in `X`;
-- directories nest through it.
#check @EntryB.mk
#check @DirB.cons
#check @EntryB.occ

-- The induction hypothesis holds at every position of the entry: the contents of every version.
#check @DirB.rec

/-- `d'` is the contents of some version of some entry of `d` (a position of the entry's
structure). -/
inductive DirB.Below {α : Type u} : DirB α → DirB α → Prop
  | head (e : EntryB α (DirB α)) (d : DirB α) (q : EntryB.Pos α (Codata.Occ.toC (EntryB.occ α) e).1) :
      DirB.Below ((Codata.Occ.toC (EntryB.occ α) e).2 q) (DirB.cons e d)
  | tail (e : EntryB α (DirB α)) (d d' : DirB α) : DirB.Below d' d → DirB.Below d' (DirB.cons e d)

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
    | head e' d'' q =>
      obtain ⟨rfl, rfl⟩ := (DirB.cons_inj _ _ _ _).mp hc
      exact ih_e q
    | tail e' d'' _ h' =>
      obtain ⟨rfl, rfl⟩ := (DirB.cons_inj _ _ _ _).mp hc
      exact ih_d.inv h'

end

end OrderTest
