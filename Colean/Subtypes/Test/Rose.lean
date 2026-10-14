import Colean.Subtypes.CodataCmd

/-! # Test: nested occurrences, coinductively

`List`, `Option` and `A × ·` in recursive positions: finitely branching trees of infinite depth,
possibly ending streams, and streams as pairs. -/

universe u

namespace CodataTest

noncomputable section

codata Rose (α : Type u)
  | node (a : α) (children : List (Rose α))

#check @Rose.node
#check @Rose.F.node
#check @Rose.Shape.node
#check @Rose.B.node_children
#check @Rose.F.map_node
#check @Rose.F.Rel.node
#check @Rose.dtor
#check @Rose.casesOn

/-- The tree with label `a` and `n` copies of itself as children. -/
def Rose.rep {α : Type u} (a : α) (n : Nat) : Rose α :=
  Rose.corec (S := Unit) (fun _ => .node a (List.ofFn fun _ : Fin n => ())) ()

@[simp] theorem Rose.dtor_rep {α : Type u} (a : α) (n : Nat) :
    (Rose.rep a n).dtor = .node a (List.ofFn fun _ : Fin n => Rose.rep a n) := by
  simp [Rose.rep, Rose.dtor_corec]

/-- A coalgebra with a counter that is never looked at. -/
def natCoalg {α : Type u} (a : α) (n : Nat) (k : Nat) : Rose.F α Nat :=
  .node a (List.ofFn fun _ : Fin n => k + 1)

/-- Bisimulation with a nested field: `Occ.rel_intro` relates the lists positionwise. -/
example {α : Type u} (a : α) (n k : Nat) : Rose.rep a n = Rose.corec (natCoalg a n) k := by
  refine Rose.bisim (fun x y => x = Rose.rep a n ∧ ∃ k, y = Rose.corec (natCoalg a n) k) ?_
    ⟨rfl, k, rfl⟩
  rintro _ _ ⟨rfl, k, rfl⟩
  simp only [Rose.rep, Rose.dtor_corec, natCoalg, Rose.F.map_node, Codata.Occ.map_list,
    List.map_ofFn]
  exact .node _ _ _ (Codata.Occ.rel_intro _ _ _ _ _ fun _ => ⟨rfl, _, rfl⟩)

/-- Case analysis: the children of any tree form a list. -/
example {α : Type u} (t : Rose α) : ∃ a cs, t = Rose.node a cs := by
  cases t with
  | node a cs => exact ⟨a, cs, rfl⟩

-- Through a composite: optional children in a list.
codata Rose₂ (α : Type u)
  | node (a : α) (children : List (Option (Rose₂ α)))

#check @Rose₂.node
#check @Rose₂.B.node_children
#check @Rose₂.F.Rel.node

def Rose₂.rep {α : Type u} (a : α) : Rose₂ α :=
  Rose₂.corec (S := Unit) (fun _ => .node a [some (), none]) ()

theorem Rose₂.dtor_rep {α : Type u} (a : α) :
    (Rose₂.rep a).dtor = .node a [some (Rose₂.rep a), none] := by
  rw [Rose₂.rep, Rose₂.dtor_corec]
  rfl

-- Possibly ending streams: `Option` in a recursive position.
codata Stream? (α : Type u)
  | cons (a : α) (tail : Option (Stream? α))

#check @Stream?.cons
#check @Stream?.B.cons_tail

def Stream?.const {α : Type u} (a : α) : Stream? α :=
  Stream?.corec (S := Unit) (fun _ => .cons a (some ())) ()

@[simp] theorem Stream?.dtor_const {α : Type u} (a : α) :
    (Stream?.const a).dtor = .cons a (some (Stream?.const a)) := by
  simp [Stream?.const, Stream?.dtor_corec]

-- Streams as pairs: `A × ·` in a recursive position.
codata Str' (α : Type u)
  | mk (p : α × Str' α)

def Str'.const {α : Type u} (a : α) : Str' α := Str'.corec (S := Unit) (fun _ => .mk (a, ())) ()

@[simp] theorem Str'.dtor_const {α : Type u} (a : α) :
    (Str'.const a).dtor = .mk (a, Str'.const a) := by
  simp [Str'.const, Str'.dtor_corec]

end

end CodataTest
