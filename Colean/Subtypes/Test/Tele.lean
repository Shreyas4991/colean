import Colean.Subtypes.CodataCmd

/-! # Test: recursive arguments under a telescope

A recursive argument may sit under any chain of arrows, dependent or not, whose domains do not
mention the type being defined; its index may depend on the bound variables. -/

namespace CodataTest

noncomputable section

-- A countdown protocol: at `n`, choose any `i < n` and continue at `i`. The continuation's
-- index depends on the answer.
codata Proto : Nat → Type
  | choose {n : Nat} (k : (i : Fin n) → Proto i.val) : Proto n
  | done : Proto 0

#check @Proto.choose
#check @Proto.B.choose_k
#check @Proto.F.Rel.choose

/-- Always choose again; at `0` there is nothing to choose, and `Fin 0` is empty. -/
def Proto.forever (n : Nat) : Proto n :=
  Proto.corec (S := fun _ => Unit) (fun _ _ => .choose fun _ => ()) ()

@[simp] theorem Proto.dtor_forever (n : Nat) :
    (Proto.forever n).dtor = .choose fun i => Proto.forever i.val := by
  simp [Proto.forever, Proto.dtor_corec]

-- A curried continuation, and one whose second domain depends on the first.
codata Table
  | node (a : Nat) (k : Nat → Bool → Table)
  | leaf (f : (n : Nat) → Fin (n + 1) → Table)

#check @Table.node
#check @Table.B.node_k
#check @Table.B.leaf_f

def Table.const (a : Nat) : Table :=
  Table.corec (S := Unit) (fun _ => .node a fun _ _ => ()) ()

theorem Table.dtor_const (a : Nat) : (Table.const a).dtor = .node a fun _ _ => Table.const a := by
  simp [Table.const, Table.dtor_corec]

/-- The unfolding equation, through a two-argument continuation. -/
example (a : Nat) : Table.const a = Table.node a fun _ _ => Table.const a := by
  conv => lhs; rw [← Table.ctor_dtor (Table.const a), Table.dtor_const]
  rfl

end

end CodataTest
