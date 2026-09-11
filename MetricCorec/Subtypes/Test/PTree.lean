import MetricCorec.Subtypes.CodataCmd

/-! Trees with two type parameters: `mirror` is an involution, by bisimulation and `cases`. -/

universe u v

namespace CodataTest

noncomputable section

codata PTree (α : Type u) (β : Type v)
  | leaf (b : β)
  | node (a : α) (l r : PTree α β)

example {α : Type u} {β : Type v} (a : α) (l r l' r' : PTree α β) :
    PTree.node a l r = PTree.node a l' r' ↔ l = l' ∧ r = r' := by simp

def PTree.mirror {α : Type u} {β : Type v} (t : PTree α β) : PTree α β :=
  PTree.corec (fun t => match t.dtor with
    | .leaf b => .leaf b
    | .node a l r => .node a r l) t

example {α : Type u} {β : Type v} (t : PTree α β) : t.mirror.mirror = t := by
  refine PTree.bisim (fun x y => x = y.mirror.mirror) ?_ rfl
  intro x y hxy
  subst hxy
  cases y with
  | leaf b => simp [PTree.mirror, PTree.dtor_corec]; exact .leaf b
  | node a l r =>
    simp [PTree.mirror, PTree.dtor_corec]
    exact .node a _ _ _ _ rfl rfl

end

end CodataTest
