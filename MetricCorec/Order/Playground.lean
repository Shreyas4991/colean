import MetricCorec.Order.Completion

namespace Hidden

-- define inductive type
inductive List (α : Type)
  | nil
  | cons (hd : α) (tl : List α)

namespace List

-- instance

-- def Nondet (α : Type) := Lean.Order.Completion (List α)



namespace Nondet

-- def

end Nondet

end List

end Hidden
