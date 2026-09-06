
namespace hidden

/-
Plan for implementing `coinductive`:

1. Parse it as inductive + one extra constructor `hold`. For example
  coinductive Stream (α : Type)
  | cons (hd : α) (tl : Stream α)

  becomes
  inductive Stream.Partial (α : Type)
  | hold
  | cons (hd : α) (tl : Stream α)

2. For that inductive (`T.Partial`) we derive a `MetricSpace` instance
  `dist (ctorᵢ ...) (ctorⱼ ...) = 1 for i ≠ j`
  `dist (ctorᵢ ...) (ctorᵢ ...) = 1 if some non-recursive parameters are not equal`
  `dist (ctorᵢ ...) (ctorᵢ ...) = 1/2 * max dist between corresponding recursive parameters, otherwise`

3. We define `T.Completion := metric completion of T.Partial`

4. We prove `T.Completion` is bounded.

5. We prove that the set {↑(x : T.Partial) | x does not contain `hold` constructor} is closed

6. We define `T := this subtype`

TODO


-/

inductive Stream (α : Type)
| hold
| cons (hd : α) (tl : Stream α)




end hidden
