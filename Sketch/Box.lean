import Mathlib.Logic.Equiv.Defs

/-! # Scrat                                                                                                                                                                                                                                                                                                                                                                                                                                                       ch: the lifting `□` of a motive to layers, for any functor

`F` is a functor on families over `I`, given by its action on maps; the laws are not needed.
`□ P y` is the type of layers over the pairs `(x, p)` with `p : P x` whose underlying layer is
`y`. The motive may land in any `Sort w`, at one condition: the pairs must form a family `F`
applies to, so the universe of `F` is at least that of the motive; with `F` at
`Type (max u w)` this is built in. `All` is the inhabitation of `□` at a predicate, `Rel` is
`All` of a relation as a predicate on the product. -/

universe w u v

namespace Scratch

section Box

variable {I : Type v} (F : (I → Type (max u w)) → I → Type (max u w))
  (map : ∀ {X Y : I → Type (max u w)}, (∀ j, X j → Y j) → ∀ {i}, F X i → F Y i)

/-- The lifting of a motive `P : ∀ i, X i → Sort w` to the layers of `X`. -/
def Box {X : I → Type (max u w)} (P : ∀ i, X i → Sort w) {i : I} (y : F X i) :
    Type (max u w) :=
  { z : F (fun i => (x : X i) ×' P i x) i // map (fun _ p => p.1) z = y }

end Box

section Prop'

variable {I : Type v} (F : (I → Type u) → I → Type u)
  (map : ∀ {X Y : I → Type u}, (∀ j, X j → Y j) → ∀ {i}, F X i → F Y i)

/-- The lifted predicate: `□ P y` is inhabited (`w = 0`, so `F` is at `Type u`). -/
def All {X : I → Type u} (P : ∀ i, X i → Prop) {i : I} (y : F X i) : Prop :=
  Nonempty (Box F map P y)

/-- The lifted relation: `All` of the relation as a predicate on the product, at a layer whose
two projections are the given layers. -/
def Rel {X Y : I → Type u} (R : ∀ i, X i → Y i → Prop) {i : I} (a : F X i) (b : F Y i) :
    Prop :=
  ∃ z : F (fun i => X i × Y i) i, All F map (fun i p => R i p.1 p.2) z ∧
    map (fun _ => Prod.fst) z = a ∧ map (fun _ => Prod.snd) z = b

end Prop'

end Scratch

#check @Scratch.Box
#check @Scratch.All
#check @Scratch.Rel
