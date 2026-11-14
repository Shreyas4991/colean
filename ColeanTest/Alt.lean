import Colean.CodataCmd

/-! # Test: a coinductive family, alternating streams

`Alt α β b` is an infinite stream whose elements alternate between `α` and `β`, the index
saying which comes next. -/

universe u v

namespace CodataTest

noncomputable section

codata Alt (α : Type u) (β : Type v) : Bool → Type (max u v)
  | left (a : α) (s : Alt α β false) : Alt α β true
  | right (b : β) (s : Alt α β true) : Alt α β false

#check @Alt.left
#check @Alt.corec
#check @Alt.casesOn
#check @Alt.left_inj

/-- The stream `a b a b …`, from either side. -/
def Alt.const {α : Type u} {β : Type v} (a : α) (b : β) (i : Bool) : Alt α β i :=
  Alt.corec (S := fun _ => Unit) (fun i _ => match i with
    | true => .left a ()
    | false => .right b ()) ()

@[simp] theorem Alt.dtor_const_true {α : Type u} {β : Type v} (a : α) (b : β) :
    (Alt.const a b true).dtor = .left a (Alt.const a b false) := by
  simp [Alt.const, Alt.dtor_corec]

@[simp] theorem Alt.dtor_const_false {α : Type u} {β : Type v} (a : α) (b : β) :
    (Alt.const a b false).dtor = .right b (Alt.const a b true) := by
  simp [Alt.const, Alt.dtor_corec]

/-- Mapping both sorts. -/
def Alt.map {α : Type u} {β : Type v} {α' : Type u} {β' : Type v} (f : α → α') (g : β → β')
    {i : Bool} (s : Alt α β i) : Alt α' β' i :=
  Alt.corec (S := Alt α β) (fun _ t => match t.dtor with
    | .left a t => .left (f a) t
    | .right b t => .right (g b) t) s

@[simp] theorem Alt.dtor_map_left {α : Type u} {β : Type v} {α' : Type u} {β' : Type v}
    (f : α → α') (g : β → β') (a : α) (s : Alt α β false) :
    (Alt.map f g (Alt.left a s)).dtor = .left (f a) (Alt.map f g s) := by
  simp [Alt.map, Alt.dtor_corec]

@[simp] theorem Alt.dtor_map_right {α : Type u} {β : Type v} {α' : Type u} {β' : Type v}
    (f : α → α') (g : β → β') (b : β) (s : Alt α β true) :
    (Alt.map f g (Alt.right b s)).dtor = .right (g b) (Alt.map f g s) := by
  simp [Alt.map, Alt.dtor_corec]

/-- `map id id` is the identity, by bisimulation over the family and case analysis. -/
example {α : Type u} {β : Type v} {i : Bool} (s : Alt α β i) : Alt.map id id s = s := by
  refine Alt.bisim (fun _ x y => x = Alt.map id id y) ?_ rfl
  rintro i x y rfl
  cases y with
  | left a t => simp
  | right b t => simp

/-- The head of a stream at index `true`, by case analysis with a motive over the index. -/
def Alt.headLeft {α : Type u} {β : Type v} (s : Alt α β true) : α :=
  Alt.casesOn (motive := fun j _ => j = true → α) s (fun a _ _ => a) (fun _ _ h => nomatch h) rfl

@[simp] theorem Alt.headLeft_left {α : Type u} {β : Type v} (a : α) (s : Alt α β false) :
    (Alt.left a s).headLeft = a := by
  simp [Alt.headLeft]

example {α : Type u} {β : Type v} (a : α) (b : β) : (Alt.const a b true).headLeft = a := by
  rw [← Alt.ctor_dtor (Alt.const a b true), Alt.dtor_const_true, Alt.ctor_left, Alt.headLeft_left]

end

end CodataTest
