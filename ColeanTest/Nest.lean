import Colean.MutualCmd

/-! # Test: nesting through a user's functor

The interface of `Colean/PolyIso.lean`: instances of `PolyIso` and `PolyMap` make a type
constructor usable in nested arguments, for `codata`, `data` and mutual blocks. -/

universe u u' v

namespace NestTest

noncomputable section

structure Box (X : Type u) where
  val : X

instance : Codata.PolyIso Box.{u} Unit (fun _ => Unit) where
  equiv := ⟨fun b => ⟨(), fun _ => b.val⟩, fun z => ⟨z.2 ()⟩, fun _ => rfl, fun _ => rfl⟩

instance : Codata.PolyMap Box.{u} Box.{u'} where
  map f b := ⟨f b.val⟩
  equiv_map _ _ := rfl

/-! ### `codata` and `data` -/

codata BStream (α : Type u)
  | cons (a : α) (tail : Box (BStream α))

/-- The state may live in another universe than the type. -/
example : ∀ {α : Type u} {S : Type v}, (S → BStream.F α S) → S → BStream α := BStream.corec

def BStream.const {α : Type u} (a : α) : BStream α :=
  BStream.corec (S := Unit) (fun _ => .cons a ⟨()⟩) ()

/-- The generated map on the nested argument is the intended one. -/
example {X : Type u} {Y : Type u'} (f : X → Y) (b : Box X) :
    Codata.Occ.map (Codata.Occ.ofIso Box) (Codata.Occ.ofIso Box) f b = ⟨f b.val⟩ :=
  Codata.Occ.map_ofIso f b

@[simp] theorem BStream.dtor_const {α : Type u} (a : α) :
    (BStream.const a).dtor = .cons a ⟨BStream.const a⟩ := by
  rw [BStream.const, BStream.dtor_corec]
  simp only [BStream.F.map_cons]
  rw [Codata.Occ.map_ofIso]
  rfl

data BList (α : Type u)
  | nil
  | cons (a : α) (tail : Box (BList α))

def BList.length {α : Type u} (l : BList α) : Nat :=
  BList.fold (S := Nat) (fun | .nil => 0 | .cons _ b => b.val + 1) l

/-! ### Composites and families -/

-- The leaf composes with the built-in forms and with other leaves.
codata BTree
  | node (children : List (Box BTree × Option (Box BTree)))

-- At several indices of a family, through a plain leaf.
codata BVec (α : Type u) : Nat → Type u
  | nil : BVec α 0
  | cons {n : Nat} (a : α) (tail : Box (BVec α n)) : BVec α (n + 1)

mutual
data Even
  | zero
  | succ (o : Box Odd)
data Odd
  | succ (e : Box Even)
end

/-- A functor on families: the values at the two booleans. -/
structure Both (X : Bool → Type u) where
  yes : X true
  no : X false

instance : Codata.IPolyIso Both.{u} Unit (fun _ => Bool) (fun _ b => b) where
  equiv :=
    { toFun := fun t => ⟨(), fun b => match b with | true => t.yes | false => t.no⟩
      invFun := fun z => ⟨z.2 true, z.2 false⟩
      left_inv := fun _ => rfl
      right_inv := fun ⟨_, c⟩ => congrArg (Sigma.mk ()) (funext fun b => by cases b <;> rfl) }

instance : Codata.IPolyMap Both.{u} Both.{u'} where
  map f t := ⟨f _ t.yes, f _ t.no⟩
  equiv_map f t := congrArg (Sigma.mk ()) (funext fun b => by cases b <;> rfl)

codata Alt : Bool → Type
  | mk {b : Bool} (children : Both (fun c => Alt c)) : Alt b

/-! ### Missing instances -/

structure NoIso (X : Type u) where
  val : X

/--
error: no `Codata.PolyIso` instance for `NoIso`; to nest through a type constructor, give it `Codata.PolyIso` and `Codata.PolyMap` instances (`Colean/PolyIso.lean`); products, sums, functions and dependent pairs over constant types need none
-/
#guard_msgs in
codata Bad₁
  | mk (x : NoIso Bad₁)

structure NoMap (X : Type u) where
  val : X

instance : Codata.PolyIso NoMap.{u} Unit (fun _ => Unit) where
  equiv := ⟨fun b => ⟨(), fun _ => b.val⟩, fun z => ⟨z.2 ()⟩, fun _ => rfl, fun _ => rfl⟩

/--
error: no `Codata.PolyMap` instance for `NoMap`: the `Codata.PolyIso` instance needs the intended action on functions, and its naturality
-/
#guard_msgs in
codata Bad₂
  | mk (x : NoMap Bad₂)

end

/-! ### A noncomputable instance, outside a `noncomputable section` -/

data NBox (X : Type u)
  | mk (val : X)

noncomputable def NBox.val {X : Type u} (b : NBox X) : X :=
  NBox.casesOn (motive := fun _ => X) b id

@[simp] theorem NBox.val_mk {X : Type u} (x : X) : (NBox.mk x).val = x := by
  simp [NBox.val]

noncomputable instance : Codata.PolyIso NBox.{u} Unit (fun _ => Unit) where
  equiv :=
    { toFun := fun b => ⟨(), fun _ => b.val⟩
      invFun := fun z => .mk (z.2 ())
      left_inv := fun b => by cases b with | mk x => simp
      right_inv := fun _ => by simp }

noncomputable instance : Codata.PolyMap NBox.{u} NBox.{u'} where
  map f b := .mk (f b.val)
  equiv_map f b := by simp [Equiv.coe_fn_mk, Codata.PolyIso.equiv, Codata.Poly.map]

codata NStream
  | cons (tail : NBox NStream)

#check @NStream.corec

end NestTest
