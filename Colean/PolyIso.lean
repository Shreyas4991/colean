import Mathlib.Data.List.OfFn

/-!
# Nesting through a functor

A constructor argument may mention the type being defined under a named type constructor `F`,
as in `children : List (Tree α)`. The `codata` and `data` commands accept this exactly when `F`
is isomorphic, as a functor, to a polynomial functor, which is what the classes of this file say.
They are the interface for users: to nest through your own `F`, give two instances.

```
structure Box (X : Type u) where
  val : X

instance : PolyIso Box.{u} Unit (fun _ => Unit) where
  equiv := ⟨fun b => ⟨(), fun _ => b.val⟩, fun z => ⟨z.2 ()⟩, fun _ => rfl, fun _ => rfl⟩

instance : PolyMap Box.{u} Box.{u'} where
  map f b := ⟨f b.val⟩
  equiv_map _ _ := rfl

codata Stream' (α : Type u)
  | cons (a : α) (tail : Box (Stream' α))
```

* `PolyIso F Sh Pos` presents `F` as the polynomial functor with shapes `Sh` and positions `Pos`:
  a bijection `F X ≃ Σ sh : Sh, (Pos sh → X)` for every `X`.
* `PolyMap F F'` gives the intended action on functions and says that the bijections are natural
  with respect to it. Together the two classes state the isomorphism of functors.

The action is a class of its own, on two instantiations of `F`, because the generated `T.F.map`
crosses universes: the state of `corec` may live in any universe. Lean's `Functor` maps within
one universe, and naturality in each universe separately does not determine the map between
them. With `PolyMap`, the map the command generates on a nested argument is provably the
intended one (`Occ.map_ofIso`).

A nested argument may have several occurrences through products, sums, functions and dependent
pairs, which the command handles itself. Named type constructors take the occurrences in one
argument. `IPolyIso` and `IPolyMap` are the same classes for functors on families
`(J → Type u) → Type v`, where every position says at which index its child lives.

Instances are never generated: a type declared by `codata` or `data` can be nested through once
it is given these instances.
-/

universe u u' v v' s p j

namespace Codata

/-! ### Polynomial functors -/

/-- The polynomial functor with shapes `Sh` and positions `Pos`. -/
abbrev Poly (Sh : Type s) (Pos : Sh → Type p) (X : Type u) : Type (max s p u) :=
  Σ sh : Sh, (Pos sh → X)

/-- Its action on functions: the same shape, the contents mapped. -/
def Poly.map {Sh : Type s} {Pos : Sh → Type p} {X : Type u} {Y : Type u'} (f : X → Y)
    (z : Poly Sh Pos X) : Poly Sh Pos Y :=
  ⟨z.1, fun q => f (z.2 q)⟩

/-- The indexed polynomial functor: positions carry the index of their child. -/
abbrev IPoly {J : Type j} (Sh : Type s) (Pos : Sh → Type p) (pidx : (sh : Sh) → Pos sh → J)
    (X : J → Type u) : Type (max s p u) :=
  Σ sh : Sh, (q : Pos sh) → X (pidx sh q)

/-- Its action on functions. -/
def IPoly.map {J : Type j} {Sh : Type s} {Pos : Sh → Type p} {pidx : (sh : Sh) → Pos sh → J}
    {X : J → Type u} {Y : J → Type u'} (f : ∀ j, X j → Y j) (z : IPoly Sh Pos pidx X) :
    IPoly Sh Pos pidx Y :=
  ⟨z.1, fun q => f _ (z.2 q)⟩

/-! ### The classes -/

/-- `F` is presented as the polynomial functor with shapes `Sh` and positions `Pos`. -/
class PolyIso (F : Type u → Type v) (Sh : outParam (Type s)) (Pos : outParam (Sh → Type p)) where
  equiv {X : Type u} : F X ≃ Poly Sh Pos X

/-- The intended action on functions between two instantiations of `F`, and the naturality of
the presentation: `PolyIso` and `PolyMap` together are an isomorphism of functors. -/
class PolyMap (F : Type u → Type v) (F' : Type u' → Type v') {Sh : Type s} {Pos : Sh → Type p}
    [hF : PolyIso F Sh Pos] [hF' : PolyIso F' Sh Pos] where
  map {X : Type u} {Y : Type u'} : (X → Y) → F X → F' Y
  equiv_map {X : Type u} {Y : Type u'} (f : X → Y) (x : F X) :
    hF'.equiv (map f x) = Poly.map f (hF.equiv x)

/-- `PolyIso` for a functor on families: every position carries the index of its child. -/
class IPolyIso {J : Type j} (G : (J → Type u) → Type v) (Sh : outParam (Type s))
    (Pos : outParam (Sh → Type p)) (pidx : outParam ((sh : Sh) → Pos sh → J)) where
  equiv {X : J → Type u} : G X ≃ IPoly Sh Pos pidx X

/-- `PolyMap` for a functor on families. -/
class IPolyMap {J : Type j} (G : (J → Type u) → Type v) (G' : (J → Type u') → Type v')
    {Sh : Type s} {Pos : Sh → Type p} {pidx : (sh : Sh) → Pos sh → J}
    [hG : IPolyIso G Sh Pos pidx] [hG' : IPolyIso G' Sh Pos pidx] where
  map {X : J → Type u} {Y : J → Type u'} : (∀ j, X j → Y j) → G X → G' Y
  equiv_map {X : J → Type u} {Y : J → Type u'} (f : ∀ j, X j → Y j) (x : G X) :
    hG'.equiv (map f x) = IPoly.map f (hG.equiv x)

/-! ### `List`, `Option`, `Array` -/

/-- Lists: the shape is the length, the positions its indices. -/
instance : PolyIso List.{u} Nat Fin := ⟨List.equivSigmaTuple⟩

instance : PolyMap List.{u} List.{u'} where
  map := List.map
  equiv_map f l := by
    refine List.equivSigmaTuple.symm.injective ?_
    change List.equivSigmaTuple.symm (List.equivSigmaTuple (l.map f)) = List.ofFn (f ∘ l.get)
    rw [Equiv.symm_apply_apply, ← List.map_ofFn, List.ofFn_get]

/-- The positions of `Option`: one when the shape is `true`, none when it is `false`. -/
inductive OptionPos : Bool → Type
  | unit : OptionPos true

/-- Options: the shape says whether there is a value. -/
instance : PolyIso Option.{u} Bool OptionPos where
  equiv := {
    toFun
      | none => ⟨false, fun q => nomatch q⟩
      | some x => ⟨true, fun _ => x⟩
    invFun
      | ⟨false, _⟩ => none
      | ⟨true, f⟩ => some (f .unit)
    left_inv := by
      intro x
      cases x <;> rfl
    right_inv := by
      rintro ⟨_ | _, f⟩
      · exact congrArg (Sigma.mk false) (funext fun q => nomatch q)
      · exact congrArg (Sigma.mk true) (funext fun q => match q with | .unit => rfl) }

instance : PolyMap Option.{u} Option.{u'} where
  map := Option.map
  equiv_map f x := by
    cases x
    · exact congrArg (Sigma.mk false) (funext fun q => nomatch q)
    · rfl

/-- Arrays, through their lists. -/
instance : PolyIso Array.{u} Nat Fin :=
  ⟨(Equiv.mk Array.toList List.toArray (fun _ => by simp) (fun _ => by simp)).trans
    List.equivSigmaTuple⟩

instance : PolyMap Array.{u} Array.{u'} where
  map := Array.map
  equiv_map f a := by
    change List.equivSigmaTuple (a.map f).toList = Poly.map f (List.equivSigmaTuple a.toList)
    rw [Array.toList_map]
    exact PolyMap.equiv_map (F := List) (F' := List) f a.toList

end Codata
