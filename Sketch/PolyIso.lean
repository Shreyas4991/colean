import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum

/-! # Scratch: functors naturally isomorphic to polynomial functors

To nest through a type constructor `F` it is enough to present `F` as a polynomial functor:
shapes `Sh`, positions `Pos`, and an isomorphism of functors `F ≅ Poly Sh Pos`, that is, a
family of bijections `F X ≃ Σ sh : Sh, (Pos sh → X)` that is *natural*: it commutes with `F`'s
own `map` and the polynomial functor's `Poly.map`. The class `PolyIso F Sh Pos` states exactly
this.

Instances: the formers `Id`, constants, `Option`, `Except ε`, `ReaderM ρ`, `StateM σ`, and the
closure under products, sums and composition. Instance search cannot take a lambda such as
`fun X => X × X` apart, so products, sums, composition and constants are named functors
(`FProd`, `FSum`, `FComp`, `FConst`); applied to `X` they are definitionally the expected types
(`FProd Id (FSum Id (Except ε)) X = X × (X ⊕ Except ε X)`, checked by `rfl` below). A command
would produce these names from the syntax of an argument type.
-/

universe u v w s p s' p'

namespace PolyIsoSketch

/-! ### Polynomial functors -/

/-- The polynomial functor with shapes `Sh` and positions `Pos`. -/
abbrev Poly (Sh : Type s) (Pos : Sh → Type p) (X : Type u) : Type (max s p u) :=
  Σ sh : Sh, (Pos sh → X)

/-- Its action on functions: the same shape, the contents mapped. -/
def Poly.map {Sh : Type s} {Pos : Sh → Type p} {X Y : Type u} (f : X → Y)
    (z : Poly Sh Pos X) : Poly Sh Pos Y :=
  ⟨z.1, fun q => f (z.2 q)⟩

theorem Poly.ext_of {Sh : Type s} {Pos : Sh → Type p} {X : Type u} {sh : Sh}
    {c c' : Pos sh → X} (h : ∀ q, c q = c' q) : (⟨sh, c⟩ : Poly Sh Pos X) = ⟨sh, c'⟩ :=
  congrArg (Sigma.mk sh) (funext h)

/-- Equality of layers with the same shape (up to conversion) and equal contents. -/
theorem Poly.ext {Sh : Type s} {Pos : Sh → Type p} {X : Type u} {z w : Poly Sh Pos X}
    (h : z.1 = w.1) (h' : ∀ q, z.2 q = w.2 (cast (congrArg Pos h) q)) : z = w := by
  obtain ⟨sh, c⟩ := z
  obtain ⟨sh', c'⟩ := w
  cases h
  exact Poly.ext_of h'

/-! ### The class -/

/-- `F` is isomorphic, as a functor, to the polynomial functor with shapes `Sh` and positions
`Pos`: bijections `F X ≃ Poly Sh Pos X` for every `X`, natural with respect to `F`'s `map`. -/
class PolyIso (F : Type u → Type v) [Functor F] (Sh : outParam (Type s))
    (Pos : outParam (Sh → Type p)) where
  equiv {X : Type u} : F X ≃ Poly Sh Pos X
  natural {X Y : Type u} (f : X → Y) (x : F X) : equiv (f <$> x) = Poly.map f (equiv x)

/-! ### The formers -/

/-- The identity: one shape, one position. -/
instance instId : PolyIso Id Unit (fun _ => Unit) where
  equiv :=
    { toFun := fun x => ⟨(), fun _ => x⟩
      invFun := fun z => z.2 ()
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  natural _ _ := rfl

/-- The positions of `Option`: none for `none`, one for `some`. -/
def OptPos : Bool → Type
  | false => Empty
  | true => Unit

instance instOption : PolyIso Option Bool OptPos where
  equiv :=
    { toFun := fun
        | none => ⟨false, fun q => nomatch q⟩
        | some x => ⟨true, fun _ => x⟩
      invFun := fun
        | ⟨false, _⟩ => none
        | ⟨true, c⟩ => some (c ())
      left_inv := fun x => by cases x <;> rfl
      right_inv := by
        rintro ⟨_ | _, c⟩
        · exact Poly.ext_of fun q => nomatch q
        · rfl }
  natural f x := by
    cases x
    · exact Poly.ext_of fun q => nomatch q
    · rfl

/-- The positions of `Except ε`: none for an error, one for a value. -/
def ExceptPos {ε : Type u} : Except ε Unit → Type
  | .error _ => Empty
  | .ok _ => Unit

instance instExcept (ε : Type u) : PolyIso (Except ε) (Except ε Unit) ExceptPos where
  equiv :=
    { toFun := fun
        | .error e => ⟨.error e, fun q => nomatch q⟩
        | .ok x => ⟨.ok (), fun _ => x⟩
      invFun := fun
        | ⟨.error e, _⟩ => .error e
        | ⟨.ok _, c⟩ => .ok (c ())
      left_inv := fun x => by cases x <;> rfl
      right_inv := by
        rintro ⟨_ | _, c⟩
        · exact Poly.ext_of fun q => nomatch q
        · rfl }
  natural f x := by
    cases x
    · exact Poly.ext_of fun q => nomatch q
    · rfl

/-- `ReaderM ρ X = ρ → X`: one shape, a position per environment. -/
instance instReaderM (ρ : Type u) : PolyIso (ReaderT ρ Id) Unit (fun _ => ρ) where
  equiv :=
    { toFun := fun r => ⟨(), fun q => r q⟩
      invFun := fun z q => z.2 q
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  natural _ _ := rfl

/-- `StateM σ X = σ → X × σ`: the shape is the state transition, a position per initial
state. -/
instance instStateM (σ : Type u) : PolyIso (StateT σ Id) (σ → σ) (fun _ => σ) where
  equiv :=
    { toFun := fun m => ⟨fun s => (m s).2, fun s => (m s).1⟩
      invFun := fun z s => (z.2 s, z.1 s)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  natural _ _ := rfl

/-! ### Constants, products, sums, composition -/

/-- The constant functor. -/
def FConst (A : Type v) (_X : Type u) : Type v := A

instance (A : Type v) : Functor (FConst A : Type u → Type v) where
  map _ a := a

instance instConst (A : Type v) : PolyIso (FConst A : Type u → Type v) A (fun _ => Empty) where
  equiv :=
    { toFun := fun a => ⟨a, fun q => Empty.elim q⟩
      invFun := fun z => z.1
      left_inv := fun _ => rfl
      right_inv := fun _ => Poly.ext rfl fun q => Empty.elim q }
  natural _ _ := Poly.ext rfl fun q => Empty.elim q

/-- The product of two functors. -/
def FProd (F G : Type u → Type v) (X : Type u) : Type v := F X × G X

instance (F G : Type u → Type v) [Functor F] [Functor G] : Functor (FProd F G) where
  map f (x : _ × _) := (f <$> x.1, f <$> x.2)

/-- The sum of two functors. -/
def FSum (F G : Type u → Type v) (X : Type u) : Type v := F X ⊕ G X

instance (F G : Type u → Type v) [Functor F] [Functor G] : Functor (FSum F G) where
  map f (x : _ ⊕ _) := Sum.map (f <$> ·) (f <$> ·) x

/-- The composite of two functors. -/
def FComp (F : Type v → Type w) (G : Type u → Type v) (X : Type u) : Type w := F (G X)

instance (F : Type v → Type w) (G : Type u → Type v) [Functor F] [Functor G] :
    Functor (FComp F G) where
  map {α β} f x := show F (G β) from (fun y : G α => f <$> y) <$> (show F (G α) from x)

section Closure

variable {X : Type u} {A : Type s} {PA : A → Type p} {B : Type s'} {PB : B → Type p'}

/-- The product of two polynomial functors: pairs of shapes, positions of either side. -/
def polyProd : Poly A PA X × Poly B PB X ≃ Poly (A × B) (fun s => PA s.1 ⊕ PB s.2) X where
  toFun z := ⟨(z.1.1, z.2.1), Sum.elim z.1.2 z.2.2⟩
  invFun z := (⟨z.1.1, fun q => z.2 (.inl q)⟩, ⟨z.1.2, fun q => z.2 (.inr q)⟩)
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun _ => Poly.ext rfl fun q => by cases q <;> rfl

theorem polyProd_map {Y : Type u} (f : X → Y) (a : Poly A PA X) (b : Poly B PB X) :
    polyProd (Poly.map f a, Poly.map f b) = Poly.map f (polyProd (a, b)) :=
  Poly.ext rfl fun q => by cases q <;> rfl

/-- The sum of two polynomial functors: shapes of either side, with their positions (in one
universe, as `Sum.elim` requires). -/
def polySum {PB : B → Type p} : Poly A PA X ⊕ Poly B PB X ≃ Poly (A ⊕ B) (Sum.elim PA PB) X where
  toFun
    | .inl z => ⟨.inl z.1, z.2⟩
    | .inr z => ⟨.inr z.1, z.2⟩
  invFun
    | ⟨.inl a, c⟩ => .inl ⟨a, c⟩
    | ⟨.inr b, c⟩ => .inr ⟨b, c⟩
  left_inv := fun z => by rcases z with ⟨_, _⟩ | ⟨_, _⟩ <;> rfl
  right_inv := fun ⟨s, _⟩ => by cases s <;> rfl

theorem polySum_map {PB : B → Type p} {Y : Type u} (f : X → Y) (z : Poly A PA X ⊕ Poly B PB X) :
    polySum (Sum.map (Poly.map f) (Poly.map f) z) = Poly.map f (polySum z) := by
  rcases z with ⟨_, _⟩ | ⟨_, _⟩ <;> rfl

/-- A polynomial functor applied to isomorphic arguments. -/
def polyCongr {Y : Type v} {Z : Type w} (e : Y ≃ Z) : Poly A PA Y ≃ Poly A PA Z where
  toFun z := ⟨z.1, fun q => e (z.2 q)⟩
  invFun z := ⟨z.1, fun q => e.symm (z.2 q)⟩
  left_inv := fun ⟨_, _⟩ => Poly.ext_of fun _ => e.symm_apply_apply _
  right_inv := fun ⟨_, _⟩ => Poly.ext_of fun _ => e.apply_symm_apply _

/-- The composite of two polynomial functors: an outer shape with an inner shape at each of its
positions; a position is an outer position with an inner position there. -/
def polyComp :
    Poly A PA (Poly B PB X) ≃ Poly (Σ a, PA a → B) (fun z => Σ q, PB (z.2 q)) X where
  toFun z := ⟨⟨z.1, fun q => (z.2 q).1⟩, fun r => (z.2 r.1).2 r.2⟩
  invFun z := ⟨z.1.1, fun q => ⟨z.1.2 q, fun r => z.2 ⟨q, r⟩⟩⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

end Closure

instance instProd (F G : Type u → Type v) [Functor F] [Functor G] {ShF : Type s}
    {PosF : ShF → Type p} {ShG : Type s'} {PosG : ShG → Type p'} [hF : PolyIso F ShF PosF]
    [hG : PolyIso G ShG PosG] :
    PolyIso (FProd F G) (ShF × ShG) (fun s => PosF s.1 ⊕ PosG s.2) where
  equiv := (Equiv.prodCongr hF.equiv hG.equiv).trans polyProd
  natural f x := by
    change polyProd (hF.equiv (f <$> x.1), hG.equiv (f <$> x.2)) = _
    rw [hF.natural, hG.natural, polyProd_map]
    rfl

instance instSum (F G : Type u → Type v) [Functor F] [Functor G] {ShF : Type s}
    {PosF : ShF → Type p} {ShG : Type s'} {PosG : ShG → Type p} [hF : PolyIso F ShF PosF]
    [hG : PolyIso G ShG PosG] :
    PolyIso (FSum F G) (ShF ⊕ ShG) (Sum.elim PosF PosG) where
  equiv := (Equiv.sumCongr hF.equiv hG.equiv).trans polySum
  natural f x := by
    rcases x with x | x
    · change polySum (.inl (hF.equiv (f <$> x))) = Poly.map f (polySum (.inl (hF.equiv x)))
      rw [hF.natural]
      exact polySum_map f (.inl _)
    · change polySum (.inr (hG.equiv (f <$> x))) = Poly.map f (polySum (.inr (hG.equiv x)))
      rw [hG.natural]
      exact polySum_map f (.inr _)

/-- Naturality of the composite, stated on `F (G X)`. -/
theorem comp_natural {F : Type v → Type w} {G : Type u → Type v} [Functor F] [Functor G]
    {ShF : Type s} {PosF : ShF → Type p} {ShG : Type s'} {PosG : ShG → Type p'}
    [hF : PolyIso F ShF PosF] [hG : PolyIso G ShG PosG] {X Y : Type u} (f : X → Y)
    (x : F (G X)) :
    polyComp (polyCongr hG.equiv (hF.equiv ((fun y => f <$> y) <$> x))) =
      Poly.map f (polyComp (polyCongr hG.equiv (hF.equiv x))) := by
    rw [hF.natural]
    generalize hF.equiv x = z
    obtain ⟨sh, c⟩ := z
    change polyComp ⟨sh, fun q => hG.equiv (f <$> c q)⟩ = _
    simp only [hG.natural]
    rfl

instance instComp (F : Type v → Type w) (G : Type u → Type v) [Functor F] [Functor G]
    {ShF : Type s} {PosF : ShF → Type p} {ShG : Type s'} {PosG : ShG → Type p'}
    [hF : PolyIso F ShF PosF] [hG : PolyIso G ShG PosG] :
    PolyIso (FComp F G) (Σ a, PosF a → ShG) (fun z => Σ q, PosG (z.2 q)) where
  equiv := (hF.equiv.trans (polyCongr hG.equiv)).trans polyComp
  natural f x := comp_natural f (show F (G _) from x)

/-! ### Checks -/

-- The formers.
#synth PolyIso Id _ _
#synth PolyIso Option _ _
#synth PolyIso (Except String) _ _
#synth PolyIso (ReaderM Nat) _ _
#synth PolyIso (StateM Nat) _ _
#synth PolyIso (FConst Nat : Type → Type) _ _

-- `X × X`
#synth PolyIso (FProd Id Id) _ _
-- `X × (X ⊕ Except String X)`
#synth PolyIso (FProd Id (FSum Id (Except String))) _ _
-- `Option (X × X)`
#synth PolyIso (FComp Option (FProd Id Id)) _ _
-- `StateM Nat (X ⊕ Bool)`
#synth PolyIso (FComp (StateM Nat) (FSum Id (FConst Bool))) _ _
-- `ReaderM Nat (Except String (Option X))`
#synth PolyIso (FComp (ReaderM Nat) (FComp (Except String) Option)) _ _
-- `Option X × StateM Nat (X × X)`
#synth PolyIso (FProd Option (FComp (StateM Nat) (FProd Id Id))) _ _

-- The named functors are the expected types.
example (X : Type) : FProd Id (FSum Id (Except String)) X = (X × (X ⊕ Except String X)) := rfl
example (X : Type) : FComp Option (FProd Id Id) X = Option (X × X) := rfl
example (X : Type) : FComp (StateM Nat) (FSum Id (FConst Bool)) X = StateM Nat (X ⊕ Bool) := rfl

-- The computed shapes and positions: for `X × (X ⊕ Except String X)` a shape is a choice of
-- side and, on the right, an error or not; the positions are the left hole and those of the
-- chosen right side.
example : PolyIso (FProd Id (FSum Id (Except String)))
    (Unit × (Unit ⊕ Except String Unit))
    (fun s => Unit ⊕ Sum.elim (fun _ => Unit) ExceptPos s.2) := inferInstance

end PolyIsoSketch
