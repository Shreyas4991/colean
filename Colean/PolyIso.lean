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

A presentation says what the members of a value are: those at its positions (`PolyIso.Mem`,
`IPolyIso.Mem` at an index). The recursor of a `data` type states the induction hypothesis of a
nested argument `c : G T` with it, `∀ t, PolyIso.Mem (fun X => G X) t c → motive t`, and the
`simp` lemmas of this file turn membership into the containers' own (`mem_list`, …) or into
components (`mem_prod`, …).

Products, sums, functions and dependent pairs of functors with instances have instances too, so
every argument type with occurrences has one, `fun X => List (X × Nat)` say: they are the
presentations the command uses for these forms (`Model/Occ.lean`), and so the instances the
recursor's hypotheses are stated with. Constants, the identity, `List`, `Option` and `Array`
are the other instances here.

A type declared by `codata` or `data` gets these instances when it can (`Gen/Derive.lean`):
in the arguments that may vary, for the functors `fun X => T (H X)` with `H` itself an instance
(`PolyMap` from that of `H`, as for the forms here), and for a family or a type of a block at
every index, `fun X => T (H X) idx`. With them come
`simp` lemmas on its constructors, for the map on the leaf `Occ.ofIso` of the instance
(`T.Poly.map_c`) and for membership (`T.Poly.mem_c`), so that `simp` computes through them.
-/

universe u u' u'' v v' v'' w w' s s' p p' j k a

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

/-! ### Membership -/

/-- A transport of a value of a dependent function is its value at the other point. -/
theorem ndrec_app {α : Sort u} {β : α → Sort v} (g : ∀ a, β a) {a b : α} (e : a = b) :
    Eq.ndrec (motive := β) (g a) e = g b := by
  subst e
  rfl

namespace PolyIso

section Mem

variable (F : Type u → Type v) {Sh : Type s} {Pos : Sh → Type p} [h : PolyIso F Sh Pos]
  {X : Type u}

/-- `x` is a member of `c`: some position of `c`, in the presentation of `F`, holds `x`. The
functor is explicit, since Lean cannot always infer it from `c`. -/
def Mem (x : X) (c : F X) : Prop :=
  ∃ q, (h.equiv c).2 q = x

variable {F}

theorem mem_iff {x : X} {c : F X} : Mem F x c ↔ ∃ q, (h.equiv c).2 q = x := Iff.rfl

/-- The content of a position is a member. -/
theorem mem_pos (c : F X) (q : Pos (h.equiv c).1) : Mem F ((h.equiv c).2 q) c := ⟨q, rfl⟩

/-- A property of every member is one of the content of every position. -/
theorem forall_mem_iff {P : X → Prop} {c : F X} :
    (∀ x, Mem F x c → P x) ↔ ∀ q, P ((h.equiv c).2 q) :=
  ⟨fun H q => H _ (mem_pos c q), fun H _ ⟨q, e⟩ => e ▸ H q⟩

/-- The members of a mapped value are the images of the members. -/
theorem mem_map {F' : Type u' → Type v'} [h' : PolyIso F' Sh Pos] [m : PolyMap F F'] {Y : Type u'}
    (f : X → Y) (c : F X) (y : Y) :
    Mem F' y (PolyMap.map (self := m) Pos f c) ↔ ∃ x, Mem F x c ∧ f x = y := by
  rw [mem_iff, PolyMap.equiv_map]
  constructor
  · rintro ⟨q, e⟩
    exact ⟨_, mem_pos c q, e⟩
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨q, rfl⟩

/-- A function on the members of `c` from one on the contents of its positions: how a
hypothesis at every position becomes one at every member. -/
noncomputable def memRec {c : F X} {motive : X → Sort w} (ih : ∀ q, motive ((h.equiv c).2 q))
    (x : X) (hx : Mem F x c) : motive x :=
  Eq.ndrec (motive := motive) (ih (Classical.choose hx)) (Classical.choose_spec hx)

/-- At the contents of the positions of a function `g`, `memRec` is `g`. -/
theorem memRec_pos {c : F X} {motive : X → Sort w} (g : ∀ x, motive x) :
    memRec (h := h) (c := c) (fun q => g ((h.equiv c).2 q)) = fun x _ => g x := by
  funext x hx
  exact ndrec_app g (Classical.choose_spec hx)

end Mem

end PolyIso

namespace IPolyIso

section Mem

variable {J : Type j} (G : (J → Type u) → Type v) {Sh : Type s} {Pos : Sh → Type p}
  {pidx : (sh : Sh) → Pos sh → J} [h : IPolyIso G Sh Pos pidx] {X : J → Type u}

/-- `x` is a member of `c` at the index `j`: some position of `c` is at `j` and holds `x`. The
functor is explicit, as for `PolyIso.Mem`. -/
def Mem (j : J) (x : X j) (c : G X) : Prop :=
  ∃ q, (⟨_, (h.equiv c).2 q⟩ : Σ j, X j) = ⟨j, x⟩

variable {G}

theorem mem_iff {j : J} {x : X j} {c : G X} :
    Mem G j x c ↔ ∃ q, (⟨_, (h.equiv c).2 q⟩ : Σ j, X j) = ⟨j, x⟩ := Iff.rfl

/-- The content of a position is a member at its index. -/
theorem mem_pos (c : G X) (q : Pos (h.equiv c).1) : Mem G _ ((h.equiv c).2 q) c := ⟨q, rfl⟩

/-- A property of every member is one of the content of every position. -/
theorem forall_mem_iff {P : ∀ j, X j → Prop} {c : G X} :
    (∀ j x, Mem G j x c → P j x) ↔ ∀ q, P _ ((h.equiv c).2 q) :=
  ⟨fun H q => H _ _ (mem_pos c q), fun H _ _ ⟨q, e⟩ =>
    Eq.ndrec (motive := fun z : Σ j, X j => P z.1 z.2) (H q) e⟩

/-- A function on the members of `c` from one on the contents of its positions. -/
noncomputable def memRec {c : G X} {motive : ∀ j, X j → Sort w}
    (ih : ∀ q, motive _ ((h.equiv c).2 q)) (j : J) (x : X j) (hx : Mem G j x c) : motive j x :=
  Eq.ndrec (motive := fun z : Σ j, X j => motive z.1 z.2) (ih (Classical.choose hx))
    (Classical.choose_spec hx)

/-- At the contents of the positions of a function `g`, `memRec` is `g`. -/
theorem memRec_pos {c : G X} {motive : ∀ j, X j → Sort w} (g : ∀ j x, motive j x) :
    memRec (h := h) (c := c) (fun q => g _ ((h.equiv c).2 q)) = fun j x _ => g j x := by
  funext j x hx
  exact ndrec_app (β := fun z : Σ j, X j => motive z.1 z.2) (fun z => g z.1 z.2)
    (Classical.choose_spec hx)

end Mem

end IPolyIso

open PolyIso (Mem)

/-! A property of the members of a pair, one of them through a container, splits by `simp`:
`∀ t, t ∈ p.1 ∨ t = p.2 → P t` is `(∀ t ∈ p.1, P t) ∧ P p.2`, as `forall_eq_or_imp` does with the
equation first. The lemma is Lean's own; it is a `simp` lemma from here on. -/

attribute [simp] forall_or_eq_imp

/-! ### The identity and constants

What the instances of a functor with several arguments compose with: `Pair Nat X` is `Pair` at
a constant and the identity. A constant is preferred to every other instance that could take
it apart (`List Nat` as a composite). -/

instance : PolyIso (fun X : Type u => X) Unit (fun _ => Unit) :=
  ⟨⟨fun x => ⟨(), fun _ => x⟩, fun z => z.2 (), fun _ => rfl, fun _ => rfl⟩⟩

instance : PolyMap (fun X : Type u => X) (fun X : Type u' => X) where
  map f x := f x
  equiv_map _ _ := rfl

instance (priority := high) (A : Type v) : PolyIso (fun _ : Type u => A) A (fun _ => Empty) :=
  ⟨⟨fun a => ⟨a, fun q => q.elim⟩, fun z => z.1, fun _ => rfl,
    fun z => congrArg (Sigma.mk z.1) (funext fun q => q.elim)⟩⟩

instance (A : Type v) : PolyMap (fun _ : Type u => A) (fun _ : Type u' => A) where
  map _ a := a
  equiv_map _ a := congrArg (Sigma.mk a) (funext fun q => q.elim)

namespace PolyIso

@[simp] theorem mem_id {X : Type u} (x c : X) : Mem (fun X : Type u => X) x c ↔ x = c :=
  ⟨fun ⟨_, e⟩ => e.symm, fun e => ⟨(), e.symm⟩⟩

@[simp] theorem not_mem_const (A : Type v) {X : Type u} (x : X) (c : A) :
    ¬ Mem (fun _ : Type u => A) x c :=
  fun ⟨q, _⟩ => q.elim

end PolyIso

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

namespace PolyIso

variable {X : Type u}

@[simp] theorem mem_list (x : X) (l : List X) : Mem List x l ↔ x ∈ l :=
  List.mem_iff_get.symm

@[simp] theorem mem_option (x : X) (o : Option X) : Mem Option x o ↔ x ∈ o := by
  cases o with
  | none => exact iff_of_false (fun ⟨q, _⟩ => nomatch q) (by simp)
  | some y => exact ⟨fun ⟨_, e⟩ => congrArg some e, fun h => ⟨.unit, Option.some.inj h⟩⟩

@[simp] theorem mem_array (x : X) (c : Array X) : Mem Array x c ↔ x ∈ c :=
  List.mem_iff_get.symm.trans Array.mem_def.symm

end PolyIso

/-! ### Products, sums, functions and dependent pairs

The forms the command reads off an argument type are functors with instances too, built from
the instances of their parts, with the shapes and positions of the occurrence structures of
`Model/Occ.lean`. So the induction hypothesis of every nested argument has its instance. A
composite `fun X => F (G X)` is tried before the instances of declared types, which may also
apply (`fun X => T (H X)`), as the command reads it so too. `fun X => A × X` and
`fun X => A ⊕ X` are `Prod A` and `Sum A` for Lean's instance search, so they have instances of
their own. -/

namespace Occ

/-- Dependent case analysis on a sum, for the positions of a product. -/
def sumRec {α : Type u} {β : Type v} {γ : α ⊕ β → Sort s} (f : ∀ a, γ (.inl a))
    (g : ∀ b, γ (.inr b)) : ∀ x, γ x
  | .inl a => f a
  | .inr b => g b

/-- The positions of a sum, lifted to one universe. -/
def SumPos {Sh₁ : Type s} {Sh₂ : Type s'} (Pos₁ : Sh₁ → Type p) (Pos₂ : Sh₂ → Type p') :
    Sh₁ ⊕ Sh₂ → Type (max p p')
  | .inl sh => ULift.{p'} (Pos₁ sh)
  | .inr sh => ULift.{p} (Pos₂ sh)

/-- Extensionality for the layers of a function: a family of layers is a shape function and a
contents function. -/
theorem pi_ext {A : Type a} {ShA : A → Type s} {PosA : ∀ x, ShA x → Type p}
    {X : ∀ x (sh : ShA x), PosA x sh → Type u}
    (T : ∀ x, Σ sh : ShA x, (q : PosA x sh) → X x sh q) (sh : ∀ x, ShA x)
    (c : (q : Σ x, PosA x (sh x)) → X q.1 (sh q.1) q.2)
    (h : ∀ x, T x = ⟨sh x, fun q => c ⟨x, q⟩⟩) :
    (⟨fun x => (T x).1, fun q => (T q.1).2 q.2⟩ :
      Σ sh : ∀ x, ShA x, (q : Σ x, PosA x (sh x)) → X q.1 (sh q.1) q.2) = ⟨sh, c⟩ := by
  have : T = fun x => ⟨sh x, fun q => c ⟨x, q⟩⟩ := funext h
  subst this
  rfl

/-- The same over a proposition. -/
theorem piP_ext {P : Prop} {ShP : P → Type s} {PosP : ∀ h, ShP h → Type p}
    {X : ∀ h (sh : ShP h), PosP h sh → Type u}
    (T : ∀ h, Σ sh : ShP h, (q : PosP h sh) → X h sh q) (sh : ∀ h, ShP h)
    (c : (q : Σ' h, PosP h (sh h)) → X q.1 (sh q.1) q.2)
    (h : ∀ h, T h = ⟨sh h, fun q => c ⟨h, q⟩⟩) :
    (⟨fun h => (T h).1, fun q => (T q.1).2 q.2⟩ :
      Σ sh : ∀ h, ShP h, (q : Σ' h, PosP h (sh h)) → X q.1 (sh q.1) q.2) = ⟨sh, c⟩ := by
  have : T = fun h => ⟨sh h, fun q => c ⟨h, q⟩⟩ := funext h
  subst this
  rfl

/-- Extensionality for the layers of a composite: the inner layers at the positions of an
outer shape. -/
theorem comp_ext {Sh : Type s} {Pos : Sh → Type p} {Sh' : ∀ sh, Pos sh → Type s'}
    {Pos' : ∀ sh (q : Pos sh), Sh' sh q → Type p'}
    {X : ∀ sh (q : Pos sh) (sh' : Sh' sh q), Pos' sh q sh' → Type u} (sh : Sh)
    (T : ∀ q : Pos sh, Σ sh' : Sh' sh q, (r : Pos' sh q sh') → X sh q sh' r) (t : ∀ q, Sh' sh q)
    (c : (r : Σ q, Pos' sh q (t q)) → X sh r.1 (t r.1) r.2)
    (h : ∀ q, T q = ⟨t q, fun r => c ⟨q, r⟩⟩) :
    (⟨⟨sh, fun q => (T q).1⟩, fun r => (T r.1).2 r.2⟩ :
      Σ z : Σ sh, (q : Pos sh) → Sh' sh q, (r : Σ q, Pos' z.1 q (z.2 q)) → X z.1 r.1 (z.2 r.1) r.2) =
      ⟨⟨sh, t⟩, c⟩ := by
  have : T = fun q => ⟨t q, fun r => c ⟨q, r⟩⟩ := funext h
  subst this
  rfl

end Occ

/-- The indices of the positions of a sum. -/
def IOcc.sumIdx {J : Type j} {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p} {Sh₂ : Type s'}
    {Pos₂ : Sh₂ → Type p'} (pidx₁ : (sh : Sh₁) → Pos₁ sh → J)
    (pidx₂ : (sh : Sh₂) → Pos₂ sh → J) : (sh : Sh₁ ⊕ Sh₂) → Occ.SumPos Pos₁ Pos₂ sh → J
  | .inl sh, q => pidx₁ sh q.down
  | .inr sh, q => pidx₂ sh q.down

namespace PolyIso

section Forms

variable {F₁ : Type u → Type v} {F₂ : Type u → Type v'} {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p}
  {Sh₂ : Type s'} {Pos₂ : Sh₂ → Type p'}

/-- A product: a pair of shapes, the sum of the positions. -/
instance instProd [h₁ : PolyIso F₁ Sh₁ Pos₁] [h₂ : PolyIso F₂ Sh₂ Pos₂] :
    PolyIso (fun X => F₁ X × F₂ X) (Sh₁ × Sh₂) (fun sh => Pos₁ sh.1 ⊕ Pos₂ sh.2) where
  equiv := {
    toFun x := ⟨((h₁.equiv x.1).1, (h₂.equiv x.2).1), Occ.sumRec (h₁.equiv x.1).2 (h₂.equiv x.2).2⟩
    invFun z := (h₁.equiv.symm ⟨z.1.1, fun q => z.2 (.inl q)⟩,
      h₂.equiv.symm ⟨z.1.2, fun q => z.2 (.inr q)⟩)
    left_inv x := Prod.ext (h₁.equiv.symm_apply_apply x.1) (h₂.equiv.symm_apply_apply x.2)
    right_inv := fun ⟨⟨s₁, s₂⟩, c⟩ => by
      dsimp only
      generalize e₁ : h₁.equiv (h₁.equiv.symm ⟨s₁, fun q => c (.inl q)⟩) = z₁
      generalize e₂ : h₂.equiv (h₂.equiv.symm ⟨s₂, fun q => c (.inr q)⟩) = z₂
      rw [Equiv.apply_symm_apply] at e₁ e₂
      subst e₁ e₂
      exact congrArg (Sigma.mk (s₁, s₂)) (funext fun q => by cases q <;> rfl) }

/-- A sum: a shape of either side, its positions. -/
instance instSum [h₁ : PolyIso F₁ Sh₁ Pos₁] [h₂ : PolyIso F₂ Sh₂ Pos₂] :
    PolyIso (fun X => F₁ X ⊕ F₂ X) (Sh₁ ⊕ Sh₂) (Occ.SumPos Pos₁ Pos₂) where
  equiv := {
    toFun
      | .inl x => ⟨.inl (h₁.equiv x).1, fun q => (h₁.equiv x).2 q.down⟩
      | .inr x => ⟨.inr (h₂.equiv x).1, fun q => (h₂.equiv x).2 q.down⟩
    invFun
      | ⟨.inl sh, c⟩ => .inl (h₁.equiv.symm ⟨sh, fun q => c ⟨q⟩⟩)
      | ⟨.inr sh, c⟩ => .inr (h₂.equiv.symm ⟨sh, fun q => c ⟨q⟩⟩)
    left_inv
      | .inl x => congrArg Sum.inl (h₁.equiv.symm_apply_apply x)
      | .inr x => congrArg Sum.inr (h₂.equiv.symm_apply_apply x)
    right_inv
      | ⟨.inl sh, c⟩ => by
        dsimp only
        generalize e : h₁.equiv (h₁.equiv.symm ⟨sh, fun q => c ⟨q⟩⟩) = z
        rw [Equiv.apply_symm_apply] at e
        subst e
        rfl
      | ⟨.inr sh, c⟩ => by
        dsimp only
        generalize e : h₂.equiv (h₂.equiv.symm ⟨sh, fun q => c ⟨q⟩⟩) = z
        rw [Equiv.apply_symm_apply] at e
        subst e
        rfl }

/-- `fun X => A × X`, which instance search sees as `Prod A`. -/
instance instProdRight (A : Type v) : PolyIso (Prod.{v, u} A) (A × Unit) (fun _ => Empty ⊕ Unit) :=
  @instProd (fun _ => A) (fun X => X) A (fun _ => Empty) Unit (fun _ => Unit) _ _

/-- `fun X => A ⊕ X`, which instance search sees as `Sum A`. -/
instance instSumRight (A : Type v) :
    PolyIso (Sum.{v, u} A) (A ⊕ Unit) (Occ.SumPos (fun _ => Empty) (fun _ => Unit)) :=
  @instSum (fun _ => A) (fun X => X) A (fun _ => Empty) Unit (fun _ => Unit) _ _

theorem equiv_prod [h₁ : PolyIso F₁ Sh₁ Pos₁] [h₂ : PolyIso F₂ Sh₂ Pos₂] {X : Type u}
    (x : F₁ X × F₂ X) :
    (instProd (h₁ := h₁) (h₂ := h₂)).equiv x =
      ⟨((h₁.equiv x.1).1, (h₂.equiv x.2).1), Occ.sumRec (h₁.equiv x.1).2 (h₂.equiv x.2).2⟩ :=
  rfl

theorem equiv_sum_inl [h₁ : PolyIso F₁ Sh₁ Pos₁] [h₂ : PolyIso F₂ Sh₂ Pos₂] {X : Type u}
    (x : F₁ X) :
    (instSum (h₁ := h₁) (h₂ := h₂)).equiv (.inl x) =
      ⟨.inl (h₁.equiv x).1, fun q => (h₁.equiv x).2 (ULift.down q)⟩ :=
  rfl

theorem equiv_sum_inr [h₁ : PolyIso F₁ Sh₁ Pos₁] [h₂ : PolyIso F₂ Sh₂ Pos₂] {X : Type u}
    (x : F₂ X) :
    (instSum (h₁ := h₁) (h₂ := h₂)).equiv (.inr x) =
      ⟨.inr (h₂.equiv x).1, fun q => (h₂.equiv x).2 (ULift.down q)⟩ :=
  rfl

variable {F₁' : Type u' → Type w} {F₂' : Type u' → Type w'}

instance [h₁ : PolyIso F₁ Sh₁ Pos₁] [h₁' : PolyIso F₁' Sh₁ Pos₁] [m₁ : PolyMap F₁ F₁']
    [h₂ : PolyIso F₂ Sh₂ Pos₂] [h₂' : PolyIso F₂' Sh₂ Pos₂] [m₂ : PolyMap F₂ F₂'] :
    PolyMap (fun X => F₁ X × F₂ X) (fun X => F₁' X × F₂' X) where
  map f x := (PolyMap.map (self := m₁) Pos₁ f x.1, PolyMap.map (self := m₂) Pos₂ f x.2)
  equiv_map f x := by
    rw [equiv_prod, equiv_prod]
    generalize e₁ : h₁'.equiv (PolyMap.map (self := m₁) Pos₁ f x.1) = z₁
    generalize e₂ : h₂'.equiv (PolyMap.map (self := m₂) Pos₂ f x.2) = z₂
    rw [PolyMap.equiv_map] at e₁ e₂
    subst e₁ e₂
    exact congrArg (Sigma.mk _) (funext fun q => by cases q <;> rfl)

instance [h₁ : PolyIso F₁ Sh₁ Pos₁] [h₁' : PolyIso F₁' Sh₁ Pos₁] [m₁ : PolyMap F₁ F₁']
    [h₂ : PolyIso F₂ Sh₂ Pos₂] [h₂' : PolyIso F₂' Sh₂ Pos₂] [m₂ : PolyMap F₂ F₂'] :
    PolyMap (fun X => F₁ X ⊕ F₂ X) (fun X => F₁' X ⊕ F₂' X) where
  map f
    | .inl x => .inl (PolyMap.map (self := m₁) Pos₁ f x)
    | .inr x => .inr (PolyMap.map (self := m₂) Pos₂ f x)
  equiv_map f
    | .inl x => by
      rw [equiv_sum_inl, equiv_sum_inl]
      generalize e : h₁'.equiv (PolyMap.map (self := m₁) Pos₁ f x) = z
      rw [PolyMap.equiv_map] at e
      subst e
      rfl
    | .inr x => by
      rw [equiv_sum_inr, equiv_sum_inr]
      generalize e : h₂'.equiv (PolyMap.map (self := m₂) Pos₂ f x) = z
      rw [PolyMap.equiv_map] at e
      subst e
      rfl

@[simp] theorem mem_prod [PolyIso F₁ Sh₁ Pos₁] [PolyIso F₂ Sh₂ Pos₂] {X : Type u} (x : X)
    (c : F₁ X × F₂ X) :
    Mem (no_index (fun X => F₁ X × F₂ X)) x c ↔ Mem F₁ x c.1 ∨ Mem F₂ x c.2 :=
  ⟨fun ⟨q, e⟩ => match q, e with
    | .inl q, e => .inl ⟨q, e⟩
    | .inr q, e => .inr ⟨q, e⟩,
    fun h => h.elim (fun ⟨q, e⟩ => ⟨.inl q, e⟩) (fun ⟨q, e⟩ => ⟨.inr q, e⟩)⟩

@[simp] theorem mem_sum_inl [PolyIso F₁ Sh₁ Pos₁] [PolyIso F₂ Sh₂ Pos₂] {X : Type u} (x : X)
    (c : F₁ X) : Mem (no_index (fun X => F₁ X ⊕ F₂ X)) x (.inl c) ↔ Mem F₁ x c :=
  ⟨fun ⟨q, e⟩ => ⟨q.down, e⟩, fun ⟨q, e⟩ => ⟨⟨q⟩, e⟩⟩

@[simp] theorem mem_sum_inr [PolyIso F₁ Sh₁ Pos₁] [PolyIso F₂ Sh₂ Pos₂] {X : Type u} (x : X)
    (c : F₂ X) : Mem (no_index (fun X => F₁ X ⊕ F₂ X)) x (.inr c) ↔ Mem F₂ x c :=
  ⟨fun ⟨q, e⟩ => ⟨q.down, e⟩, fun ⟨q, e⟩ => ⟨⟨q⟩, e⟩⟩

/-- Through a sum at any value: on the side the value is on. -/
@[simp] theorem mem_sum [PolyIso F₁ Sh₁ Pos₁] [PolyIso F₂ Sh₂ Pos₂] {X : Type u} (x : X)
    (c : F₁ X ⊕ F₂ X) :
    Mem (no_index (fun X => F₁ X ⊕ F₂ X)) x c ↔
      (∃ a, c = .inl a ∧ Mem F₁ x a) ∨ ∃ b, c = .inr b ∧ Mem F₂ x b := by
  cases c with
  | inl a => simp only [mem_sum_inl, Sum.inl.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, or_false]
  | inr b => simp only [mem_sum_inr, Sum.inr.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, false_or]

end Forms

section Dependent

variable (A : Type a) {ShA : A → Type s} {PosA : ∀ x, ShA x → Type p} {GA : A → Type u → Type v}

/-- A function from a constant type: a shape at every point, a point with a position there. -/
instance instPi [h : ∀ x, PolyIso (GA x) (ShA x) (PosA x)] :
    PolyIso (fun X => ∀ x, GA x X) (∀ x, ShA x) (fun sh => Σ x, PosA x (sh x)) where
  equiv := {
    toFun k := ⟨fun x => ((h x).equiv (k x)).1, fun q => ((h q.1).equiv (k q.1)).2 q.2⟩
    invFun z x := (h x).equiv.symm ⟨z.1 x, fun q => z.2 ⟨x, q⟩⟩
    left_inv k := funext fun x => (h x).equiv.symm_apply_apply (k x)
    right_inv := fun ⟨sh, c⟩ => Occ.pi_ext _ sh c fun x => (h x).equiv.apply_symm_apply _ }

/-- A dependent pair over a constant type: a point with a shape there, its positions. -/
instance instSigma [h : ∀ x, PolyIso (GA x) (ShA x) (PosA x)] :
    PolyIso (fun X => Σ x, GA x X) (Σ x, ShA x) (fun sh => PosA sh.1 sh.2) where
  equiv := {
    toFun z := ⟨⟨z.1, ((h z.1).equiv z.2).1⟩, ((h z.1).equiv z.2).2⟩
    invFun w := ⟨w.1.1, (h w.1.1).equiv.symm ⟨w.1.2, w.2⟩⟩
    left_inv := fun ⟨x, y⟩ => by
      show (⟨x, (h x).equiv.symm ((h x).equiv y)⟩ : Σ x, GA x _) = _
      rw [Equiv.symm_apply_apply]
    right_inv := fun ⟨⟨x, sh⟩, c⟩ => by
      dsimp only
      generalize e : (h x).equiv ((h x).equiv.symm ⟨sh, c⟩) = z
      rw [Equiv.apply_symm_apply] at e
      subst e
      rfl }

theorem equiv_pi [h : ∀ x, PolyIso (GA x) (ShA x) (PosA x)] {X : Type u} (k : ∀ x, GA x X) :
    (instPi A (h := h)).equiv k =
      ⟨fun x => ((h x).equiv (k x)).1, fun q => ((h q.1).equiv (k q.1)).2 q.2⟩ :=
  rfl

theorem equiv_sigma [h : ∀ x, PolyIso (GA x) (ShA x) (PosA x)] {X : Type u} (z : Σ x, GA x X) :
    (instSigma A (h := h)).equiv z = ⟨⟨z.1, ((h z.1).equiv z.2).1⟩, ((h z.1).equiv z.2).2⟩ :=
  rfl

variable {GA' : A → Type u' → Type w}

instance [h : ∀ x, PolyIso (GA x) (ShA x) (PosA x)] [h' : ∀ x, PolyIso (GA' x) (ShA x) (PosA x)]
    [m : ∀ x, PolyMap (GA x) (GA' x)] : PolyMap (fun X => ∀ x, GA x X) (fun X => ∀ x, GA' x X) where
  map f k x := PolyMap.map (self := m x) (PosA x) f (k x)
  equiv_map f k := by
    rw [equiv_pi, equiv_pi]
    exact Occ.pi_ext _ _ _ fun x => PolyMap.equiv_map _ _

instance [h : ∀ x, PolyIso (GA x) (ShA x) (PosA x)] [h' : ∀ x, PolyIso (GA' x) (ShA x) (PosA x)]
    [m : ∀ x, PolyMap (GA x) (GA' x)] : PolyMap (fun X => Σ x, GA x X) (fun X => Σ x, GA' x X) where
  map f z := ⟨z.1, PolyMap.map (self := m z.1) (PosA z.1) f z.2⟩
  equiv_map f := fun ⟨x, y⟩ => by
    rw [equiv_sigma, equiv_sigma]
    generalize e : (h' x).equiv (PolyMap.map (self := m x) (PosA x) f y) = z
    rw [PolyMap.equiv_map] at e
    subst e
    rfl

variable {A}

@[simp] theorem mem_pi [∀ x, PolyIso (GA x) (ShA x) (PosA x)] {X : Type u} (y : X)
    (k : ∀ x, GA x X) : Mem (fun X => ∀ x, GA x X) y k ↔ ∃ x, Mem (GA x) y (k x) :=
  ⟨fun ⟨q, e⟩ => ⟨q.1, q.2, e⟩, fun ⟨x, q, e⟩ => ⟨⟨x, q⟩, e⟩⟩

@[simp] theorem mem_sigma [∀ x, PolyIso (GA x) (ShA x) (PosA x)] {X : Type u} (y : X)
    (z : Σ x, GA x X) : Mem (fun X => Σ x, GA x X) y z ↔ Mem (GA z.1) y z.2 :=
  Iff.rfl

end Dependent

section Prop'

variable (P : Prop) {ShP : P → Type s} {PosP : ∀ h, ShP h → Type p} {GP : P → Type u → Type v}

/-- A function from a proposition. -/
instance instPiP [h : ∀ h, PolyIso (GP h) (ShP h) (PosP h)] :
    PolyIso (fun X => ∀ h, GP h X) (∀ h, ShP h) (fun sh => Σ' h, PosP h (sh h)) where
  equiv := {
    toFun k := ⟨fun x => ((h x).equiv (k x)).1, fun q => ((h q.1).equiv (k q.1)).2 q.2⟩
    invFun z x := (h x).equiv.symm ⟨z.1 x, fun q => z.2 ⟨x, q⟩⟩
    left_inv k := funext fun x => (h x).equiv.symm_apply_apply (k x)
    right_inv := fun ⟨sh, c⟩ => Occ.piP_ext _ sh c fun x => (h x).equiv.apply_symm_apply _ }

theorem equiv_piP [h : ∀ h, PolyIso (GP h) (ShP h) (PosP h)] {X : Type u} (k : ∀ h, GP h X) :
    (instPiP P (h := h)).equiv k =
      ⟨fun x => ((h x).equiv (k x)).1, fun q => ((h q.1).equiv (k q.1)).2 q.2⟩ :=
  rfl

variable {GP' : P → Type u' → Type w}

instance [h : ∀ h, PolyIso (GP h) (ShP h) (PosP h)] [h' : ∀ h, PolyIso (GP' h) (ShP h) (PosP h)]
    [m : ∀ h, PolyMap (GP h) (GP' h)] : PolyMap (fun X => ∀ h, GP h X) (fun X => ∀ h, GP' h X) where
  map f k x := PolyMap.map (self := m x) (PosP x) f (k x)
  equiv_map f k := by
    rw [equiv_piP, equiv_piP]
    exact Occ.piP_ext _ _ _ fun x => PolyMap.equiv_map _ _

variable {P}

@[simp] theorem mem_piP [∀ h, PolyIso (GP h) (ShP h) (PosP h)] {X : Type u} (y : X)
    (k : ∀ h, GP h X) : Mem (fun X => ∀ h, GP h X) y k ↔ ∃ h, Mem (GP h) y (k h) :=
  ⟨fun ⟨q, e⟩ => ⟨q.1, q.2, e⟩, fun ⟨x, q, e⟩ => ⟨⟨x, q⟩, e⟩⟩

end Prop'

section Comp

variable {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {Pos' : Sh' → Type p'}
  {G : Type u' → Type v} {H : Type u → Type u'}

/-- A functor applied to a functor: a shape of the outer one with a shape of the inner one at
each of its positions, a position of the outer one with a position of the inner shape there. -/
instance (priority := 1100) instComp [hG : PolyIso G Sh Pos] [hH : PolyIso H Sh' Pos'] :
    PolyIso (fun X => G (H X)) (Σ sh, Pos sh → Sh') (fun z => Σ q, Pos' (z.2 q)) where
  equiv {X} := {
    toFun x := ⟨⟨(hG.equiv x).1, fun q => (hH.equiv ((hG.equiv x).2 q)).1⟩,
      fun r => (hH.equiv ((hG.equiv x).2 r.1)).2 r.2⟩
    invFun z := hG.equiv.symm ⟨z.1.1, fun q => hH.equiv.symm ⟨z.1.2 q, fun r => z.2 ⟨q, r⟩⟩⟩
    left_inv x := by
      show hG.equiv.symm ⟨(hG.equiv x).1, fun q => hH.equiv.symm (hH.equiv ((hG.equiv x).2 q))⟩ = x
      simp only [Equiv.symm_apply_apply]
      exact hG.equiv.symm_apply_apply x
    right_inv := fun ⟨⟨sh, t⟩, c⟩ => by
      dsimp only
      generalize e :
        hG.equiv (hG.equiv.symm ⟨sh, fun q => hH.equiv.symm ⟨t q, fun r => c ⟨q, r⟩⟩⟩) = U
      rw [Equiv.apply_symm_apply] at e
      subst e
      dsimp only at c
      refine Occ.comp_ext (Sh' := fun _ _ => Sh') (Pos' := fun _ _ s => Pos' s)
        (X := fun _ _ _ _ => X) sh _ t c fun q => ?_
      exact hH.equiv.apply_symm_apply _ }

theorem equiv_comp [hG : PolyIso G Sh Pos] [hH : PolyIso H Sh' Pos'] {X : Type u} (x : G (H X)) :
    (instComp (hG := hG) (hH := hH)).equiv x =
      ⟨⟨(hG.equiv x).1, fun q => (hH.equiv ((hG.equiv x).2 q)).1⟩,
        fun r => (hH.equiv ((hG.equiv x).2 r.1)).2 r.2⟩ :=
  rfl

variable {G' : Type v'' → Type w} {H' : Type u'' → Type v''}

instance [hG : PolyIso G Sh Pos] [hG' : PolyIso G' Sh Pos] [mG : PolyMap G G']
    [hH : PolyIso H Sh' Pos'] [hH' : PolyIso H' Sh' Pos'] [mH : PolyMap H H'] :
    PolyMap (fun X => G (H X)) (fun X => G' (H' X)) where
  map f x := PolyMap.map (self := mG) Pos (PolyMap.map (self := mH) Pos' f) x
  equiv_map {X Y} f x := by
    rw [equiv_comp, equiv_comp]
    generalize e : hG'.equiv (PolyMap.map (self := mG) Pos (PolyMap.map (self := mH) Pos' f) x) = z
    rw [PolyMap.equiv_map] at e
    subst e
    exact Occ.comp_ext (Sh' := fun _ _ => Sh') (Pos' := fun _ _ s => Pos' s)
      (X := fun _ _ _ _ => Y) _ _ _ _ fun q => PolyMap.equiv_map _ _

/-- The functor is not indexed: with `H` the identity it is `G` up to eta. -/
@[simp] theorem mem_comp [PolyIso G Sh Pos] [PolyIso H Sh' Pos'] {X : Type u} (x : X)
    (c : G (H X)) : Mem (no_index (fun X => G (H X))) x c ↔ ∃ y, Mem G y c ∧ Mem H x y := by
  constructor
  · rintro ⟨r, e⟩
    exact ⟨_, ⟨r.1, rfl⟩, r.2, e⟩
  · rintro ⟨_, ⟨q, rfl⟩, r, e⟩
    exact ⟨⟨q, r⟩, e⟩

end Comp

end PolyIso

/-! ### Functors on families

The same forms for functors on families, with the index of every position: the family at an
index, constants, products, sums, functions, dependent pairs, a functor with an instance at the
family's index (`fun X => F (X i)`), and the composites across the two kinds. A functor on
families at a constant family is a plain functor (`fun X => G fun _ => X`). -/

namespace IPolyIso

section Forms

variable {J : Type j}

/-- The family at an index. -/
instance instHole (i : J) :
    IPolyIso (fun X : J → Type u => X i) Unit (fun _ => Unit) (fun _ _ => i) :=
  ⟨⟨fun x => ⟨(), fun _ => x⟩, fun z => z.2 (), fun _ => rfl, fun _ => rfl⟩⟩

/-- A constant. -/
instance (priority := high) instConst (A : Type v) :
    IPolyIso (fun _ : J → Type u => A) A (fun _ => Empty) (fun _ e => e.elim) :=
  ⟨⟨fun a => ⟨a, fun e => e.elim⟩, fun z => z.1, fun _ => rfl,
    fun ⟨_, _⟩ => congrArg _ (funext fun x => x.elim)⟩⟩

/-- A functor with an instance at the index `i` of the family: every position is at `i`. -/
instance (priority := 1200) instAt {F : Type u → Type v} {Sh : Type s} {Pos : Sh → Type p}
    [h : PolyIso F Sh Pos] (i : J) :
    IPolyIso (fun X : J → Type u => F (X i)) Sh Pos (fun _ _ => i) :=
  ⟨h.equiv⟩

variable {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p} {pidx₁ : (sh : Sh₁) → Pos₁ sh → J}
  {Sh₂ : Type s'} {Pos₂ : Sh₂ → Type p'} {pidx₂ : (sh : Sh₂) → Pos₂ sh → J}
  {G₁ : (J → Type u) → Type v} {G₂ : (J → Type u) → Type v'}

/-- A product: a pair of shapes, the sum of the positions. -/
instance instProd [h₁ : IPolyIso G₁ Sh₁ Pos₁ pidx₁] [h₂ : IPolyIso G₂ Sh₂ Pos₂ pidx₂] :
    IPolyIso (fun X => G₁ X × G₂ X) (Sh₁ × Sh₂) (fun sh => Pos₁ sh.1 ⊕ Pos₂ sh.2)
      (fun sh q => Sum.elim (pidx₁ sh.1) (pidx₂ sh.2) q) where
  equiv := {
    toFun x := ⟨((h₁.equiv x.1).1, (h₂.equiv x.2).1), Occ.sumRec (h₁.equiv x.1).2 (h₂.equiv x.2).2⟩
    invFun z := (h₁.equiv.symm ⟨z.1.1, fun q => z.2 (.inl q)⟩,
      h₂.equiv.symm ⟨z.1.2, fun q => z.2 (.inr q)⟩)
    left_inv x := Prod.ext (h₁.equiv.symm_apply_apply x.1) (h₂.equiv.symm_apply_apply x.2)
    right_inv := fun ⟨⟨s₁, s₂⟩, c⟩ => by
      dsimp only
      generalize e₁ : h₁.equiv (h₁.equiv.symm ⟨s₁, fun q => c (.inl q)⟩) = z₁
      generalize e₂ : h₂.equiv (h₂.equiv.symm ⟨s₂, fun q => c (.inr q)⟩) = z₂
      rw [Equiv.apply_symm_apply] at e₁ e₂
      subst e₁ e₂
      exact congrArg (Sigma.mk (s₁, s₂)) (funext fun q => by cases q <;> rfl) }

/-- A sum: a shape of either side, its positions. -/
instance instSum [h₁ : IPolyIso G₁ Sh₁ Pos₁ pidx₁] [h₂ : IPolyIso G₂ Sh₂ Pos₂ pidx₂] :
    IPolyIso (fun X => G₁ X ⊕ G₂ X) (Sh₁ ⊕ Sh₂) (Occ.SumPos Pos₁ Pos₂)
      (IOcc.sumIdx pidx₁ pidx₂) where
  equiv := {
    toFun
      | .inl x => ⟨.inl (h₁.equiv x).1, fun q => (h₁.equiv x).2 q.down⟩
      | .inr x => ⟨.inr (h₂.equiv x).1, fun q => (h₂.equiv x).2 q.down⟩
    invFun
      | ⟨.inl sh, c⟩ => .inl (h₁.equiv.symm ⟨sh, fun q => c ⟨q⟩⟩)
      | ⟨.inr sh, c⟩ => .inr (h₂.equiv.symm ⟨sh, fun q => c ⟨q⟩⟩)
    left_inv
      | .inl x => congrArg Sum.inl (h₁.equiv.symm_apply_apply x)
      | .inr x => congrArg Sum.inr (h₂.equiv.symm_apply_apply x)
    right_inv
      | ⟨.inl sh, c⟩ => by
        dsimp only
        generalize e : h₁.equiv (h₁.equiv.symm ⟨sh, fun q => c ⟨q⟩⟩) = z
        rw [Equiv.apply_symm_apply] at e
        subst e
        rfl
      | ⟨.inr sh, c⟩ => by
        dsimp only
        generalize e : h₂.equiv (h₂.equiv.symm ⟨sh, fun q => c ⟨q⟩⟩) = z
        rw [Equiv.apply_symm_apply] at e
        subst e
        rfl }

theorem equiv_prod [h₁ : IPolyIso G₁ Sh₁ Pos₁ pidx₁] [h₂ : IPolyIso G₂ Sh₂ Pos₂ pidx₂]
    {X : J → Type u} (x : G₁ X × G₂ X) :
    (instProd (h₁ := h₁) (h₂ := h₂)).equiv x =
      ⟨((h₁.equiv x.1).1, (h₂.equiv x.2).1), Occ.sumRec (h₁.equiv x.1).2 (h₂.equiv x.2).2⟩ :=
  rfl

theorem equiv_sum_inl [h₁ : IPolyIso G₁ Sh₁ Pos₁ pidx₁] [h₂ : IPolyIso G₂ Sh₂ Pos₂ pidx₂]
    {X : J → Type u} (x : G₁ X) :
    (instSum (h₁ := h₁) (h₂ := h₂)).equiv (.inl x) =
      ⟨.inl (h₁.equiv x).1, fun q => (h₁.equiv x).2 (ULift.down q)⟩ :=
  rfl

theorem equiv_sum_inr [h₁ : IPolyIso G₁ Sh₁ Pos₁ pidx₁] [h₂ : IPolyIso G₂ Sh₂ Pos₂ pidx₂]
    {X : J → Type u} (x : G₂ X) :
    (instSum (h₁ := h₁) (h₂ := h₂)).equiv (.inr x) =
      ⟨.inr (h₂.equiv x).1, fun q => (h₂.equiv x).2 (ULift.down q)⟩ :=
  rfl

instance (i : J) : IPolyMap (fun X : J → Type u => X i) (fun X : J → Type u' => X i) where
  map f x := f i x
  equiv_map _ _ := rfl

instance (A : Type v) : IPolyMap (fun _ : J → Type u => A) (fun _ : J → Type u' => A) where
  map _ a := a
  equiv_map _ a := congrArg (Sigma.mk a) (funext fun e => e.elim)

instance {F : Type u → Type v} {F' : Type u' → Type v'} {Sh : Type s} {Pos : Sh → Type p}
    [h : PolyIso F Sh Pos] [h' : PolyIso F' Sh Pos] [m : PolyMap F F'] (i : J) :
    IPolyMap (fun X : J → Type u => F (X i)) (fun X : J → Type u' => F' (X i)) where
  map f x := PolyMap.map (self := m) Pos (f i) x
  equiv_map f x := PolyMap.equiv_map (self := m) (f i) x

variable {G₁' : (J → Type u') → Type w} {G₂' : (J → Type u') → Type w'}

instance [h₁ : IPolyIso G₁ Sh₁ Pos₁ pidx₁] [h₁' : IPolyIso G₁' Sh₁ Pos₁ pidx₁]
    [m₁ : IPolyMap G₁ G₁'] [h₂ : IPolyIso G₂ Sh₂ Pos₂ pidx₂] [h₂' : IPolyIso G₂' Sh₂ Pos₂ pidx₂]
    [m₂ : IPolyMap G₂ G₂'] : IPolyMap (fun X => G₁ X × G₂ X) (fun X => G₁' X × G₂' X) where
  map f x := (IPolyMap.map (self := m₁) pidx₁ f x.1, IPolyMap.map (self := m₂) pidx₂ f x.2)
  equiv_map f x := by
    rw [equiv_prod, equiv_prod]
    generalize e₁ : h₁'.equiv (IPolyMap.map (self := m₁) pidx₁ f x.1) = z₁
    generalize e₂ : h₂'.equiv (IPolyMap.map (self := m₂) pidx₂ f x.2) = z₂
    rw [IPolyMap.equiv_map] at e₁ e₂
    subst e₁ e₂
    exact congrArg (Sigma.mk _) (funext fun q => by cases q <;> rfl)

instance [h₁ : IPolyIso G₁ Sh₁ Pos₁ pidx₁] [h₁' : IPolyIso G₁' Sh₁ Pos₁ pidx₁]
    [m₁ : IPolyMap G₁ G₁'] [h₂ : IPolyIso G₂ Sh₂ Pos₂ pidx₂] [h₂' : IPolyIso G₂' Sh₂ Pos₂ pidx₂]
    [m₂ : IPolyMap G₂ G₂'] : IPolyMap (fun X => G₁ X ⊕ G₂ X) (fun X => G₁' X ⊕ G₂' X) where
  map f
    | .inl x => .inl (IPolyMap.map (self := m₁) pidx₁ f x)
    | .inr x => .inr (IPolyMap.map (self := m₂) pidx₂ f x)
  equiv_map f
    | .inl x => by
      rw [equiv_sum_inl, equiv_sum_inl]
      generalize e : h₁'.equiv (IPolyMap.map (self := m₁) pidx₁ f x) = z
      rw [IPolyMap.equiv_map] at e
      subst e
      rfl
    | .inr x => by
      rw [equiv_sum_inr, equiv_sum_inr]
      generalize e : h₂'.equiv (IPolyMap.map (self := m₂) pidx₂ f x) = z
      rw [IPolyMap.equiv_map] at e
      subst e
      rfl

@[simp] theorem mem_prod [IPolyIso G₁ Sh₁ Pos₁ pidx₁] [IPolyIso G₂ Sh₂ Pos₂ pidx₂]
    {X : J → Type u} (j : J) (x : X j) (c : G₁ X × G₂ X) :
    Mem (no_index (fun X => G₁ X × G₂ X)) j x c ↔ Mem G₁ j x c.1 ∨ Mem G₂ j x c.2 :=
  ⟨fun ⟨q, e⟩ => match q, e with
    | .inl q, e => .inl ⟨q, e⟩
    | .inr q, e => .inr ⟨q, e⟩,
    fun h => h.elim (fun ⟨q, e⟩ => ⟨.inl q, e⟩) (fun ⟨q, e⟩ => ⟨.inr q, e⟩)⟩

@[simp] theorem mem_sum_inl [IPolyIso G₁ Sh₁ Pos₁ pidx₁] [IPolyIso G₂ Sh₂ Pos₂ pidx₂]
    {X : J → Type u} (j : J) (x : X j) (c : G₁ X) :
    Mem (no_index (fun X => G₁ X ⊕ G₂ X)) j x (.inl c) ↔ Mem G₁ j x c :=
  ⟨fun ⟨q, e⟩ => ⟨q.down, e⟩, fun ⟨q, e⟩ => ⟨⟨q⟩, e⟩⟩

@[simp] theorem mem_sum_inr [IPolyIso G₁ Sh₁ Pos₁ pidx₁] [IPolyIso G₂ Sh₂ Pos₂ pidx₂]
    {X : J → Type u} (j : J) (x : X j) (c : G₂ X) :
    Mem (no_index (fun X => G₁ X ⊕ G₂ X)) j x (.inr c) ↔ Mem G₂ j x c :=
  ⟨fun ⟨q, e⟩ => ⟨q.down, e⟩, fun ⟨q, e⟩ => ⟨⟨q⟩, e⟩⟩

/-- Through a sum at any value: on the side the value is on. -/
@[simp] theorem mem_sum [IPolyIso G₁ Sh₁ Pos₁ pidx₁] [IPolyIso G₂ Sh₂ Pos₂ pidx₂]
    {X : J → Type u} (j : J) (x : X j) (c : G₁ X ⊕ G₂ X) :
    Mem (no_index (fun X => G₁ X ⊕ G₂ X)) j x c ↔
      (∃ a, c = .inl a ∧ Mem G₁ j x a) ∨ ∃ b, c = .inr b ∧ Mem G₂ j x b := by
  cases c with
  | inl a => simp only [mem_sum_inl, Sum.inl.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, or_false]
  | inr b => simp only [mem_sum_inr, Sum.inr.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, false_or]

@[simp] theorem mem_hole {X : J → Type u} (i j : J) (x : X j) (c : X i) :
    Mem (fun X : J → Type u => X i) j x c ↔ (⟨i, c⟩ : Σ j, X j) = ⟨j, x⟩ :=
  ⟨fun ⟨_, e⟩ => e, fun e => ⟨(), e⟩⟩

/-- A property of every member at a hole is one of its content: what `simp` makes of a
hypothesis by membership at a hole after `mem_hole`, `∀ j t, i = j → HEq c t → P j t`. -/
@[simp] theorem forall_eq_heq_imp {X : J → Type u} {i : J} {c : X i} {P : ∀ j, X j → Prop} :
    (∀ j (t : X j), i = j → HEq c t → P j t) ↔ P i c :=
  ⟨fun h => h i c rfl HEq.rfl, fun h _ _ e hc => by subst e; cases hc; exact h⟩

/-- A property of every member at a hole or elsewhere is one of the hole's content and one of the
other members: what `simp` makes of a hypothesis by membership at several indices after
`mem_prod` and `mem_hole`, `∀ j t, (i = j ∧ HEq c t) ∨ Q j t → P j t`. -/
@[simp] theorem forall_eq_heq_or_imp {X : J → Type u} {i : J} {c : X i}
    {Q P : ∀ j, X j → Prop} :
    (∀ j (t : X j), (i = j ∧ HEq c t) ∨ Q j t → P j t) ↔ P i c ∧ ∀ j t, Q j t → P j t :=
  ⟨fun h => ⟨h i c (.inl ⟨rfl, HEq.rfl⟩), fun j t hq => h j t (.inr hq)⟩, fun h j t => by
    rintro (⟨rfl, hc⟩ | hq)
    · cases hc
      exact h.1
    · exact h.2 j t hq⟩

/-- The same with the hole last: `∀ j t, Q j t ∨ (i = j ∧ HEq c t) → P j t`. -/
@[simp] theorem forall_or_eq_heq_imp {X : J → Type u} {i : J} {c : X i}
    {Q P : ∀ j, X j → Prop} :
    (∀ j (t : X j), Q j t ∨ (i = j ∧ HEq c t) → P j t) ↔ (∀ j t, Q j t → P j t) ∧ P i c :=
  ⟨fun h => ⟨fun j t hq => h j t (.inl hq), h i c (.inr ⟨rfl, HEq.rfl⟩)⟩, fun h j t => by
    rintro (hq | ⟨rfl, hc⟩)
    · exact h.1 j t hq
    · cases hc
      exact h.2⟩

/-- A property of every member at an index through a leaf is one of the members of the leaf's
value: what `simp` makes of a hypothesis by membership at `F (X i)` after `mem_at`,
`∀ j t x, Q x → i = j → HEq x t → P j t`. -/
@[simp] theorem forall_forall_eq_heq_imp {X : J → Type u} {i : J} {Q : X i → Prop}
    {P : ∀ j, X j → Prop} :
    (∀ j (t : X j) (x : X i), Q x → i = j → HEq x t → P j t) ↔ ∀ x, Q x → P i x :=
  ⟨fun h x hx => h i x x hx rfl HEq.rfl, fun h _ _ x hx e hc => by
    subst e
    cases hc
    exact h x hx⟩

@[simp] theorem not_mem_const (A : Type v) {X : J → Type u} (j : J) (x : X j) (c : A) :
    ¬ Mem (fun _ : J → Type u => A) j x c :=
  fun ⟨q, _⟩ => q.elim

@[simp] theorem mem_at {F : Type u → Type v} {Sh : Type s} {Pos : Sh → Type p}
    [PolyIso F Sh Pos] {X : J → Type u} (i j : J) (x : X j) (c : F (X i)) :
    Mem (fun X : J → Type u => F (X i)) j x c ↔
      ∃ y, PolyIso.Mem F y c ∧ (⟨i, y⟩ : Σ j, X j) = ⟨j, x⟩ := by
  constructor
  · rintro ⟨q, e⟩
    exact ⟨_, ⟨q, rfl⟩, e⟩
  · rintro ⟨_, ⟨q, rfl⟩, e⟩
    exact ⟨q, e⟩

end Forms

section Dependent

variable {J : Type j} (A : Type a) {ShA : A → Type s} {PosA : ∀ x, ShA x → Type p}
  {pidxA : ∀ x (sh : ShA x), PosA x sh → J} {GA : A → (J → Type u) → Type v}

/-- A function from a constant type. -/
instance instPi [h : ∀ x, IPolyIso (GA x) (ShA x) (PosA x) (pidxA x)] :
    IPolyIso (fun X => ∀ x, GA x X) (∀ x, ShA x) (fun sh => Σ x, PosA x (sh x))
      (fun sh q => pidxA q.1 (sh q.1) q.2) where
  equiv := {
    toFun k := ⟨fun x => ((h x).equiv (k x)).1, fun q => ((h q.1).equiv (k q.1)).2 q.2⟩
    invFun z x := (h x).equiv.symm ⟨z.1 x, fun q => z.2 ⟨x, q⟩⟩
    left_inv k := funext fun x => (h x).equiv.symm_apply_apply (k x)
    right_inv := fun ⟨sh, c⟩ => Occ.pi_ext _ sh c fun x => (h x).equiv.apply_symm_apply _ }

/-- A dependent pair over a constant type. -/
instance instSigma [h : ∀ x, IPolyIso (GA x) (ShA x) (PosA x) (pidxA x)] :
    IPolyIso (fun X => Σ x, GA x X) (Σ x, ShA x) (fun sh => PosA sh.1 sh.2)
      (fun sh q => pidxA sh.1 sh.2 q) where
  equiv := {
    toFun z := ⟨⟨z.1, ((h z.1).equiv z.2).1⟩, ((h z.1).equiv z.2).2⟩
    invFun w := ⟨w.1.1, (h w.1.1).equiv.symm ⟨w.1.2, w.2⟩⟩
    left_inv := fun ⟨x, y⟩ => by
      show (⟨x, (h x).equiv.symm ((h x).equiv y)⟩ : Σ x, GA x _) = _
      rw [Equiv.symm_apply_apply]
    right_inv := fun ⟨⟨x, sh⟩, c⟩ => by
      dsimp only
      generalize e : (h x).equiv ((h x).equiv.symm ⟨sh, c⟩) = z
      rw [Equiv.apply_symm_apply] at e
      subst e
      rfl }

theorem equiv_pi [h : ∀ x, IPolyIso (GA x) (ShA x) (PosA x) (pidxA x)] {X : J → Type u}
    (k : ∀ x, GA x X) :
    (instPi A (h := h)).equiv k =
      ⟨fun x => ((h x).equiv (k x)).1, fun q => ((h q.1).equiv (k q.1)).2 q.2⟩ :=
  rfl

theorem equiv_sigma [h : ∀ x, IPolyIso (GA x) (ShA x) (PosA x) (pidxA x)] {X : J → Type u}
    (z : Σ x, GA x X) :
    (instSigma A (h := h)).equiv z = ⟨⟨z.1, ((h z.1).equiv z.2).1⟩, ((h z.1).equiv z.2).2⟩ :=
  rfl

variable {GA' : A → (J → Type u') → Type w}

instance [h : ∀ x, IPolyIso (GA x) (ShA x) (PosA x) (pidxA x)]
    [h' : ∀ x, IPolyIso (GA' x) (ShA x) (PosA x) (pidxA x)] [m : ∀ x, IPolyMap (GA x) (GA' x)] :
    IPolyMap (fun X => ∀ x, GA x X) (fun X => ∀ x, GA' x X) where
  map f k x := IPolyMap.map (self := m x) (pidxA x) f (k x)
  equiv_map f k := by
    rw [equiv_pi, equiv_pi]
    exact Occ.pi_ext _ _ _ fun x => IPolyMap.equiv_map _ _

instance [h : ∀ x, IPolyIso (GA x) (ShA x) (PosA x) (pidxA x)]
    [h' : ∀ x, IPolyIso (GA' x) (ShA x) (PosA x) (pidxA x)] [m : ∀ x, IPolyMap (GA x) (GA' x)] :
    IPolyMap (fun X => Σ x, GA x X) (fun X => Σ x, GA' x X) where
  map f z := ⟨z.1, IPolyMap.map (self := m z.1) (pidxA z.1) f z.2⟩
  equiv_map f := fun ⟨x, y⟩ => by
    rw [equiv_sigma, equiv_sigma]
    generalize e : (h' x).equiv (IPolyMap.map (self := m x) (pidxA x) f y) = z
    rw [IPolyMap.equiv_map] at e
    subst e
    rfl

variable {A}

@[simp] theorem mem_pi [∀ x, IPolyIso (GA x) (ShA x) (PosA x) (pidxA x)] {X : J → Type u}
    (j : J) (y : X j) (k : ∀ x, GA x X) :
    Mem (fun X => ∀ x, GA x X) j y k ↔ ∃ x, Mem (GA x) j y (k x) :=
  ⟨fun ⟨q, e⟩ => ⟨q.1, q.2, e⟩, fun ⟨x, q, e⟩ => ⟨⟨x, q⟩, e⟩⟩

@[simp] theorem mem_sigma [∀ x, IPolyIso (GA x) (ShA x) (PosA x) (pidxA x)] {X : J → Type u}
    (j : J) (y : X j) (z : Σ x, GA x X) :
    Mem (fun X => Σ x, GA x X) j y z ↔ Mem (GA z.1) j y z.2 :=
  Iff.rfl

end Dependent

section Prop'

variable {J : Type j} (P : Prop) {ShP : P → Type s} {PosP : ∀ h, ShP h → Type p}
  {pidxP : ∀ h (sh : ShP h), PosP h sh → J} {GP : P → (J → Type u) → Type v}

/-- A function from a proposition. -/
instance instPiP [h : ∀ h, IPolyIso (GP h) (ShP h) (PosP h) (pidxP h)] :
    IPolyIso (fun X => ∀ h, GP h X) (∀ h, ShP h) (fun sh => Σ' h, PosP h (sh h))
      (fun sh q => pidxP q.1 (sh q.1) q.2) where
  equiv := {
    toFun k := ⟨fun x => ((h x).equiv (k x)).1, fun q => ((h q.1).equiv (k q.1)).2 q.2⟩
    invFun z x := (h x).equiv.symm ⟨z.1 x, fun q => z.2 ⟨x, q⟩⟩
    left_inv k := funext fun x => (h x).equiv.symm_apply_apply (k x)
    right_inv := fun ⟨sh, c⟩ => Occ.piP_ext _ sh c fun x => (h x).equiv.apply_symm_apply _ }

theorem equiv_piP [h : ∀ h, IPolyIso (GP h) (ShP h) (PosP h) (pidxP h)] {X : J → Type u}
    (k : ∀ h, GP h X) :
    (instPiP P (h := h)).equiv k =
      ⟨fun x => ((h x).equiv (k x)).1, fun q => ((h q.1).equiv (k q.1)).2 q.2⟩ :=
  rfl

variable {GP' : P → (J → Type u') → Type w}

instance [h : ∀ h, IPolyIso (GP h) (ShP h) (PosP h) (pidxP h)]
    [h' : ∀ h, IPolyIso (GP' h) (ShP h) (PosP h) (pidxP h)] [m : ∀ h, IPolyMap (GP h) (GP' h)] :
    IPolyMap (fun X => ∀ h, GP h X) (fun X => ∀ h, GP' h X) where
  map f k x := IPolyMap.map (self := m x) (pidxP x) f (k x)
  equiv_map f k := by
    rw [equiv_piP, equiv_piP]
    exact Occ.piP_ext _ _ _ fun x => IPolyMap.equiv_map _ _

variable {P}

@[simp] theorem mem_piP [∀ h, IPolyIso (GP h) (ShP h) (PosP h) (pidxP h)] {X : J → Type u}
    (j : J) (y : X j) (k : ∀ h, GP h X) :
    Mem (fun X => ∀ h, GP h X) j y k ↔ ∃ h, Mem (GP h) j y (k h) :=
  ⟨fun ⟨q, e⟩ => ⟨q.1, q.2, e⟩, fun ⟨x, q, e⟩ => ⟨⟨x, q⟩, e⟩⟩

end Prop'

section Comp

variable {J : Type j} {K : Type k} {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'}
  {Pos' : Sh' → Type p'}

/-- A functor with an instance applied to a functor on families. -/
instance (priority := 1100) instCompC {G : Type u' → Type v} [hG : PolyIso G Sh Pos]
    {pidx' : (sh : Sh') → Pos' sh → J} {H : (J → Type u) → Type u'}
    [hH : IPolyIso H Sh' Pos' pidx'] :
    IPolyIso (fun X => G (H X)) (Σ sh, Pos sh → Sh') (fun z => Σ q, Pos' (z.2 q))
      (fun z r => pidx' (z.2 r.1) r.2) where
  equiv {X} := {
    toFun x := ⟨⟨(hG.equiv x).1, fun q => (hH.equiv ((hG.equiv x).2 q)).1⟩,
      fun r => (hH.equiv ((hG.equiv x).2 r.1)).2 r.2⟩
    invFun z := hG.equiv.symm ⟨z.1.1, fun q => hH.equiv.symm ⟨z.1.2 q, fun r => z.2 ⟨q, r⟩⟩⟩
    left_inv x := by
      show hG.equiv.symm ⟨(hG.equiv x).1, fun q => hH.equiv.symm (hH.equiv ((hG.equiv x).2 q))⟩ = x
      simp only [Equiv.symm_apply_apply]
      exact hG.equiv.symm_apply_apply x
    right_inv := fun ⟨⟨sh, t⟩, c⟩ => by
      dsimp only
      generalize e :
        hG.equiv (hG.equiv.symm ⟨sh, fun q => hH.equiv.symm ⟨t q, fun r => c ⟨q, r⟩⟩⟩) = U
      rw [Equiv.apply_symm_apply] at e
      subst e
      dsimp only at c
      refine Occ.comp_ext (Sh' := fun _ _ => Sh') (Pos' := fun _ _ s => Pos' s)
        (X := fun _ _ s r => X (pidx' s r)) sh _ t c fun q => ?_
      exact hH.equiv.apply_symm_apply _ }

theorem equiv_compC {G : Type u' → Type v} [hG : PolyIso G Sh Pos]
    {pidx' : (sh : Sh') → Pos' sh → J} {H : (J → Type u) → Type u'}
    [hH : IPolyIso H Sh' Pos' pidx'] {X : J → Type u} (x : G (H X)) :
    (instCompC (hG := hG) (hH := hH)).equiv x =
      ⟨⟨(hG.equiv x).1, fun q => (hH.equiv ((hG.equiv x).2 q)).1⟩,
        fun r => (hH.equiv ((hG.equiv x).2 r.1)).2 r.2⟩ :=
  rfl

instance {G : Type u' → Type v} {G' : Type v'' → Type w} [hG : PolyIso G Sh Pos]
    [hG' : PolyIso G' Sh Pos] [mG : PolyMap G G'] {pidx' : (sh : Sh') → Pos' sh → J}
    {H : (J → Type u) → Type u'} {H' : (J → Type u'') → Type v''} [hH : IPolyIso H Sh' Pos' pidx']
    [hH' : IPolyIso H' Sh' Pos' pidx'] [mH : IPolyMap H H'] :
    IPolyMap (fun X => G (H X)) (fun X => G' (H' X)) where
  map f x := PolyMap.map (self := mG) Pos (IPolyMap.map (self := mH) pidx' f) x
  equiv_map {X Y} f x := by
    rw [equiv_compC, equiv_compC]
    generalize e :
      hG'.equiv (PolyMap.map (self := mG) Pos (IPolyMap.map (self := mH) pidx' f) x) = z
    rw [PolyMap.equiv_map] at e
    subst e
    exact Occ.comp_ext (Sh' := fun _ _ => Sh') (Pos' := fun _ _ s => Pos' s)
      (X := fun _ _ s r => Y (pidx' s r)) _ _ _ _ fun q => IPolyMap.equiv_map _ _

/-- A functor on families over `K`, at a family reindexed along `g : K → J`. -/
instance (priority := 1200) instReidx {pidx : (sh : Sh) → Pos sh → K}
    {G : (K → Type u) → Type v} [h : IPolyIso G Sh Pos pidx] (g : K → J) :
    IPolyIso (fun X : J → Type u => G fun k => X (g k)) Sh Pos (fun sh q => g (pidx sh q)) :=
  ⟨h.equiv⟩

/-- A functor on families over `K` applied to a family of functors on families over `J`. -/
instance (priority := 1100) instCompI {pidx : (sh : Sh) → Pos sh → K}
    {G : (K → Type u') → Type v} [hG : IPolyIso G Sh Pos pidx] {Sh' : K → Type s'}
    {Pos' : ∀ k, Sh' k → Type p'} {pidx' : ∀ k (sh : Sh' k), Pos' k sh → J}
    {H : K → (J → Type u) → Type u'} [hH : ∀ k, IPolyIso (H k) (Sh' k) (Pos' k) (pidx' k)] :
    IPolyIso (fun X => G fun k => H k X) (Σ sh, (q : Pos sh) → Sh' (pidx sh q))
      (fun z => Σ q, Pos' _ (z.2 q)) (fun z r => pidx' _ (z.2 r.1) r.2) where
  equiv {X} := {
    toFun x := ⟨⟨(hG.equiv x).1, fun q => ((hH _).equiv ((hG.equiv x).2 q)).1⟩,
      fun r => ((hH _).equiv ((hG.equiv x).2 r.1)).2 r.2⟩
    invFun z := hG.equiv.symm ⟨z.1.1, fun q => (hH _).equiv.symm ⟨z.1.2 q, fun r => z.2 ⟨q, r⟩⟩⟩
    left_inv x := by
      show hG.equiv.symm ⟨(hG.equiv x).1,
        fun q => (hH _).equiv.symm ((hH _).equiv ((hG.equiv x).2 q))⟩ = x
      simp only [Equiv.symm_apply_apply]
      exact hG.equiv.symm_apply_apply x
    right_inv := fun ⟨⟨sh, t⟩, c⟩ => by
      dsimp only
      generalize e : hG.equiv (X := fun k => H k X)
        (hG.equiv.symm ⟨sh, fun q => (hH _).equiv.symm ⟨t q, fun r => c ⟨q, r⟩⟩⟩) = U
      rw [Equiv.apply_symm_apply] at e
      subst e
      dsimp only at c
      refine Occ.comp_ext (Sh' := fun sh q => Sh' (pidx sh q))
        (Pos' := fun sh q s => Pos' (pidx sh q) s)
        (X := fun sh q s r => X (pidx' (pidx sh q) s r)) sh _ t c fun q => ?_
      exact (hH _).equiv.apply_symm_apply _ }

@[simp] theorem mem_compC {G : Type u' → Type v} [PolyIso G Sh Pos]
    {pidx' : (sh : Sh') → Pos' sh → J} {H : (J → Type u) → Type u'} [IPolyIso H Sh' Pos' pidx']
    {X : J → Type u} (j : J) (x : X j) (c : G (H X)) :
    Mem (fun X => G (H X)) j x c ↔ ∃ y, PolyIso.Mem G y c ∧ Mem H j x y := by
  constructor
  · rintro ⟨r, e⟩
    exact ⟨_, ⟨r.1, rfl⟩, r.2, e⟩
  · rintro ⟨_, ⟨q, rfl⟩, r, e⟩
    exact ⟨⟨q, r⟩, e⟩

/-- Through a functor on families at a reindexed family: a member of the functor's value, at its
index read along the reindexing. -/
@[simp] theorem mem_reidx {pidx : (sh : Sh) → Pos sh → K} {G : (K → Type u) → Type v}
    [IPolyIso G Sh Pos pidx] (g : K → J) {X : J → Type u} (j : J) (x : X j)
    (c : G fun k => X (g k)) :
    Mem (fun X : J → Type u => G fun k => X (g k)) j x c ↔
      ∃ k y, Mem G (X := fun k => X (g k)) k y c ∧ (⟨g k, y⟩ : Σ j, X j) = ⟨j, x⟩ := by
  constructor
  · rintro ⟨q, e⟩
    exact ⟨_, _, ⟨q, rfl⟩, e⟩
  · rintro ⟨k, y, ⟨q, e⟩, e'⟩
    cases e
    exact ⟨q, e'⟩

/-- Through a functor on families applied to a family of functors on families: a member of a
member. For a family of functors with one presentation, so that `simp` finds the presentation of
the composite from that of the instance. -/
@[simp] theorem mem_compI {pidx : (sh : Sh) → Pos sh → K} {G : (K → Type u') → Type v}
    [IPolyIso G Sh Pos pidx] {Sh' : Type s'} {Pos' : Sh' → Type p'}
    {pidx' : ∀ k (sh : Sh'), Pos' sh → J} {H : K → (J → Type u) → Type u'}
    [∀ k, IPolyIso (H k) Sh' Pos' (pidx' k)] {X : J → Type u} (j : J) (x : X j)
    (c : G fun k => H k X) :
    Mem (fun X => G fun k => H k X) j x c ↔
      ∃ k y, Mem G (X := fun k => H k X) k y c ∧ Mem (H k) j x y := by
  constructor
  · rintro ⟨r, e⟩
    exact ⟨_, _, ⟨r.1, rfl⟩, r.2, e⟩
  · rintro ⟨k, y, ⟨q, e⟩, r, e'⟩
    cases e
    exact ⟨⟨q, r⟩, e'⟩

end Comp

end IPolyIso

namespace PolyIso

variable {J : Type j} {Sh : Type s} {Pos : Sh → Type p} {pidx : (sh : Sh) → Pos sh → J}

/-- A functor on families at a constant family. -/
instance (priority := 1200) instOfI {G : (J → Type u) → Type v} [h : IPolyIso G Sh Pos pidx] :
    PolyIso (fun X : Type u => G fun _ => X) Sh Pos :=
  ⟨h.equiv⟩

/-- A functor on families applied to a family of functors with instances. -/
instance (priority := 1100) instCompI {G : (J → Type u') → Type v} [hG : IPolyIso G Sh Pos pidx]
    {Sh' : J → Type s'} {Pos' : ∀ j, Sh' j → Type p'} {H : J → Type u → Type u'}
    [hH : ∀ j, PolyIso (H j) (Sh' j) (Pos' j)] :
    PolyIso (fun X => G fun j => H j X) (Σ sh, (q : Pos sh) → Sh' (pidx sh q))
      (fun z => Σ q, Pos' _ (z.2 q)) where
  equiv {X} := {
    toFun x := ⟨⟨(hG.equiv x).1, fun q => ((hH _).equiv ((hG.equiv x).2 q)).1⟩,
      fun r => ((hH _).equiv ((hG.equiv x).2 r.1)).2 r.2⟩
    invFun z := hG.equiv.symm ⟨z.1.1, fun q => (hH _).equiv.symm ⟨z.1.2 q, fun r => z.2 ⟨q, r⟩⟩⟩
    left_inv x := by
      show hG.equiv.symm ⟨(hG.equiv x).1,
        fun q => (hH _).equiv.symm ((hH _).equiv ((hG.equiv x).2 q))⟩ = x
      simp only [Equiv.symm_apply_apply]
      exact hG.equiv.symm_apply_apply x
    right_inv := fun ⟨⟨sh, t⟩, c⟩ => by
      dsimp only
      generalize e : hG.equiv (X := fun k => H k X)
        (hG.equiv.symm ⟨sh, fun q => (hH _).equiv.symm ⟨t q, fun r => c ⟨q, r⟩⟩⟩) = U
      rw [Equiv.apply_symm_apply] at e
      subst e
      dsimp only at c
      refine Occ.comp_ext (Sh' := fun sh q => Sh' (pidx sh q))
        (Pos' := fun sh q s => Pos' (pidx sh q) s) (X := fun _ _ _ _ => X) sh _ t c fun q => ?_
      exact (hH _).equiv.apply_symm_apply _ }

/-- Through a functor on families at a constant family: a member at some index. -/
@[simp] theorem mem_ofI {G : (J → Type u) → Type v} [IPolyIso G Sh Pos pidx] {X : Type u} (x : X)
    (c : G fun _ => X) :
    Mem (fun X : Type u => G fun _ => X) x c ↔
      ∃ j, IPolyIso.Mem G (X := fun _ => X) j x c :=
  ⟨fun ⟨q, e⟩ => ⟨_, q, congrArg (Sigma.mk _) e⟩,
    fun ⟨_, q, e⟩ => ⟨q, eq_of_heq (Sigma.mk.inj e).2⟩⟩

/-- Through a functor on families applied to a family of functors with instances: a member of a
member. For a family of functors with one presentation, so that `simp` finds the presentation of
the composite from that of the instance. -/
@[simp] theorem mem_compI {G : (J → Type u') → Type v} [IPolyIso G Sh Pos pidx]
    {Sh' : Type s'} {Pos' : Sh' → Type p'} {H : J → Type u → Type u'}
    [∀ j, PolyIso (H j) Sh' Pos'] {X : Type u} (x : X) (c : G fun j => H j X) :
    Mem (fun X => G fun j => H j X) x c ↔
      ∃ j y, IPolyIso.Mem G (X := fun j => H j X) j y c ∧ Mem (H j) x y := by
  constructor
  · rintro ⟨r, e⟩
    exact ⟨_, _, ⟨r.1, rfl⟩, r.2, e⟩
  · rintro ⟨j, y, ⟨q, e⟩, r, e'⟩
    cases e
    exact ⟨⟨q, r⟩, e'⟩

end PolyIso

end Codata
