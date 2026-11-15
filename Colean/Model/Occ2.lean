import Colean.Model.Occ
import Colean.Model.Poly

/-!
# The model, nested occurrences: occurrence structures in two variables

*Spec.* Input: nothing but the syntax of an argument type with occurrences of a parameter `X`
and of the recursive variable `Y`, mirrored by the combinators. Output: for a type expression
`G X Y`, a structure `Occ₂ Sh PX PY G`, an equivalence `G X Y ≃ Lay PX PY X Y` with the layer of
`Model/Poly.lean`, its map in both variables, its laws, the computation of the map through the
combinators, the agreement of its map in `Y` with the map of the one-variable structure of
`G X` in `Y` (`AgreeY`), and its members in each variable (`MemX`, `MemY`) with their computation
through the combinators. Used by `deriveInstances` (`Gen/Derive.lean`), and by users to compute
the map and membership in its rules.

A declared type `T α` is presented as a polynomial functor in its parameter `α` through a layer
`Lay P B X Y`, with a position `P` for each content in `α` and a position `B` for each child.
A field `p : α × T α` is split into its components, each with positions of one kind. Under a
named type constructor or a function the split stops: `p : List (α × T α)` and
`k : Nat → α × T α` have positions of both kinds in one argument. Such a field is the layer of a
structure in two variables: the parameter `X` at the premise of the instance (`ofX`, from the
field's structure in it) and the recursion `Y` (`ofY`, from the nested argument's structure in
it), put together by products, sums, functions, dependent pairs and named type constructors in
one variable (`comp`).

The command's functor `T.F` maps such an argument by its structure in `Y` alone, with the
parameter constant (`Occ.comp list (Occ.prod (Occ.const α) Occ.hole)`). `AgreeY` says that the
map in `Y` of a structure in two variables is that map; it holds through every combinator, and
the command proves it for an argument by its lemmas, combinator by combinator.

The members of a value in `X` and in `Y` are the contents of its positions of each kind. The
command states them by the structures in each variable alone, read as instances, whose positions
are those of the structure in two variables by definition, except across a sum
(`p : List (α ⊕ T α)`): a shape of the sum is on one side, of a structure in one variable or of
the other. There the rules state membership by `MemX` and `MemY`, which `simp` computes through
the combinators. The indexed version, for families and blocks, is `Model/IOcc2.lean`.
-/

open Colean

universe u u' u'' w w' w'' v v' v'' s s' p p' q q' a r r' t t'

namespace Codata

/-- An occurrence structure in two variables: an equivalence `G X Y ≃ Lay PX PY X Y` for every
`X` and `Y`, a shape with its contents in `X` at the positions `PX` and in `Y` at the positions
`PY`, the shapes and positions independent of `X` and `Y`. -/
structure Occ₂ (Sh : Type s) (PX : Sh → Type p) (PY : Sh → Type q)
    (G : Type u → Type w → Type v) where
  equiv {X : Type u} {Y : Type w} : G X Y ≃ Lay PX PY X Y

namespace Occ₂

/-! ### The generic laws -/

section Laws

variable {Sh : Type s} {PX : Sh → Type p} {PY : Sh → Type q}
variable {G : Type u → Type w → Type v} (o : Occ₂ Sh PX PY G)
  {G' : Type u' → Type w' → Type v'} (o' : Occ₂ Sh PX PY G')
  {G'' : Type u'' → Type w'' → Type v''} (o'' : Occ₂ Sh PX PY G'')
variable {X : Type u} {Y : Type w} {X' : Type u'} {Y' : Type w'} {X'' : Type u''} {Y'' : Type w''}

/-- The layer of a value: its shape and its contents of both kinds. -/
def toC (x : G X Y) : Lay PX PY X Y := o.equiv x

/-- The value of a layer. -/
def ofC (z : Lay PX PY X Y) : G X Y := o.equiv.symm z

theorem ofC_toC (x : G X Y) : o.ofC (o.toC x) = x := o.equiv.symm_apply_apply x

theorem toC_ofC (z : Lay PX PY X Y) : o.toC (o.ofC z) = z := o.equiv.apply_symm_apply z

/-- `ofC_toC` with the layer written out, as it appears in a generated `ofC (toC a)`. -/
theorem ofC_toC' (x : G X Y) :
    o.ofC ⟨(o.toC x).1, fun q => (o.toC x).2.1 q, fun q => (o.toC x).2.2 q⟩ = x :=
  o.ofC_toC x

/-- The action on functions in both variables, between two structures with the same shapes and
positions. -/
def map (f : X → X') (g : Y → Y') (x : G X Y) : G' X' Y' :=
  o'.ofC ⟨(o.toC x).1, fun q => f ((o.toC x).2.1 q), fun q => g ((o.toC x).2.2 q)⟩

theorem map_id (x : G X Y) : map o o (fun x => x) (fun y => y) x = x := o.ofC_toC x

theorem map_ofC (f : X → X') (g : Y → Y') (sh : Sh) (c : PX sh → X) (d : PY sh → Y) :
    map o o' f g (o.ofC ⟨sh, c, d⟩) = o'.ofC ⟨sh, fun q => f (c q), fun q => g (d q)⟩ := by
  unfold map
  rw [toC_ofC]

/-- The layer of a mapped value: the same shape, the contents mapped. -/
theorem toC_map (f : X → X') (g : Y → Y') (x : G X Y) :
    o'.toC (map o o' f g x) =
      ⟨(o.toC x).1, fun q => f ((o.toC x).2.1 q), fun q => g ((o.toC x).2.2 q)⟩ := by
  unfold map
  rw [toC_ofC]

theorem map_map (f' : X' → X'') (g' : Y' → Y'') (f : X → X') (g : Y → Y') (x : G X Y) :
    map o' o'' f' g' (map o o' f g x) = map o o'' (fun x => f' (f x)) (fun y => g' (g y)) x := by
  unfold map
  rw [toC_ofC]

end Laws

/-! ### Extensionality of layers through functions and composites -/

section Ext

variable {X : Type u} {Y : Type w}

/-- Extensionality for the layers of a function: a family of layers is a shape function and two
contents functions. -/
theorem pi_ext {A : Type a} {ShA : A → Type s} {PXA : ∀ x, ShA x → Type p}
    {PYA : ∀ x, ShA x → Type q} (T : ∀ x, Lay (PXA x) (PYA x) X Y) (sh : ∀ x, ShA x)
    (c : (Σ x, PXA x (sh x)) → X) (d : (Σ x, PYA x (sh x)) → Y)
    (h : ∀ x, T x = ⟨sh x, fun q => c ⟨x, q⟩, fun q => d ⟨x, q⟩⟩) :
    (⟨fun x => (T x).1, fun q => (T q.1).2.1 q.2, fun q => (T q.1).2.2 q.2⟩ :
      Lay (fun sh : ∀ x, ShA x => Σ x, PXA x (sh x)) (fun sh => Σ x, PYA x (sh x)) X Y) =
      ⟨sh, c, d⟩ := by
  have : T = fun x => ⟨sh x, fun q => c ⟨x, q⟩, fun q => d ⟨x, q⟩⟩ := funext h
  subst this
  rfl

/-- The same over a proposition. -/
theorem piP_ext {P : Prop} {ShP : P → Type s} {PXP : ∀ h, ShP h → Type p}
    {PYP : ∀ h, ShP h → Type q} (T : ∀ h, Lay (PXP h) (PYP h) X Y) (sh : ∀ h, ShP h)
    (c : (Σ' h, PXP h (sh h)) → X) (d : (Σ' h, PYP h (sh h)) → Y)
    (h : ∀ h, T h = ⟨sh h, fun q => c ⟨h, q⟩, fun q => d ⟨h, q⟩⟩) :
    (⟨fun h => (T h).1, fun q => (T q.1).2.1 q.2, fun q => (T q.1).2.2 q.2⟩ :
      Lay (fun sh : ∀ h, ShP h => Σ' h, PXP h (sh h)) (fun sh => Σ' h, PYP h (sh h)) X Y) =
      ⟨sh, c, d⟩ := by
  have : T = fun h => ⟨sh h, fun q => c ⟨h, q⟩, fun q => d ⟨h, q⟩⟩ := funext h
  subst this
  rfl

/-- Extensionality for the layers of a composite: the inner layers at the positions of an outer
shape. -/
theorem comp_ext {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {PX' : Sh' → Type p'}
    {PY' : Sh' → Type q'} (sh : Sh) (T : Pos sh → Lay PX' PY' X Y) (t : Pos sh → Sh')
    (c : (Σ q, PX' (t q)) → X) (d : (Σ q, PY' (t q)) → Y)
    (h : ∀ q, T q = ⟨t q, fun r => c ⟨q, r⟩, fun r => d ⟨q, r⟩⟩) :
    (⟨⟨sh, fun q => (T q).1⟩, fun r => (T r.1).2.1 r.2, fun r => (T r.1).2.2 r.2⟩ :
      Lay (fun z : Σ sh, Pos sh → Sh' => Σ q, PX' (z.2 q)) (fun z => Σ q, PY' (z.2 q)) X Y) =
      ⟨⟨sh, t⟩, c, d⟩ := by
  have : T = fun q => ⟨t q, fun r => c ⟨q, r⟩, fun r => d ⟨q, r⟩⟩ := funext h
  subst this
  rfl

end Ext

/-! ### The combinators

As for `Occ`, every combinator is defined by its two maps directly, so that `toC`, `ofC` and
`map` compute through it by `rfl`. A part in one variable is a structure in it (`ofX`, `ofY`); the
occurrence of `Y` is `ofY Occ.hole`. -/

/-- A constant: the value is the shape, there are no positions. -/
def const (A : Type v) :
    Occ₂ A (fun _ => Empty) (fun _ => Empty) (fun (_ : Type u) (_ : Type w) => A) where
  equiv := {
    toFun x := ⟨x, Empty.elim, Empty.elim⟩
    invFun z := z.1
    left_inv _ := rfl
    right_inv := fun ⟨_, _, _⟩ =>
      congrArg _ (Prod.ext (funext fun x => x.elim) (funext fun x => x.elim)) }

/-- A part in `X` alone, with its structure in `X`: positions in `X` only. -/
def ofX {ShX : Type s} {PosX : ShX → Type p} {GX : Type u → Type v} (o : Occ ShX PosX GX) :
    Occ₂ ShX PosX (fun _ => Empty) (fun X (_ : Type w) => GX X) where
  equiv := {
    toFun x := ⟨(o.toC x).1, (o.toC x).2, Empty.elim⟩
    invFun z := o.ofC ⟨z.1, z.2.1⟩
    left_inv x := o.ofC_toC x
    right_inv := fun ⟨sh, c, _⟩ => by
      dsimp only
      generalize h : o.toC (o.ofC ⟨sh, c⟩) = z
      rw [Occ.toC_ofC] at h
      subst h
      exact congrArg (Sigma.mk sh) (Prod.ext rfl (funext fun x => x.elim)) }

/-- A part in `Y` alone, with its structure in `Y`: positions in `Y` only. -/
def ofY {ShY : Type s} {PosY : ShY → Type q} {GY : Type w → Type v} (o : Occ ShY PosY GY) :
    Occ₂ ShY (fun _ => Empty) PosY (fun (_ : Type u) Y => GY Y) where
  equiv := {
    toFun y := ⟨(o.toC y).1, Empty.elim, (o.toC y).2⟩
    invFun z := o.ofC ⟨z.1, z.2.2⟩
    left_inv y := o.ofC_toC y
    right_inv := fun ⟨sh, _, d⟩ => by
      dsimp only
      generalize h : o.toC (o.ofC ⟨sh, d⟩) = z
      rw [Occ.toC_ofC] at h
      subst h
      exact congrArg (Sigma.mk sh) (Prod.ext (funext fun x => x.elim) rfl) }

section Combinators

variable {Sh₁ : Type s} {PX₁ : Sh₁ → Type p} {PY₁ : Sh₁ → Type q}
  {Sh₂ : Type s'} {PX₂ : Sh₂ → Type p'} {PY₂ : Sh₂ → Type q'}
  {G₁ : Type u → Type w → Type v} {G₂ : Type u → Type w → Type v'}

/-- A product: a pair of shapes, the sums of the positions. -/
def prod (o₁ : Occ₂ Sh₁ PX₁ PY₁ G₁) (o₂ : Occ₂ Sh₂ PX₂ PY₂ G₂) :
    Occ₂ (Sh₁ × Sh₂) (fun sh => PX₁ sh.1 ⊕ PX₂ sh.2) (fun sh => PY₁ sh.1 ⊕ PY₂ sh.2)
      (fun X Y => G₁ X Y × G₂ X Y) where
  equiv := {
    toFun x := ⟨((o₁.toC x.1).1, (o₂.toC x.2).1),
      Occ.sumRec (o₁.toC x.1).2.1 (o₂.toC x.2).2.1, Occ.sumRec (o₁.toC x.1).2.2 (o₂.toC x.2).2.2⟩
    invFun z := (o₁.ofC ⟨z.1.1, fun q => z.2.1 (.inl q), fun q => z.2.2 (.inl q)⟩,
      o₂.ofC ⟨z.1.2, fun q => z.2.1 (.inr q), fun q => z.2.2 (.inr q)⟩)
    left_inv x := by
      show (o₁.ofC ⟨(o₁.toC x.1).1, fun q => (o₁.toC x.1).2.1 q, fun q => (o₁.toC x.1).2.2 q⟩,
        o₂.ofC ⟨(o₂.toC x.2).1, fun q => (o₂.toC x.2).2.1 q, fun q => (o₂.toC x.2).2.2 q⟩) = x
      rw [ofC_toC', ofC_toC']
    right_inv := fun ⟨⟨s₁, s₂⟩, c, d⟩ => by
      dsimp only
      generalize h₁ : o₁.toC (o₁.ofC ⟨s₁, fun q => c (.inl q), fun q => d (.inl q)⟩) = z₁
      generalize h₂ : o₂.toC (o₂.ofC ⟨s₂, fun q => c (.inr q), fun q => d (.inr q)⟩) = z₂
      rw [toC_ofC] at h₁ h₂
      subst h₁ h₂
      exact congrArg (Sigma.mk (s₁, s₂))
        (Prod.ext (funext fun q => by cases q <;> rfl) (funext fun q => by cases q <;> rfl)) }

/-- A sum: a shape of either side, its positions (lifted to one universe). -/
def sum (o₁ : Occ₂ Sh₁ PX₁ PY₁ G₁) (o₂ : Occ₂ Sh₂ PX₂ PY₂ G₂) :
    Occ₂ (Sh₁ ⊕ Sh₂) (Occ.SumPos PX₁ PX₂) (Occ.SumPos PY₁ PY₂) (fun X Y => G₁ X Y ⊕ G₂ X Y) where
  equiv := {
    toFun
      | .inl x => ⟨.inl (o₁.toC x).1, fun q => (o₁.toC x).2.1 q.down,
          fun q => (o₁.toC x).2.2 q.down⟩
      | .inr x => ⟨.inr (o₂.toC x).1, fun q => (o₂.toC x).2.1 q.down,
          fun q => (o₂.toC x).2.2 q.down⟩
    invFun
      | ⟨.inl sh, c, d⟩ => .inl (o₁.ofC ⟨sh, fun q => c ⟨q⟩, fun q => d ⟨q⟩⟩)
      | ⟨.inr sh, c, d⟩ => .inr (o₂.ofC ⟨sh, fun q => c ⟨q⟩, fun q => d ⟨q⟩⟩)
    left_inv
      | .inl x => by
        show Sum.inl (o₁.ofC ⟨(o₁.toC x).1, fun q => (o₁.toC x).2.1 q,
          fun q => (o₁.toC x).2.2 q⟩) = _
        rw [ofC_toC']
      | .inr x => by
        show Sum.inr (o₂.ofC ⟨(o₂.toC x).1, fun q => (o₂.toC x).2.1 q,
          fun q => (o₂.toC x).2.2 q⟩) = _
        rw [ofC_toC']
    right_inv
      | ⟨.inl sh, c, d⟩ => by
        dsimp only
        generalize h : o₁.toC (o₁.ofC ⟨sh, fun q => c ⟨q⟩, fun q => d ⟨q⟩⟩) = z
        rw [toC_ofC] at h
        subst h
        rfl
      | ⟨.inr sh, c, d⟩ => by
        dsimp only
        generalize h : o₂.toC (o₂.ofC ⟨sh, fun q => c ⟨q⟩, fun q => d ⟨q⟩⟩) = z
        rw [toC_ofC] at h
        subst h
        rfl }

end Combinators

section Dependent

variable (A : Type a) {ShA : A → Type s} {PXA : ∀ x, ShA x → Type p}
  {PYA : ∀ x, ShA x → Type q} {GA : A → Type u → Type w → Type v}

/-- A function from a constant type: a shape at every point, a point with a position there. -/
def pi (o : ∀ x, Occ₂ (ShA x) (PXA x) (PYA x) (GA x)) :
    Occ₂ (∀ x : A, ShA x) (fun sh => Σ x, PXA x (sh x)) (fun sh => Σ x, PYA x (sh x))
      (fun X Y => ∀ x, GA x X Y) where
  equiv := {
    toFun k := ⟨fun x => ((o x).toC (k x)).1, fun q => ((o q.1).toC (k q.1)).2.1 q.2,
      fun q => ((o q.1).toC (k q.1)).2.2 q.2⟩
    invFun z x := (o x).ofC ⟨z.1 x, fun q => z.2.1 ⟨x, q⟩, fun q => z.2.2 ⟨x, q⟩⟩
    left_inv k := funext fun x => (o x).ofC_toC' (k x)
    right_inv := fun ⟨sh, c, d⟩ => pi_ext _ sh c d fun x => (o x).toC_ofC _ }

/-- A dependent pair over a constant type: a point with a shape there, its positions. -/
def sigma (o : ∀ x, Occ₂ (ShA x) (PXA x) (PYA x) (GA x)) :
    Occ₂ (Σ x : A, ShA x) (fun sh => PXA sh.1 sh.2) (fun sh => PYA sh.1 sh.2)
      (fun X Y => Σ x, GA x X Y) where
  equiv := {
    toFun z := ⟨⟨z.1, ((o z.1).toC z.2).1⟩, ((o z.1).toC z.2).2.1, ((o z.1).toC z.2).2.2⟩
    invFun w := ⟨w.1.1, (o w.1.1).ofC ⟨w.1.2, w.2.1, w.2.2⟩⟩
    left_inv := fun ⟨x, y⟩ => by
      show (⟨x, (o x).ofC ((o x).toC y)⟩ : Σ x, GA x _ _) = _
      rw [ofC_toC]
    right_inv := fun ⟨⟨x, sh⟩, c, d⟩ => by
      dsimp only
      generalize h : (o x).toC ((o x).ofC ⟨sh, c, d⟩) = z
      rw [toC_ofC] at h
      subst h
      rfl }

end Dependent

section Prop'

variable (P : Prop) {ShP : P → Type s} {PXP : ∀ h, ShP h → Type p}
  {PYP : ∀ h, ShP h → Type q} {GP : P → Type u → Type w → Type v}

/-- A function from a proposition. -/
def piP (o : ∀ h, Occ₂ (ShP h) (PXP h) (PYP h) (GP h)) :
    Occ₂ (∀ h : P, ShP h) (fun sh => Σ' h, PXP h (sh h)) (fun sh => Σ' h, PYP h (sh h))
      (fun X Y => ∀ h, GP h X Y) where
  equiv := {
    toFun k := ⟨fun h => ((o h).toC (k h)).1, fun q => ((o q.1).toC (k q.1)).2.1 q.2,
      fun q => ((o q.1).toC (k q.1)).2.2 q.2⟩
    invFun z h := (o h).ofC ⟨z.1 h, fun q => z.2.1 ⟨h, q⟩, fun q => z.2.2 ⟨h, q⟩⟩
    left_inv k := funext fun h => (o h).ofC_toC' (k h)
    right_inv := fun ⟨sh, c, d⟩ => piP_ext _ sh c d fun h => (o h).toC_ofC _ }

end Prop'

section Comp

variable {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {PX' : Sh' → Type p'}
  {PY' : Sh' → Type q'}

/-- A named type constructor in one variable applied to an expression in two: the shapes are a
shape of the outer structure with a shape of the inner one at each of its positions, the
positions of each kind a position of the outer with a position of that kind of the inner shape
there. -/
def comp {G : Type w' → Type v} (oG : Occ Sh Pos G) {H : Type u → Type w → Type w'}
    (oH : Occ₂ Sh' PX' PY' H) :
    Occ₂ (Σ sh, Pos sh → Sh') (fun z => Σ q, PX' (z.2 q)) (fun z => Σ q, PY' (z.2 q))
      (fun X Y => G (H X Y)) where
  equiv {X Y} := {
    toFun x := ⟨⟨(oG.toC x).1, fun q => (oH.toC ((oG.toC x).2 q)).1⟩,
      fun r => (oH.toC ((oG.toC x).2 r.1)).2.1 r.2, fun r => (oH.toC ((oG.toC x).2 r.1)).2.2 r.2⟩
    invFun z := oG.ofC ⟨z.1.1, fun q => oH.ofC ⟨z.1.2 q, fun r => z.2.1 ⟨q, r⟩,
      fun r => z.2.2 ⟨q, r⟩⟩⟩
    left_inv x := by
      show oG.ofC ⟨(oG.toC x).1, fun q => oH.ofC ⟨(oH.toC ((oG.toC x).2 q)).1,
        fun r => (oH.toC ((oG.toC x).2 q)).2.1 r, fun r => (oH.toC ((oG.toC x).2 q)).2.2 r⟩⟩ = x
      simp only [ofC_toC', Occ.ofC_toC']
    right_inv := fun ⟨⟨sh, t⟩, c, d⟩ => by
      dsimp only
      generalize hU : oG.toC (oG.ofC ⟨sh, fun q => oH.ofC ⟨t q, fun r => c ⟨q, r⟩,
        fun r => d ⟨q, r⟩⟩⟩) = U
      rw [Occ.toC_ofC] at hU
      subst hU
      exact comp_ext sh _ t c d fun q => oH.toC_ofC _ }

end Comp

/-! ### The computation of `map` through the combinators -/

section Compute

variable {X : Type u} {Y : Type w} {X' : Type u'} {Y' : Type w'}

@[simp] theorem map_const {A : Type v} (f : X → X') (g : Y → Y') (x : A) :
    map (const A) (const A) f g x = x := rfl

/-- The map of a part in `X` alone is the map of its structure. -/
@[simp] theorem map_ofX {ShX : Type s} {PosX : ShX → Type p} {GX : Type u → Type v}
    {GX' : Type u' → Type v'} (o : Occ ShX PosX GX) (o' : Occ ShX PosX GX') (f : X → X')
    (g : Y → Y') (x : GX X) : map (ofX o) (ofX o') f g x = Occ.map o o' f x := rfl

/-- The map of a part in `Y` alone is the map of its structure. -/
@[simp] theorem map_ofY {ShY : Type s} {PosY : ShY → Type q} {GY : Type w → Type v}
    {GY' : Type w' → Type v'} (o : Occ ShY PosY GY) (o' : Occ ShY PosY GY') (f : X → X')
    (g : Y → Y') (y : GY Y) : map (ofY o) (ofY o') f g y = Occ.map o o' g y := rfl

variable {Sh₁ : Type s} {PX₁ : Sh₁ → Type p} {PY₁ : Sh₁ → Type q}
  {Sh₂ : Type s'} {PX₂ : Sh₂ → Type p'} {PY₂ : Sh₂ → Type q'}
  {G₁ : Type u → Type w → Type v} {G₂ : Type u → Type w → Type v'}
  {G₁' : Type u' → Type w' → Type v''} {G₂' : Type u' → Type w' → Type w''}
  (o₁ : Occ₂ Sh₁ PX₁ PY₁ G₁) (o₂ : Occ₂ Sh₂ PX₂ PY₂ G₂)
  (o₁' : Occ₂ Sh₁ PX₁ PY₁ G₁') (o₂' : Occ₂ Sh₂ PX₂ PY₂ G₂')

@[simp] theorem map_prod (f : X → X') (g : Y → Y') (x : G₁ X Y × G₂ X Y) :
    map (prod o₁ o₂) (prod o₁' o₂') f g x = (map o₁ o₁' f g x.1, map o₂ o₂' f g x.2) := rfl

@[simp] theorem map_sum_inl (f : X → X') (g : Y → Y') (x : G₁ X Y) :
    map (sum o₁ o₂) (sum o₁' o₂') f g (.inl x) = .inl (map o₁ o₁' f g x) := rfl

@[simp] theorem map_sum_inr (f : X → X') (g : Y → Y') (x : G₂ X Y) :
    map (sum o₁ o₂) (sum o₁' o₂') f g (.inr x) = .inr (map o₂ o₂' f g x) := rfl

end Compute

section ComputeDep

variable {X : Type u} {Y : Type w} {X' : Type u'} {Y' : Type w'}
variable {A : Type a} {ShA : A → Type s} {PXA : ∀ x, ShA x → Type p}
  {PYA : ∀ x, ShA x → Type q} {GA : A → Type u → Type w → Type v}
  {GA' : A → Type u' → Type w' → Type v'}
  (o : ∀ x, Occ₂ (ShA x) (PXA x) (PYA x) (GA x)) (o' : ∀ x, Occ₂ (ShA x) (PXA x) (PYA x) (GA' x))

@[simp] theorem map_pi (f : X → X') (g : Y → Y') (k : ∀ x, GA x X Y) :
    map (pi A o) (pi A o') f g k = fun x => map (o x) (o' x) f g (k x) := rfl

@[simp] theorem map_sigma (f : X → X') (g : Y → Y') (z : Σ x, GA x X Y) :
    map (sigma A o) (sigma A o') f g z = ⟨z.1, map (o z.1) (o' z.1) f g z.2⟩ := rfl

@[simp] theorem map_piP {P : Prop} {ShP : P → Type s} {PXP : ∀ h, ShP h → Type p}
    {PYP : ∀ h, ShP h → Type q} {GP : P → Type u → Type w → Type v}
    {GP' : P → Type u' → Type w' → Type v'} (o : ∀ h, Occ₂ (ShP h) (PXP h) (PYP h) (GP h))
    (o' : ∀ h, Occ₂ (ShP h) (PXP h) (PYP h) (GP' h)) (f : X → X') (g : Y → Y')
    (k : ∀ h, GP h X Y) : map (piP P o) (piP P o') f g k = fun h => map (o h) (o' h) f g (k h) :=
  rfl

end ComputeDep

section ComputeComp

variable {X : Type u} {Y : Type w} {X' : Type u'} {Y' : Type w'}
variable {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {PX' : Sh' → Type p'}
  {PY' : Sh' → Type q'} {G : Type w'' → Type v} {G' : Type u'' → Type v'}
  {H : Type u → Type w → Type w''} {H' : Type u' → Type w' → Type u''}
  (oG : Occ Sh Pos G) (oG' : Occ Sh Pos G') (oH : Occ₂ Sh' PX' PY' H) (oH' : Occ₂ Sh' PX' PY' H')

/-- The map through a composite is the map of the map. -/
@[simp] theorem map_comp (f : X → X') (g : Y → Y') (x : G (H X Y)) :
    map (comp oG oH) (comp oG' oH') f g x = Occ.map oG oG' (map oH oH' f g) x := rfl

end ComputeComp

/-! ### The map in `Y` is the map of the structure in `Y` alone

The command's functor maps an argument with a structure in two variables by its structure in `Y`
alone, the parameter `X` constant (`Occ.const (GX X)` where the structure in two variables has
`ofX`, the same structure where it has `ofY`). `AgreeY o o' X oY oY'` says that the two maps are
the same; it holds through every combinator (`AgreeY.prod`, …), and `AgreeY.map_ofC` is how the
command uses it. -/

section Agree

variable {Sh : Type s} {PX : Sh → Type p} {PY : Sh → Type q}
  {G : Type u → Type w → Type v} {G' : Type u → Type w' → Type v'}
  {ShY : Type r} {PosY : ShY → Type t}

/-- The map in `Y` of `o`, `o'` at `X` is the map of `oY`, `oY'`, structures of `G X` in `Y`
alone. -/
def AgreeY (o : Occ₂ Sh PX PY G) (o' : Occ₂ Sh PX PY G') (X : Type u)
    (oY : Occ ShY PosY (G X)) (oY' : Occ ShY PosY (G' X)) : Prop :=
  ∀ {Y : Type w} {Y' : Type w'} (g : Y → Y') (y : G X Y),
    Occ.map oY oY' g y = map o o' (fun x => x) g y

/-- The command's functor applied to a value with a given layer: the layer with its contents in
`Y` mapped. -/
theorem AgreeY.map_ofC {o : Occ₂ Sh PX PY G} {o' : Occ₂ Sh PX PY G'} {X : Type u}
    {oY : Occ ShY PosY (G X)} {oY' : Occ ShY PosY (G' X)} (h : AgreeY o o' X oY oY')
    {Y : Type w} {Y' : Type w'} (g : Y → Y') (sh : Sh) (c : PX sh → X) (d : PY sh → Y) :
    Occ.map oY oY' g (o.ofC ⟨sh, c, d⟩) = o'.ofC ⟨sh, c, fun q => g (d q)⟩ := by
  rw [h, Occ₂.map_ofC]

end Agree

namespace AgreeY

variable {X : Type u}

theorem const (A : Type v) : AgreeY (const A) (const A) X (Occ.const A) (Occ.const A) :=
  fun _ _ => rfl

theorem ofX {ShX : Type s} {PosX : ShX → Type p} {GX : Type u → Type v}
    (oX : Occ ShX PosX GX) :
    AgreeY (ofX oX) (ofX oX) X (Occ.const (GX X)) (Occ.const (GX X)) :=
  fun _ y => (oX.ofC_toC' y).symm

theorem ofY {ShY : Type s} {PosY : ShY → Type q} {GY : Type w → Type v}
    {GY' : Type w' → Type v'} (oY : Occ ShY PosY GY) (oY' : Occ ShY PosY GY') :
    AgreeY (ofY oY) (ofY oY') X oY oY' :=
  fun _ _ => rfl

section Combinators

variable {Sh₁ : Type s} {PX₁ : Sh₁ → Type p} {PY₁ : Sh₁ → Type q}
  {Sh₂ : Type s'} {PX₂ : Sh₂ → Type p'} {PY₂ : Sh₂ → Type q'}
  {G₁ : Type u → Type w → Type v} {G₂ : Type u → Type w → Type v'}
  {G₁' : Type u → Type w' → Type v''} {G₂' : Type u → Type w' → Type w''}
  {o₁ : Occ₂ Sh₁ PX₁ PY₁ G₁} {o₂ : Occ₂ Sh₂ PX₂ PY₂ G₂}
  {o₁' : Occ₂ Sh₁ PX₁ PY₁ G₁'} {o₂' : Occ₂ Sh₂ PX₂ PY₂ G₂'}
  {ShY₁ : Type r} {PosY₁ : ShY₁ → Type t} {ShY₂ : Type r'} {PosY₂ : ShY₂ → Type t'}
  {oY₁ : Occ ShY₁ PosY₁ (G₁ X)} {oY₂ : Occ ShY₂ PosY₂ (G₂ X)}
  {oY₁' : Occ ShY₁ PosY₁ (G₁' X)} {oY₂' : Occ ShY₂ PosY₂ (G₂' X)}

theorem prod (h₁ : AgreeY o₁ o₁' X oY₁ oY₁') (h₂ : AgreeY o₂ o₂' X oY₂ oY₂') :
    AgreeY (Occ₂.prod o₁ o₂) (Occ₂.prod o₁' o₂') X (Occ.prod oY₁ oY₂) (Occ.prod oY₁' oY₂') :=
  fun g y => Prod.ext (h₁ g y.1) (h₂ g y.2)

theorem sum (h₁ : AgreeY o₁ o₁' X oY₁ oY₁') (h₂ : AgreeY o₂ o₂' X oY₂ oY₂') :
    AgreeY (Occ₂.sum o₁ o₂) (Occ₂.sum o₁' o₂') X (Occ.sum oY₁ oY₂) (Occ.sum oY₁' oY₂')
  | _, _, g, .inl y => congrArg Sum.inl (h₁ g y)
  | _, _, g, .inr y => congrArg Sum.inr (h₂ g y)

end Combinators

section Dependent

variable {A : Type a} {ShA : A → Type s} {PXA : ∀ x, ShA x → Type p}
  {PYA : ∀ x, ShA x → Type q} {GA : A → Type u → Type w → Type v}
  {GA' : A → Type u → Type w' → Type v'} {o : ∀ x, Occ₂ (ShA x) (PXA x) (PYA x) (GA x)}
  {o' : ∀ x, Occ₂ (ShA x) (PXA x) (PYA x) (GA' x)} {ShYA : A → Type r}
  {PosYA : ∀ x, ShYA x → Type t} {oY : ∀ x, Occ (ShYA x) (PosYA x) (GA x X)}
  {oY' : ∀ x, Occ (ShYA x) (PosYA x) (GA' x X)}

theorem pi (h : ∀ x, AgreeY (o x) (o' x) X (oY x) (oY' x)) :
    AgreeY (Occ₂.pi A o) (Occ₂.pi A o') X (Occ.pi A oY) (Occ.pi A oY') :=
  fun g k => funext fun x => h x g (k x)

theorem sigma (h : ∀ x, AgreeY (o x) (o' x) X (oY x) (oY' x)) :
    AgreeY (Occ₂.sigma A o) (Occ₂.sigma A o') X (Occ.sigma A oY) (Occ.sigma A oY') :=
  fun g z => congrArg (Sigma.mk z.1) (h z.1 g z.2)

end Dependent

theorem piP {P : Prop} {ShP : P → Type s} {PXP : ∀ h, ShP h → Type p}
    {PYP : ∀ h, ShP h → Type q} {GP : P → Type u → Type w → Type v}
    {GP' : P → Type u → Type w' → Type v'} {o : ∀ h, Occ₂ (ShP h) (PXP h) (PYP h) (GP h)}
    {o' : ∀ h, Occ₂ (ShP h) (PXP h) (PYP h) (GP' h)} {ShYP : P → Type r}
    {PosYP : ∀ h, ShYP h → Type t} {oY : ∀ h, Occ (ShYP h) (PosYP h) (GP h X)}
    {oY' : ∀ h, Occ (ShYP h) (PosYP h) (GP' h X)} (h : ∀ h, AgreeY (o h) (o' h) X (oY h) (oY' h)) :
    AgreeY (Occ₂.piP P o) (Occ₂.piP P o') X (Occ.piP P oY) (Occ.piP P oY') :=
  fun g k => funext fun h' => h h' g (k h')

theorem comp {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {PX' : Sh' → Type p'}
    {PY' : Sh' → Type q'} {G : Type w'' → Type v} {G' : Type u'' → Type v'}
    {H : Type u → Type w → Type w''} {H' : Type u → Type w' → Type u''} (oG : Occ Sh Pos G)
    (oG' : Occ Sh Pos G') {oH : Occ₂ Sh' PX' PY' H} {oH' : Occ₂ Sh' PX' PY' H'}
    {ShY : Type r} {PosY : ShY → Type t} {oY : Occ ShY PosY (H X)} {oY' : Occ ShY PosY (H' X)}
    (h : AgreeY oH oH' X oY oY') :
    AgreeY (Occ₂.comp oG oH) (Occ₂.comp oG' oH') X (Occ.comp oG oY) (Occ.comp oG' oY') :=
  fun g x => congrArg (fun k => Occ.map oG oG' k x) (funext fun y => h g y)

end AgreeY

/-! ### Membership

The members of a value in each variable are the contents of its positions of that kind, defined
from the presentation as `PolyIso.Mem` is (`MemX`, `MemY`). `simp` computes them through the
combinators, down to the parts in one variable, whose members are those of their structure in
that variable (`Occ.Mem`, `memX_ofX`, `memY_ofY`), which `simp` computes through its combinators
down to the leaves, where they are those of the instance (`Occ.mem_ofIso`). A sum is gone through
for any value (`memX_sum`), so that the members through a sum inside a list are computed
(`List (α ⊕ T α)`). -/

section Mem

variable {Sh : Type s} {PX : Sh → Type p} {PY : Sh → Type q} {G : Type u → Type w → Type v}
  {X : Type u} {Y : Type w}

/-- `x` is a member of `y` in `X`: some position of `y` in `X` holds `x`. -/
def MemX (o : Occ₂ Sh PX PY G) (x : X) (y : G X Y) : Prop :=
  ∃ q, (o.toC y).2.1 q = x

/-- `t` is a member of `y` in `Y`: some position of `y` in `Y` holds `t`. -/
def MemY (o : Occ₂ Sh PX PY G) (t : Y) (y : G X Y) : Prop :=
  ∃ q, (o.toC y).2.2 q = t

theorem memX_iff (o : Occ₂ Sh PX PY G) {x : X} {y : G X Y} :
    MemX o x y ↔ ∃ q, (o.toC y).2.1 q = x := Iff.rfl

theorem memY_iff (o : Occ₂ Sh PX PY G) {t : Y} {y : G X Y} :
    MemY o t y ↔ ∃ q, (o.toC y).2.2 q = t := Iff.rfl

/-- A property of every member in `X` is one of the content of every position in `X`. -/
theorem forall_memX_iff (o : Occ₂ Sh PX PY G) {P : X → Prop} {y : G X Y} :
    (∀ x, MemX o x y → P x) ↔ ∀ q, P ((o.toC y).2.1 q) :=
  ⟨fun H q => H _ ⟨q, rfl⟩, fun H _ ⟨q, e⟩ => e ▸ H q⟩

/-- A property of every member in `Y` is one of the content of every position in `Y`. -/
theorem forall_memY_iff (o : Occ₂ Sh PX PY G) {P : Y → Prop} {y : G X Y} :
    (∀ t, MemY o t y → P t) ↔ ∀ q, P ((o.toC y).2.2 q) :=
  ⟨fun H q => H _ ⟨q, rfl⟩, fun H _ ⟨q, e⟩ => e ▸ H q⟩

end Mem

section MemCompute

variable {X : Type u} {Y : Type w}

@[simp] theorem not_memX_const (A : Type v) (x : X) (a : A) :
    ¬ MemX (const A) (Y := Y) x a :=
  fun ⟨q, _⟩ => q.elim

@[simp] theorem not_memY_const (A : Type v) (t : Y) (a : A) :
    ¬ MemY (const A) (X := X) t a :=
  fun ⟨q, _⟩ => q.elim

@[simp] theorem not_memX_ofY {ShY : Type s} {PosY : ShY → Type q} {GY : Type w → Type v}
    (o : Occ ShY PosY GY) (x : X) (y : GY Y) : ¬ MemX (ofY o) x y :=
  fun ⟨q, _⟩ => q.elim

@[simp] theorem not_memY_ofX {ShX : Type s} {PosX : ShX → Type p} {GX : Type u → Type v}
    (o : Occ ShX PosX GX) (t : Y) (y : GX X) : ¬ MemY (ofX o) t y :=
  fun ⟨q, _⟩ => q.elim

/-- The members of a part in `Y` alone are those of its structure (`Occ.Mem`). -/
@[simp] theorem memY_ofY {ShY : Type s} {PosY : ShY → Type q} {GY : Type w → Type v}
    (o : Occ ShY PosY GY) (t : Y) (y : GY Y) : MemY (X := X) (ofY o) t y ↔ Occ.Mem o t y :=
  Iff.rfl

/-- The members of a part in `X` alone are those of its structure (`Occ.Mem`), which `simp`
computes through its combinators down to the leaves (`Occ.mem_ofIso`). -/
@[simp] theorem memX_ofX {ShX : Type s} {PosX : ShX → Type p} {GX : Type u → Type v}
    (o : Occ ShX PosX GX) (x : X) (y : GX X) : MemX (Y := Y) (ofX o) x y ↔ Occ.Mem o x y :=
  Iff.rfl

/-! The members through the combinators in two variables. -/

section Forms

variable {Sh₁ : Type s} {PX₁ : Sh₁ → Type p} {PY₁ : Sh₁ → Type q}
  {Sh₂ : Type s'} {PX₂ : Sh₂ → Type p'} {PY₂ : Sh₂ → Type q'}
  {G₁ : Type u → Type w → Type v} {G₂ : Type u → Type w → Type v'}
  (o₁ : Occ₂ Sh₁ PX₁ PY₁ G₁) (o₂ : Occ₂ Sh₂ PX₂ PY₂ G₂)

@[simp] theorem memX_prod (x : X) (y : G₁ X Y × G₂ X Y) :
    MemX (prod o₁ o₂) x y ↔ MemX o₁ x y.1 ∨ MemX o₂ x y.2 :=
  ⟨fun ⟨q, e⟩ => match q, e with
    | .inl q, e => .inl ⟨q, e⟩
    | .inr q, e => .inr ⟨q, e⟩,
    fun h => h.elim (fun ⟨q, e⟩ => ⟨.inl q, e⟩) (fun ⟨q, e⟩ => ⟨.inr q, e⟩)⟩

@[simp] theorem memY_prod (t : Y) (y : G₁ X Y × G₂ X Y) :
    MemY (prod o₁ o₂) t y ↔ MemY o₁ t y.1 ∨ MemY o₂ t y.2 :=
  ⟨fun ⟨q, e⟩ => match q, e with
    | .inl q, e => .inl ⟨q, e⟩
    | .inr q, e => .inr ⟨q, e⟩,
    fun h => h.elim (fun ⟨q, e⟩ => ⟨.inl q, e⟩) (fun ⟨q, e⟩ => ⟨.inr q, e⟩)⟩

@[simp] theorem memX_sum_inl (x : X) (y : G₁ X Y) :
    MemX (sum o₁ o₂) x (.inl y) ↔ MemX o₁ x y :=
  ⟨fun ⟨q, e⟩ => ⟨q.down, e⟩, fun ⟨q, e⟩ => ⟨⟨q⟩, e⟩⟩

@[simp] theorem memX_sum_inr (x : X) (y : G₂ X Y) :
    MemX (sum o₁ o₂) x (.inr y) ↔ MemX o₂ x y :=
  ⟨fun ⟨q, e⟩ => ⟨q.down, e⟩, fun ⟨q, e⟩ => ⟨⟨q⟩, e⟩⟩

@[simp] theorem memY_sum_inl (t : Y) (y : G₁ X Y) :
    MemY (sum o₁ o₂) t (.inl y) ↔ MemY o₁ t y :=
  ⟨fun ⟨q, e⟩ => ⟨q.down, e⟩, fun ⟨q, e⟩ => ⟨⟨q⟩, e⟩⟩

@[simp] theorem memY_sum_inr (t : Y) (y : G₂ X Y) :
    MemY (sum o₁ o₂) t (.inr y) ↔ MemY o₂ t y :=
  ⟨fun ⟨q, e⟩ => ⟨q.down, e⟩, fun ⟨q, e⟩ => ⟨⟨q⟩, e⟩⟩

/-- Through a sum at any value: on the side the value is on. -/
@[simp] theorem memX_sum (x : X) (y : G₁ X Y ⊕ G₂ X Y) :
    MemX (sum o₁ o₂) x y ↔ (∃ a, y = .inl a ∧ MemX o₁ x a) ∨ ∃ b, y = .inr b ∧ MemX o₂ x b := by
  cases y with
  | inl a => simp only [memX_sum_inl, Sum.inl.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, or_false]
  | inr b => simp only [memX_sum_inr, Sum.inr.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, false_or]

/-- Through a sum at any value: on the side the value is on. -/
@[simp] theorem memY_sum (t : Y) (y : G₁ X Y ⊕ G₂ X Y) :
    MemY (sum o₁ o₂) t y ↔ (∃ a, y = .inl a ∧ MemY o₁ t a) ∨ ∃ b, y = .inr b ∧ MemY o₂ t b := by
  cases y with
  | inl a => simp only [memY_sum_inl, Sum.inl.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, or_false]
  | inr b => simp only [memY_sum_inr, Sum.inr.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, false_or]

end Forms

section Dependent

variable {A : Type a} {ShA : A → Type s} {PXA : ∀ x, ShA x → Type p}
  {PYA : ∀ x, ShA x → Type q} {GA : A → Type u → Type w → Type v}
  (o : ∀ x, Occ₂ (ShA x) (PXA x) (PYA x) (GA x))

@[simp] theorem memX_pi (x : X) (k : ∀ a, GA a X Y) :
    MemX (pi A o) x k ↔ ∃ a, MemX (o a) x (k a) :=
  ⟨fun ⟨q, e⟩ => ⟨q.1, q.2, e⟩, fun ⟨a, q, e⟩ => ⟨⟨a, q⟩, e⟩⟩

@[simp] theorem memY_pi (t : Y) (k : ∀ a, GA a X Y) :
    MemY (pi A o) t k ↔ ∃ a, MemY (o a) t (k a) :=
  ⟨fun ⟨q, e⟩ => ⟨q.1, q.2, e⟩, fun ⟨a, q, e⟩ => ⟨⟨a, q⟩, e⟩⟩

@[simp] theorem memX_sigma (x : X) (z : Σ a, GA a X Y) :
    MemX (sigma A o) x z ↔ MemX (o z.1) x z.2 :=
  Iff.rfl

@[simp] theorem memY_sigma (t : Y) (z : Σ a, GA a X Y) :
    MemY (sigma A o) t z ↔ MemY (o z.1) t z.2 :=
  Iff.rfl

end Dependent

section DependentP

variable {P : Prop} {ShP : P → Type s} {PXP : ∀ h, ShP h → Type p}
  {PYP : ∀ h, ShP h → Type q} {GP : P → Type u → Type w → Type v}
  (o : ∀ h, Occ₂ (ShP h) (PXP h) (PYP h) (GP h))

@[simp] theorem memX_piP (x : X) (k : ∀ h, GP h X Y) :
    MemX (piP P o) x k ↔ ∃ h, MemX (o h) x (k h) :=
  ⟨fun ⟨q, e⟩ => ⟨q.1, q.2, e⟩, fun ⟨h, q, e⟩ => ⟨⟨h, q⟩, e⟩⟩

@[simp] theorem memY_piP (t : Y) (k : ∀ h, GP h X Y) :
    MemY (piP P o) t k ↔ ∃ h, MemY (o h) t (k h) :=
  ⟨fun ⟨q, e⟩ => ⟨q.1, q.2, e⟩, fun ⟨h, q, e⟩ => ⟨⟨h, q⟩, e⟩⟩

end DependentP

section Comp

variable {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {PX' : Sh' → Type p'}
  {PY' : Sh' → Type q'} {G : Type w' → Type v} {H : Type u → Type w → Type w'}
  (oG : Occ Sh Pos G) (oH : Occ₂ Sh' PX' PY' H)

/-- Through a composite: a member of a member of the outer structure. -/
@[simp] theorem memX_comp (x : X) (y : G (H X Y)) :
    MemX (comp oG oH) x y ↔ ∃ z, Occ.Mem oG z y ∧ MemX oH x z :=
  ⟨fun ⟨r, e⟩ => ⟨_, ⟨r.1, rfl⟩, r.2, e⟩, fun ⟨_, ⟨q, e⟩, r, e'⟩ => by subst e; exact ⟨⟨q, r⟩, e'⟩⟩

/-- Through a composite: a member of a member of the outer structure. -/
@[simp] theorem memY_comp (t : Y) (y : G (H X Y)) :
    MemY (comp oG oH) t y ↔ ∃ z, Occ.Mem oG z y ∧ MemY oH t z :=
  ⟨fun ⟨r, e⟩ => ⟨_, ⟨r.1, rfl⟩, r.2, e⟩, fun ⟨_, ⟨q, e⟩, r, e'⟩ => by subst e; exact ⟨⟨q, r⟩, e'⟩⟩

end Comp

end MemCompute

/-! ### A member with a property

What `simp` makes of `∃ t, MemY o t y ∧ P t`, the members in `Y` of a nested argument with a
property, before it computes the membership (`simp ↓`), as for `Occ.Mem` (`Occ.exists_mem_prod`,
…): the combinators are gone through first, so that the member is eliminated at each leaf also
where several occurrences make a disjunction (`List (α ⊕ T α × T α)`), which the membership
computed first would leave under an existential. -/

section ExistsMem

variable {X : Type u} {Y : Type w} (P : Y → Prop)

@[simp ↓] theorem exists_memY_const (A : Type v) (a : A) :
    (∃ t, MemY (const A) (X := X) t a ∧ P t) ↔ False :=
  ⟨fun ⟨_, h, _⟩ => not_memY_const A _ a h, False.elim⟩

@[simp ↓] theorem exists_memY_ofX {ShX : Type s} {PosX : ShX → Type p} {GX : Type u → Type v}
    (o : Occ ShX PosX GX) (y : GX X) : (∃ t, MemY (Y := Y) (ofX o) t y ∧ P t) ↔ False :=
  ⟨fun ⟨_, h, _⟩ => not_memY_ofX o _ y h, False.elim⟩

@[simp ↓] theorem exists_memY_ofY {ShY : Type s} {PosY : ShY → Type q} {GY : Type w → Type v}
    (o : Occ ShY PosY GY) (y : GY Y) :
    (∃ t, MemY (X := X) (ofY o) t y ∧ P t) ↔
      ∃ t, Occ.Mem o t y ∧ P t :=
  Iff.rfl

section Forms

variable {Sh₁ : Type s} {PX₁ : Sh₁ → Type p} {PY₁ : Sh₁ → Type q}
  {Sh₂ : Type s'} {PX₂ : Sh₂ → Type p'} {PY₂ : Sh₂ → Type q'}
  {G₁ : Type u → Type w → Type v} {G₂ : Type u → Type w → Type v'}
  (o₁ : Occ₂ Sh₁ PX₁ PY₁ G₁) (o₂ : Occ₂ Sh₂ PX₂ PY₂ G₂)

@[simp ↓] theorem exists_memY_prod (y : G₁ X Y × G₂ X Y) :
    (∃ t, MemY (prod o₁ o₂) t y ∧ P t) ↔
      (∃ t, MemY o₁ t y.1 ∧ P t) ∨ ∃ t, MemY o₂ t y.2 ∧ P t := by
  simp only [memY_prod, or_and_right, exists_or]

@[simp ↓] theorem exists_memY_sum (y : G₁ X Y ⊕ G₂ X Y) :
    (∃ t, MemY (sum o₁ o₂) t y ∧ P t) ↔
      (∃ a, y = .inl a ∧ ∃ t, MemY o₁ t a ∧ P t) ∨ ∃ b, y = .inr b ∧ ∃ t, MemY o₂ t b ∧ P t := by
  cases y with
  | inl a => simp only [memY_sum_inl, Sum.inl.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, or_false]
  | inr b => simp only [memY_sum_inr, Sum.inr.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, false_or]

end Forms

section Dependent

variable {A : Type a} {ShA : A → Type s} {PXA : ∀ x, ShA x → Type p}
  {PYA : ∀ x, ShA x → Type q} {GA : A → Type u → Type w → Type v}
  (o : ∀ x, Occ₂ (ShA x) (PXA x) (PYA x) (GA x))

@[simp ↓] theorem exists_memY_pi (k : ∀ a, GA a X Y) :
    (∃ t, MemY (pi A o) t k ∧ P t) ↔ ∃ a, ∃ t, MemY (o a) t (k a) ∧ P t := by
  simp only [memY_pi]
  exact ⟨fun ⟨t, ⟨a, h⟩, h'⟩ => ⟨a, t, h, h'⟩, fun ⟨a, t, h, h'⟩ => ⟨t, ⟨a, h⟩, h'⟩⟩

@[simp ↓] theorem exists_memY_sigma (z : Σ a, GA a X Y) :
    (∃ t, MemY (sigma A o) t z ∧ P t) ↔ ∃ t, MemY (o z.1) t z.2 ∧ P t :=
  Iff.rfl

end Dependent

@[simp ↓] theorem exists_memY_piP {Q : Prop} {ShP : Q → Type s} {PXP : ∀ h, ShP h → Type p}
    {PYP : ∀ h, ShP h → Type q} {GP : Q → Type u → Type w → Type v}
    (o : ∀ h, Occ₂ (ShP h) (PXP h) (PYP h) (GP h)) (k : ∀ h, GP h X Y) :
    (∃ t, MemY (piP Q o) t k ∧ P t) ↔ ∃ h, ∃ t, MemY (o h) t (k h) ∧ P t := by
  simp only [memY_piP]
  exact ⟨fun ⟨t, ⟨h, m⟩, h'⟩ => ⟨h, t, m, h'⟩, fun ⟨h, t, m, h'⟩ => ⟨t, ⟨h, m⟩, h'⟩⟩

@[simp ↓] theorem exists_memY_comp {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'}
    {PX' : Sh' → Type p'} {PY' : Sh' → Type q'} {G : Type w' → Type v}
    {H : Type u → Type w → Type w'} (oG : Occ Sh Pos G) (oH : Occ₂ Sh' PX' PY' H)
    (y : G (H X Y)) :
    (∃ t, MemY (comp oG oH) t y ∧ P t) ↔
      ∃ z, Occ.Mem oG z y ∧ ∃ t, MemY oH t z ∧ P t := by
  simp only [memY_comp]
  exact ⟨fun ⟨t, ⟨z, hz, m⟩, h⟩ => ⟨z, hz, t, m, h⟩, fun ⟨z, hz, t, m, h⟩ => ⟨t, ⟨z, hz, m⟩, h⟩⟩

end ExistsMem

end Occ₂

end Codata
