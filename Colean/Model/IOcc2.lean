import Colean.Model.Occ2

/-!
# The model, nested occurrences: occurrence structures in two variables over a family

*Spec.* Input: nothing but the syntax of an argument type with occurrences of a parameter `X`
and of a family `Y` over an index type, mirrored by the combinators. Output: for a type
expression `G X Y`, a structure `IOcc₂ Sh PX PY pidx G`, an equivalence
`G X Y ≃ ILay₂ PX PY pidx X Y`, its map in both variables, its laws, the computation of the map
through the combinators, the agreement of its map in `Y` with the map of the indexed structure of
`G X` in `Y` alone (`AgreeY`), and membership in each variable. Used by `deriveInstances`
(`Gen/Derive.lean`), and by users to compute the map and membership in its rules.

This is `Model/Occ2.lean` for a family, a type with indices or the types of a block: the
recursive variable is a family over the index of the presentation, each position in `Y` at its
index (`pidx`), as in the layer `ILay` of `Model/Poly.lean`, and the parameter a type. A field
`p : List (α × T n)` of a family, or `p : List (RA α × Nat)` of a type of a block, has positions
of both kinds, or positions at a type of the block only after cases on them, in one argument
under a named type constructor; its layer is that of such a structure, whose positions carry the
index of the presentation by construction.

The command's functor `T.F` maps such an argument by its indexed structure in `Y` alone, with the
parameter constant, over the family's own index, which in a block is the block's index at the
parameters (`Blk.Ix`) while the presentation's is the block's index without the parameters that
vary. `AgreeY o o' X ι oY oY'` says that the map in `Y` of a structure in two variables over the
index `I` of the presentation is the map of `oY` over the family's index `J`, read along
`ι : I → J`; it holds through every combinator.

When the positions in `Y` are all at one index after cases on them (`List (α × T n)`,
`List (RA α × Nat)`), the structure is a plain one at that index (`ofOcc₂`): its map and members
are those of the plain structure by definition, so the command states its rules as for a single
type. Its agreement with the family's indexed structure is the plain one, with the indexed
structure at that index being the plain one in `Y` alone, which holds by unfolding
(`AgreeY.ofOcc₂`).
-/

open Colean

universe u u' u'' w w' w'' v v' v'' s s' p p' q q' a r r' t t' j i

namespace Codata

/-- The layer of a structure in two variables over a family: a shape, its contents in `X` at the
positions `PX`, and in the family `Y` at the positions `PY`, each at its index `pidx`. -/
abbrev ILay₂ {J : Type j} {Sh : Type s} (PX : Sh → Type p) (PY : Sh → Type q)
    (pidx : (sh : Sh) → PY sh → J) (X : Type u) (Y : J → Type w) : Type (max s p q u w) :=
  Σ sh : Sh, (PX sh → X) × ((q : PY sh) → Y (pidx sh q))

/-- An occurrence structure in two variables over a family: an equivalence
`G X Y ≃ ILay₂ PX PY pidx X Y` for every type `X` and every family `Y` over `J`, the shapes, the
positions and their indices independent of `X` and `Y`. -/
structure IOcc₂ {J : Type j} (Sh : Type s) (PX : Sh → Type p) (PY : Sh → Type q)
    (pidx : (sh : Sh) → PY sh → J) (G : Type u → (J → Type w) → Type v) where
  equiv {X : Type u} {Y : J → Type w} : G X Y ≃ ILay₂ PX PY pidx X Y

namespace IOcc₂

/-! ### The generic laws -/

section Laws

variable {J : Type j} {Sh : Type s} {PX : Sh → Type p} {PY : Sh → Type q}
  {pidx : (sh : Sh) → PY sh → J}
variable {G : Type u → (J → Type w) → Type v} (o : IOcc₂ Sh PX PY pidx G)
  {G' : Type u' → (J → Type w') → Type v'} (o' : IOcc₂ Sh PX PY pidx G')
  {G'' : Type u'' → (J → Type w'') → Type v''} (o'' : IOcc₂ Sh PX PY pidx G'')
variable {X : Type u} {Y : J → Type w} {X' : Type u'} {Y' : J → Type w'} {X'' : Type u''}
  {Y'' : J → Type w''}

/-- The layer of a value: its shape and its contents of both kinds. -/
def toC (x : G X Y) : ILay₂ PX PY pidx X Y := o.equiv x

/-- The value of a layer. -/
def ofC (z : ILay₂ PX PY pidx X Y) : G X Y := o.equiv.symm z

theorem ofC_toC (x : G X Y) : o.ofC (o.toC x) = x := o.equiv.symm_apply_apply x

theorem toC_ofC (z : ILay₂ PX PY pidx X Y) : o.toC (o.ofC z) = z := o.equiv.apply_symm_apply z

/-- `ofC_toC` with the layer written out, as it appears in a generated `ofC (toC a)`. -/
theorem ofC_toC' (x : G X Y) :
    o.ofC ⟨(o.toC x).1, fun q => (o.toC x).2.1 q, fun q => (o.toC x).2.2 q⟩ = x :=
  o.ofC_toC x

/-- The action on functions in both variables, between two structures with the same shapes,
positions and indices. -/
def map (f : X → X') (g : ∀ j, Y j → Y' j) (x : G X Y) : G' X' Y' :=
  o'.ofC ⟨(o.toC x).1, fun q => f ((o.toC x).2.1 q), fun q => g _ ((o.toC x).2.2 q)⟩

theorem map_id (x : G X Y) : map o o (fun x => x) (fun _ y => y) x = x := o.ofC_toC x

theorem map_ofC (f : X → X') (g : ∀ j, Y j → Y' j) (sh : Sh) (c : PX sh → X)
    (d : (q : PY sh) → Y (pidx sh q)) :
    map o o' f g (o.ofC ⟨sh, c, d⟩) = o'.ofC ⟨sh, fun q => f (c q), fun q => g _ (d q)⟩ := by
  unfold map
  rw [toC_ofC]

/-- The layer of a mapped value: the same shape, the contents mapped. -/
theorem toC_map (f : X → X') (g : ∀ j, Y j → Y' j) (x : G X Y) :
    o'.toC (map o o' f g x) =
      ⟨(o.toC x).1, fun q => f ((o.toC x).2.1 q), fun q => g _ ((o.toC x).2.2 q)⟩ := by
  unfold map
  rw [toC_ofC]

theorem map_map (f' : X' → X'') (g' : ∀ j, Y' j → Y'' j) (f : X → X') (g : ∀ j, Y j → Y' j)
    (x : G X Y) :
    map o' o'' f' g' (map o o' f g x) =
      map o o'' (fun x => f' (f x)) (fun j y => g' j (g j y)) x := by
  unfold map
  rw [toC_ofC]

end Laws

/-! ### Extensionality of layers through functions and composites -/

section Ext

variable {J : Type j} {X : Type u} {Y : J → Type w}

/-- Extensionality for the layers of a function: a family of layers is a shape function and two
contents functions. -/
theorem pi_ext {A : Type a} {ShA : A → Type s} {PXA : ∀ x, ShA x → Type p}
    {PYA : ∀ x, ShA x → Type q} {pidxA : ∀ x (sh : ShA x), PYA x sh → J}
    (T : ∀ x, ILay₂ (PXA x) (PYA x) (pidxA x) X Y) (sh : ∀ x, ShA x)
    (c : (Σ x, PXA x (sh x)) → X) (d : (q : Σ x, PYA x (sh x)) → Y (pidxA q.1 (sh q.1) q.2))
    (h : ∀ x, T x = ⟨sh x, fun q => c ⟨x, q⟩, fun q => d ⟨x, q⟩⟩) :
    (⟨fun x => (T x).1, fun q => (T q.1).2.1 q.2, fun q => (T q.1).2.2 q.2⟩ :
      ILay₂ (fun sh : ∀ x, ShA x => Σ x, PXA x (sh x)) (fun sh => Σ x, PYA x (sh x))
        (fun sh q => pidxA q.1 (sh q.1) q.2) X Y) = ⟨sh, c, d⟩ := by
  have : T = fun x => ⟨sh x, fun q => c ⟨x, q⟩, fun q => d ⟨x, q⟩⟩ := funext h
  subst this
  rfl

/-- The same over a proposition. -/
theorem piP_ext {P : Prop} {ShP : P → Type s} {PXP : ∀ h, ShP h → Type p}
    {PYP : ∀ h, ShP h → Type q} {pidxP : ∀ h (sh : ShP h), PYP h sh → J}
    (T : ∀ h, ILay₂ (PXP h) (PYP h) (pidxP h) X Y) (sh : ∀ h, ShP h)
    (c : (Σ' h, PXP h (sh h)) → X) (d : (q : Σ' h, PYP h (sh h)) → Y (pidxP q.1 (sh q.1) q.2))
    (h : ∀ h, T h = ⟨sh h, fun q => c ⟨h, q⟩, fun q => d ⟨h, q⟩⟩) :
    (⟨fun h => (T h).1, fun q => (T q.1).2.1 q.2, fun q => (T q.1).2.2 q.2⟩ :
      ILay₂ (fun sh : ∀ h, ShP h => Σ' h, PXP h (sh h)) (fun sh => Σ' h, PYP h (sh h))
        (fun sh q => pidxP q.1 (sh q.1) q.2) X Y) = ⟨sh, c, d⟩ := by
  have : T = fun h => ⟨sh h, fun q => c ⟨h, q⟩, fun q => d ⟨h, q⟩⟩ := funext h
  subst this
  rfl

/-- Extensionality for the layers of a composite: the inner layers at the positions of an outer
shape. -/
theorem comp_ext {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {PX' : Sh' → Type p'}
    {PY' : Sh' → Type q'} {pidx' : (sh : Sh') → PY' sh → J} (sh : Sh)
    (T : Pos sh → ILay₂ PX' PY' pidx' X Y) (t : Pos sh → Sh') (c : (Σ q, PX' (t q)) → X)
    (d : (r : Σ q, PY' (t q)) → Y (pidx' (t r.1) r.2))
    (h : ∀ q, T q = ⟨t q, fun r => c ⟨q, r⟩, fun r => d ⟨q, r⟩⟩) :
    (⟨⟨sh, fun q => (T q).1⟩, fun r => (T r.1).2.1 r.2, fun r => (T r.1).2.2 r.2⟩ :
      ILay₂ (fun z : Σ sh, Pos sh → Sh' => Σ q, PX' (z.2 q)) (fun z => Σ q, PY' (z.2 q))
        (fun z r => pidx' (z.2 r.1) r.2) X Y) = ⟨⟨sh, t⟩, c, d⟩ := by
  have : T = fun q => ⟨t q, fun r => c ⟨q, r⟩, fun r => d ⟨q, r⟩⟩ := funext h
  subst this
  rfl

end Ext

/-! ### The combinators

As for `Occ₂`, every combinator is defined by its two maps directly, so that `toC`, `ofC` and
`map` compute through it by `rfl`. A part in `X` alone is a plain structure in it (`ofX`), a part
in `Y` alone an indexed one (`ofY`): the occurrence at the index `i` is `ofY (IOcc.hole i)`. -/

section Leaves

variable {J : Type j}

/-- A constant: the value is the shape, there are no positions. -/
def const (A : Type v) :
    IOcc₂ (J := J) A (fun _ => Empty) (fun _ => Empty) (fun _ e => e.elim)
      (fun (_ : Type u) (_ : J → Type w) => A) where
  equiv := {
    toFun x := ⟨x, Empty.elim, fun e => e.elim⟩
    invFun z := z.1
    left_inv _ := rfl
    right_inv := fun ⟨_, _, _⟩ =>
      congrArg _ (Prod.ext (funext fun x => x.elim) (funext fun x => x.elim)) }

/-- A part in `X` alone, with its structure in `X`: positions in `X` only. -/
def ofX {ShX : Type s} {PosX : ShX → Type p} {GX : Type u → Type v} (o : Occ ShX PosX GX) :
    IOcc₂ (J := J) ShX PosX (fun _ => Empty) (fun _ e => e.elim)
      (fun X (_ : J → Type w) => GX X) where
  equiv := {
    toFun x := ⟨(o.toC x).1, (o.toC x).2, fun e => e.elim⟩
    invFun z := o.ofC ⟨z.1, z.2.1⟩
    left_inv x := o.ofC_toC x
    right_inv := fun ⟨sh, c, _⟩ => by
      dsimp only
      generalize h : o.toC (o.ofC ⟨sh, c⟩) = z
      rw [Occ.toC_ofC] at h
      subst h
      exact congrArg (Sigma.mk sh) (Prod.ext rfl (funext fun x => x.elim)) }

/-- A part in `Y` alone, with its indexed structure in `Y`: positions in `Y` only. -/
def ofY {ShY : Type s} {PosY : ShY → Type q} {pidxY : (sh : ShY) → PosY sh → J}
    {GY : (J → Type w) → Type v} (o : IOcc ShY PosY pidxY GY) :
    IOcc₂ ShY (fun _ => Empty) PosY pidxY (fun (_ : Type u) Y => GY Y) where
  equiv := {
    toFun y := ⟨(o.toC y).1, Empty.elim, (o.toC y).2⟩
    invFun z := o.ofC ⟨z.1, z.2.2⟩
    left_inv y := o.ofC_toC y
    right_inv := fun ⟨sh, _, d⟩ => by
      dsimp only
      generalize h : o.toC (o.ofC ⟨sh, d⟩) = z
      rw [IOcc.toC_ofC] at h
      subst h
      exact congrArg (Sigma.mk sh) (Prod.ext (funext fun x => x.elim) rfl) }

/-- A plain structure in two variables at the index `i`: every position in `Y` is at `i`. -/
def ofOcc₂ {Sh : Type s} {PX : Sh → Type p} {PY : Sh → Type q}
    {G : Type u → Type w → Type v} (o : Occ₂ Sh PX PY G) (i : J) :
    IOcc₂ Sh PX PY (fun _ _ => i) (fun X Y => G X (Y i)) :=
  ⟨o.equiv⟩

end Leaves

section Combinators

variable {J : Type j} {Sh₁ : Type s} {PX₁ : Sh₁ → Type p} {PY₁ : Sh₁ → Type q}
  {pidx₁ : (sh : Sh₁) → PY₁ sh → J} {Sh₂ : Type s'} {PX₂ : Sh₂ → Type p'} {PY₂ : Sh₂ → Type q'}
  {pidx₂ : (sh : Sh₂) → PY₂ sh → J}
  {G₁ : Type u → (J → Type w) → Type v} {G₂ : Type u → (J → Type w) → Type v'}

/-- A product: a pair of shapes, the sums of the positions. -/
def prod (o₁ : IOcc₂ Sh₁ PX₁ PY₁ pidx₁ G₁) (o₂ : IOcc₂ Sh₂ PX₂ PY₂ pidx₂ G₂) :
    IOcc₂ (Sh₁ × Sh₂) (fun sh => PX₁ sh.1 ⊕ PX₂ sh.2) (fun sh => PY₁ sh.1 ⊕ PY₂ sh.2)
      (fun sh q => Sum.elim (pidx₁ sh.1) (pidx₂ sh.2) q) (fun X Y => G₁ X Y × G₂ X Y) where
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
def sum (o₁ : IOcc₂ Sh₁ PX₁ PY₁ pidx₁ G₁) (o₂ : IOcc₂ Sh₂ PX₂ PY₂ pidx₂ G₂) :
    IOcc₂ (Sh₁ ⊕ Sh₂) (Occ.SumPos PX₁ PX₂) (Occ.SumPos PY₁ PY₂) (IOcc.sumIdx pidx₁ pidx₂)
      (fun X Y => G₁ X Y ⊕ G₂ X Y) where
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

variable {J : Type j} (A : Type a) {ShA : A → Type s} {PXA : ∀ x, ShA x → Type p}
  {PYA : ∀ x, ShA x → Type q} {pidxA : ∀ x (sh : ShA x), PYA x sh → J}
  {GA : A → Type u → (J → Type w) → Type v}

/-- A function from a constant type: a shape at every point, a point with a position there. -/
def pi (o : ∀ x, IOcc₂ (ShA x) (PXA x) (PYA x) (pidxA x) (GA x)) :
    IOcc₂ (∀ x : A, ShA x) (fun sh => Σ x, PXA x (sh x)) (fun sh => Σ x, PYA x (sh x))
      (fun sh q => pidxA q.1 (sh q.1) q.2) (fun X Y => ∀ x, GA x X Y) where
  equiv := {
    toFun k := ⟨fun x => ((o x).toC (k x)).1, fun q => ((o q.1).toC (k q.1)).2.1 q.2,
      fun q => ((o q.1).toC (k q.1)).2.2 q.2⟩
    invFun z x := (o x).ofC ⟨z.1 x, fun q => z.2.1 ⟨x, q⟩, fun q => z.2.2 ⟨x, q⟩⟩
    left_inv k := funext fun x => (o x).ofC_toC' (k x)
    right_inv := fun ⟨sh, c, d⟩ => pi_ext _ sh c d fun x => (o x).toC_ofC _ }

/-- A dependent pair over a constant type: a point with a shape there, its positions. -/
def sigma (o : ∀ x, IOcc₂ (ShA x) (PXA x) (PYA x) (pidxA x) (GA x)) :
    IOcc₂ (Σ x : A, ShA x) (fun sh => PXA sh.1 sh.2) (fun sh => PYA sh.1 sh.2)
      (fun sh q => pidxA sh.1 sh.2 q) (fun X Y => Σ x, GA x X Y) where
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

variable {J : Type j} (P : Prop) {ShP : P → Type s} {PXP : ∀ h, ShP h → Type p}
  {PYP : ∀ h, ShP h → Type q} {pidxP : ∀ h (sh : ShP h), PYP h sh → J}
  {GP : P → Type u → (J → Type w) → Type v}

/-- A function from a proposition. -/
def piP (o : ∀ h, IOcc₂ (ShP h) (PXP h) (PYP h) (pidxP h) (GP h)) :
    IOcc₂ (∀ h : P, ShP h) (fun sh => Σ' h, PXP h (sh h)) (fun sh => Σ' h, PYP h (sh h))
      (fun sh q => pidxP q.1 (sh q.1) q.2) (fun X Y => ∀ h, GP h X Y) where
  equiv := {
    toFun k := ⟨fun h => ((o h).toC (k h)).1, fun q => ((o q.1).toC (k q.1)).2.1 q.2,
      fun q => ((o q.1).toC (k q.1)).2.2 q.2⟩
    invFun z h := (o h).ofC ⟨z.1 h, fun q => z.2.1 ⟨h, q⟩, fun q => z.2.2 ⟨h, q⟩⟩
    left_inv k := funext fun h => (o h).ofC_toC' (k h)
    right_inv := fun ⟨sh, c, d⟩ => piP_ext _ sh c d fun h => (o h).toC_ofC _ }

end Prop'

section Comp

variable {J : Type j} {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {PX' : Sh' → Type p'}
  {PY' : Sh' → Type q'} {pidx' : (sh : Sh') → PY' sh → J}

/-- A named type constructor in one variable applied to an expression in two: the shapes are a
shape of the outer structure with a shape of the inner one at each of its positions, the
positions of each kind a position of the outer with a position of that kind of the inner shape
there, at the index of the latter. -/
def comp {G : Type w' → Type v} (oG : Occ Sh Pos G) {H : Type u → (J → Type w) → Type w'}
    (oH : IOcc₂ Sh' PX' PY' pidx' H) :
    IOcc₂ (Σ sh, Pos sh → Sh') (fun z => Σ q, PX' (z.2 q)) (fun z => Σ q, PY' (z.2 q))
      (fun z r => pidx' (z.2 r.1) r.2) (fun X Y => G (H X Y)) where
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

variable {J : Type j} {X : Type u} {Y : J → Type w} {X' : Type u'} {Y' : J → Type w'}

@[simp] theorem map_const {A : Type v} (f : X → X') (g : ∀ j, Y j → Y' j) (x : A) :
    map (const A) (const A) f g x = x := rfl

/-- The map of a part in `X` alone is the map of its structure. -/
@[simp] theorem map_ofX {ShX : Type s} {PosX : ShX → Type p} {GX : Type u → Type v}
    {GX' : Type u' → Type v'} (o : Occ ShX PosX GX) (o' : Occ ShX PosX GX') (f : X → X')
    (g : ∀ j, Y j → Y' j) (x : GX X) : map (ofX o) (ofX o') f g x = Occ.map o o' f x := rfl

/-- The map of a part in `Y` alone is the map of its indexed structure. -/
@[simp] theorem map_ofY {ShY : Type s} {PosY : ShY → Type q} {pidxY : (sh : ShY) → PosY sh → J}
    {GY : (J → Type w) → Type v} {GY' : (J → Type w') → Type v'} (o : IOcc ShY PosY pidxY GY)
    (o' : IOcc ShY PosY pidxY GY') (f : X → X') (g : ∀ j, Y j → Y' j) (y : GY Y) :
    map (ofY o) (ofY o') f g y = IOcc.map o o' g y := rfl

/-- The map of a plain structure at an index is its map at that index. -/
@[simp] theorem map_ofOcc₂ {Sh : Type s} {PX : Sh → Type p} {PY : Sh → Type q}
    {G : Type u → Type w → Type v} {G' : Type u' → Type w' → Type v'} (o : Occ₂ Sh PX PY G)
    (o' : Occ₂ Sh PX PY G') (i : J) (f : X → X') (g : ∀ j, Y j → Y' j) (y : G X (Y i)) :
    map (ofOcc₂ o i) (ofOcc₂ o' i) f g y = Occ₂.map o o' f (g i) y := rfl

variable {Sh₁ : Type s} {PX₁ : Sh₁ → Type p} {PY₁ : Sh₁ → Type q}
  {pidx₁ : (sh : Sh₁) → PY₁ sh → J} {Sh₂ : Type s'} {PX₂ : Sh₂ → Type p'} {PY₂ : Sh₂ → Type q'}
  {pidx₂ : (sh : Sh₂) → PY₂ sh → J}
  {G₁ : Type u → (J → Type w) → Type v} {G₂ : Type u → (J → Type w) → Type v'}
  {G₁' : Type u' → (J → Type w') → Type v''} {G₂' : Type u' → (J → Type w') → Type w''}
  (o₁ : IOcc₂ Sh₁ PX₁ PY₁ pidx₁ G₁) (o₂ : IOcc₂ Sh₂ PX₂ PY₂ pidx₂ G₂)
  (o₁' : IOcc₂ Sh₁ PX₁ PY₁ pidx₁ G₁') (o₂' : IOcc₂ Sh₂ PX₂ PY₂ pidx₂ G₂')

@[simp] theorem map_prod (f : X → X') (g : ∀ j, Y j → Y' j) (x : G₁ X Y × G₂ X Y) :
    map (prod o₁ o₂) (prod o₁' o₂') f g x = (map o₁ o₁' f g x.1, map o₂ o₂' f g x.2) := rfl

@[simp] theorem map_sum_inl (f : X → X') (g : ∀ j, Y j → Y' j) (x : G₁ X Y) :
    map (sum o₁ o₂) (sum o₁' o₂') f g (.inl x) = .inl (map o₁ o₁' f g x) := rfl

@[simp] theorem map_sum_inr (f : X → X') (g : ∀ j, Y j → Y' j) (x : G₂ X Y) :
    map (sum o₁ o₂) (sum o₁' o₂') f g (.inr x) = .inr (map o₂ o₂' f g x) := rfl

end Compute

section ComputeDep

variable {J : Type j} {X : Type u} {Y : J → Type w} {X' : Type u'} {Y' : J → Type w'}
variable {A : Type a} {ShA : A → Type s} {PXA : ∀ x, ShA x → Type p}
  {PYA : ∀ x, ShA x → Type q} {pidxA : ∀ x (sh : ShA x), PYA x sh → J}
  {GA : A → Type u → (J → Type w) → Type v} {GA' : A → Type u' → (J → Type w') → Type v'}
  (o : ∀ x, IOcc₂ (ShA x) (PXA x) (PYA x) (pidxA x) (GA x))
  (o' : ∀ x, IOcc₂ (ShA x) (PXA x) (PYA x) (pidxA x) (GA' x))

@[simp] theorem map_pi (f : X → X') (g : ∀ j, Y j → Y' j) (k : ∀ x, GA x X Y) :
    map (pi A o) (pi A o') f g k = fun x => map (o x) (o' x) f g (k x) := rfl

@[simp] theorem map_sigma (f : X → X') (g : ∀ j, Y j → Y' j) (z : Σ x, GA x X Y) :
    map (sigma A o) (sigma A o') f g z = ⟨z.1, map (o z.1) (o' z.1) f g z.2⟩ := rfl

@[simp] theorem map_piP {P : Prop} {ShP : P → Type s} {PXP : ∀ h, ShP h → Type p}
    {PYP : ∀ h, ShP h → Type q} {pidxP : ∀ h (sh : ShP h), PYP h sh → J}
    {GP : P → Type u → (J → Type w) → Type v} {GP' : P → Type u' → (J → Type w') → Type v'}
    (o : ∀ h, IOcc₂ (ShP h) (PXP h) (PYP h) (pidxP h) (GP h))
    (o' : ∀ h, IOcc₂ (ShP h) (PXP h) (PYP h) (pidxP h) (GP' h)) (f : X → X')
    (g : ∀ j, Y j → Y' j) (k : ∀ h, GP h X Y) :
    map (piP P o) (piP P o') f g k = fun h => map (o h) (o' h) f g (k h) :=
  rfl

end ComputeDep

section ComputeComp

variable {J : Type j} {X : Type u} {Y : J → Type w} {X' : Type u'} {Y' : J → Type w'}
variable {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {PX' : Sh' → Type p'}
  {PY' : Sh' → Type q'} {pidx' : (sh : Sh') → PY' sh → J} {G : Type w'' → Type v}
  {G' : Type u'' → Type v'} {H : Type u → (J → Type w) → Type w''}
  {H' : Type u' → (J → Type w') → Type u''} (oG : Occ Sh Pos G) (oG' : Occ Sh Pos G')
  (oH : IOcc₂ Sh' PX' PY' pidx' H) (oH' : IOcc₂ Sh' PX' PY' pidx' H')

/-- The map through a composite is the map of the map. -/
@[simp] theorem map_comp (f : X → X') (g : ∀ j, Y j → Y' j) (x : G (H X Y)) :
    map (comp oG oH) (comp oG' oH') f g x = Occ.map oG oG' (map oH oH' f g) x := rfl

end ComputeComp

/-! ### The map in `Y` is the map of the indexed structure in `Y` alone

The command's functor maps an argument with a structure in two variables by its indexed structure
in `Y` alone, the parameter `X` constant (`IOcc.const (GX X)` where the structure in two
variables has `ofX`), over the family's own index `J`. The structure in two variables is over the
index `I` of the presentation, read in `J` along `ι`: its occurrence `ofY (IOcc.hole i)` is the
family's at `ι i`. `AgreeY o o' X ι oY oY'` says that the two maps are the same; it holds through
every combinator (`AgreeY.prod`, …), and `AgreeY.map_ofC` is how the command uses it. -/

section Agree

variable {I : Type i} {J : Type j} {Sh : Type s} {PX : Sh → Type p} {PY : Sh → Type q}
  {pidx : (sh : Sh) → PY sh → I} {G : Type u → (I → Type w) → Type v}
  {G' : Type u → (I → Type w') → Type v'} {ShY : Type r} {PosY : ShY → Type t}
  {pidxY : (sh : ShY) → PosY sh → J}

/-- The map in `Y` of `o`, `o'` at `X` is the map of `oY`, `oY'`, indexed structures of `G X` in
`Y` alone over `J`, the index `i` of `o` being `ι i`. -/
def AgreeY (o : IOcc₂ Sh PX PY pidx G) (o' : IOcc₂ Sh PX PY pidx G') (X : Type u) (ι : I → J)
    (oY : IOcc ShY PosY pidxY fun Y : J → Type w => G X fun i => Y (ι i))
    (oY' : IOcc ShY PosY pidxY fun Y : J → Type w' => G' X fun i => Y (ι i)) : Prop :=
  ∀ {Y : J → Type w} {Y' : J → Type w'} (g : ∀ j, Y j → Y' j) (y : G X fun i => Y (ι i)),
    IOcc.map oY oY' g y = map o o' (fun x => x) (fun i => g (ι i)) y

/-- The command's functor applied to a value with a given layer: the layer with its contents in
`Y` mapped. -/
theorem AgreeY.map_ofC {o : IOcc₂ Sh PX PY pidx G} {o' : IOcc₂ Sh PX PY pidx G'} {X : Type u}
    {ι : I → J} {oY : IOcc ShY PosY pidxY fun Y : J → Type w => G X fun i => Y (ι i)}
    {oY' : IOcc ShY PosY pidxY fun Y : J → Type w' => G' X fun i => Y (ι i)}
    (h : AgreeY o o' X ι oY oY') {Y : J → Type w} {Y' : J → Type w'} (g : ∀ j, Y j → Y' j)
    (sh : Sh) (c : PX sh → X) (d : (q : PY sh) → Y (ι (pidx sh q))) :
    IOcc.map oY oY' g (o.ofC (Y := fun i => Y (ι i)) ⟨sh, c, d⟩) =
      o'.ofC ⟨sh, c, fun q => g _ (d q)⟩ := by
  rw [h, IOcc₂.map_ofC]

end Agree

namespace AgreeY

variable {I : Type i} {J : Type j} {X : Type u} {ι : I → J}

theorem const (A : Type v) :
    AgreeY (const A) (const A) X ι (IOcc.const A) (IOcc.const A) :=
  fun _ _ => rfl

theorem ofX {ShX : Type s} {PosX : ShX → Type p} {GX : Type u → Type v}
    (oX : Occ ShX PosX GX) :
    AgreeY (ofX oX) (ofX oX) X ι (IOcc.const (GX X))
      (IOcc.const (GX X)) :=
  fun _ y => (oX.ofC_toC' y).symm

/-- The occurrence at the index `i₀`: the family's at `ι i₀`. -/
theorem hole (i₀ : I) :
    AgreeY (ofY (IOcc.hole i₀)) (ofY (IOcc.hole i₀)) X ι
      (IOcc.hole (ι i₀)) (IOcc.hole (ι i₀)) :=
  fun _ _ => rfl

/-- A plain leaf at the index `i₀`: the family's at `ι i₀`. -/
theorem ofOcc {ShF : Type s} {PosF : ShF → Type q} {F : Type w → Type v} {F' : Type w' → Type v'}
    (oF : Occ ShF PosF F) (oF' : Occ ShF PosF F') (i₀ : I) :
    AgreeY (ofY (IOcc.ofOcc oF i₀)) (ofY (IOcc.ofOcc oF' i₀)) X ι
      (IOcc.ofOcc oF (ι i₀)) (IOcc.ofOcc oF' (ι i₀)) :=
  fun _ _ => rfl

/-- A part in `Y` alone read along `ι`. -/
theorem reidx {ShY : Type s} {PosY : ShY → Type q} {pidxY : (sh : ShY) → PosY sh → I}
    {GY : (I → Type w) → Type v} {GY' : (I → Type w') → Type v'} (oY : IOcc ShY PosY pidxY GY)
    (oY' : IOcc ShY PosY pidxY GY') :
    AgreeY (ofY oY) (ofY oY') X ι (IOcc.reidx oY ι) (IOcc.reidx oY' ι) :=
  fun _ _ => rfl

/-- A plain structure at the index `i₀`, against an indexed structure whose map is, at the
index `ι i₀`, that of a plain one in `Y` alone (an argument whose positions are all at `ι i₀`,
`List (T n × Nat)`, `hA` by definitional unfolding): the agreement of the plain structures. -/
theorem ofOcc₂ {Sh : Type s} {PX : Sh → Type p} {PY : Sh → Type q} {G : Type u → Type w → Type v}
    {G' : Type u → Type w' → Type v'} {o : Occ₂ Sh PX PY G} {o' : Occ₂ Sh PX PY G'}
    {ShY : Type r} {PosY : ShY → Type t} {oY : Occ ShY PosY (G X)} {oY' : Occ ShY PosY (G' X)}
    (h : Occ₂.AgreeY o o' X oY oY') (i₀ : I) {ShA : Type r'} {PosA : ShA → Type t'}
    {pidxA : (sh : ShA) → PosA sh → J}
    {oA : IOcc ShA PosA pidxA fun Y : J → Type w => G X (Y (ι i₀))}
    {oA' : IOcc ShA PosA pidxA fun Y : J → Type w' => G' X (Y (ι i₀))}
    (hA : ∀ {Y : J → Type w} {Y' : J → Type w'} (g : ∀ j, Y j → Y' j) (y : G X (Y (ι i₀))),
      IOcc.map oA oA' g y = Occ.map oY oY' (g (ι i₀)) y) :
    AgreeY (IOcc₂.ofOcc₂ o i₀) (IOcc₂.ofOcc₂ o' i₀) X ι oA oA' :=
  fun g y => (hA g y).trans (h (g (ι i₀)) y)

section Combinators

variable {Sh₁ : Type s} {PX₁ : Sh₁ → Type p} {PY₁ : Sh₁ → Type q}
  {pidx₁ : (sh : Sh₁) → PY₁ sh → I} {Sh₂ : Type s'} {PX₂ : Sh₂ → Type p'} {PY₂ : Sh₂ → Type q'}
  {pidx₂ : (sh : Sh₂) → PY₂ sh → I}
  {G₁ : Type u → (I → Type w) → Type v} {G₂ : Type u → (I → Type w) → Type v'}
  {G₁' : Type u → (I → Type w') → Type v''} {G₂' : Type u → (I → Type w') → Type w''}
  {o₁ : IOcc₂ Sh₁ PX₁ PY₁ pidx₁ G₁} {o₂ : IOcc₂ Sh₂ PX₂ PY₂ pidx₂ G₂}
  {o₁' : IOcc₂ Sh₁ PX₁ PY₁ pidx₁ G₁'} {o₂' : IOcc₂ Sh₂ PX₂ PY₂ pidx₂ G₂'}
  {ShY₁ : Type r} {PosY₁ : ShY₁ → Type t} {pidxY₁ : (sh : ShY₁) → PosY₁ sh → J}
  {ShY₂ : Type r'} {PosY₂ : ShY₂ → Type t'} {pidxY₂ : (sh : ShY₂) → PosY₂ sh → J}
  {oY₁ : IOcc ShY₁ PosY₁ pidxY₁ fun Y : J → Type w => G₁ X fun i => Y (ι i)}
  {oY₂ : IOcc ShY₂ PosY₂ pidxY₂ fun Y : J → Type w => G₂ X fun i => Y (ι i)}
  {oY₁' : IOcc ShY₁ PosY₁ pidxY₁ fun Y : J → Type w' => G₁' X fun i => Y (ι i)}
  {oY₂' : IOcc ShY₂ PosY₂ pidxY₂ fun Y : J → Type w' => G₂' X fun i => Y (ι i)}

theorem prod (h₁ : AgreeY o₁ o₁' X ι oY₁ oY₁') (h₂ : AgreeY o₂ o₂' X ι oY₂ oY₂') :
    AgreeY (IOcc₂.prod o₁ o₂) (IOcc₂.prod o₁' o₂') X ι (IOcc.prod oY₁ oY₂)
      (IOcc.prod oY₁' oY₂') :=
  fun g y => Prod.ext (h₁ g y.1) (h₂ g y.2)

theorem sum (h₁ : AgreeY o₁ o₁' X ι oY₁ oY₁') (h₂ : AgreeY o₂ o₂' X ι oY₂ oY₂') :
    AgreeY (IOcc₂.sum o₁ o₂) (IOcc₂.sum o₁' o₂') X ι (IOcc.sum oY₁ oY₂) (IOcc.sum oY₁' oY₂')
  | _, _, g, .inl y => congrArg Sum.inl (h₁ g y)
  | _, _, g, .inr y => congrArg Sum.inr (h₂ g y)

end Combinators

section Dependent

variable {A : Type a} {ShA : A → Type s} {PXA : ∀ x, ShA x → Type p}
  {PYA : ∀ x, ShA x → Type q} {pidxA : ∀ x (sh : ShA x), PYA x sh → I}
  {GA : A → Type u → (I → Type w) → Type v} {GA' : A → Type u → (I → Type w') → Type v'}
  {o : ∀ x, IOcc₂ (ShA x) (PXA x) (PYA x) (pidxA x) (GA x)}
  {o' : ∀ x, IOcc₂ (ShA x) (PXA x) (PYA x) (pidxA x) (GA' x)} {ShYA : A → Type r}
  {PosYA : ∀ x, ShYA x → Type t} {pidxYA : ∀ x (sh : ShYA x), PosYA x sh → J}
  {oY : ∀ x, IOcc (ShYA x) (PosYA x) (pidxYA x) fun Y : J → Type w => GA x X fun i => Y (ι i)}
  {oY' : ∀ x, IOcc (ShYA x) (PosYA x) (pidxYA x) fun Y : J → Type w' => GA' x X fun i => Y (ι i)}

theorem pi (h : ∀ x, AgreeY (o x) (o' x) X ι (oY x) (oY' x)) :
    AgreeY (IOcc₂.pi A o) (IOcc₂.pi A o') X ι (IOcc.pi A oY) (IOcc.pi A oY') :=
  fun g k => funext fun x => h x g (k x)

theorem sigma (h : ∀ x, AgreeY (o x) (o' x) X ι (oY x) (oY' x)) :
    AgreeY (IOcc₂.sigma A o) (IOcc₂.sigma A o') X ι (IOcc.sigma A oY) (IOcc.sigma A oY') :=
  fun g z => congrArg (Sigma.mk z.1) (h z.1 g z.2)

end Dependent

theorem piP {P : Prop} {ShP : P → Type s} {PXP : ∀ h, ShP h → Type p}
    {PYP : ∀ h, ShP h → Type q} {pidxP : ∀ h (sh : ShP h), PYP h sh → I}
    {GP : P → Type u → (I → Type w) → Type v} {GP' : P → Type u → (I → Type w') → Type v'}
    {o : ∀ h, IOcc₂ (ShP h) (PXP h) (PYP h) (pidxP h) (GP h)}
    {o' : ∀ h, IOcc₂ (ShP h) (PXP h) (PYP h) (pidxP h) (GP' h)} {ShYP : P → Type r}
    {PosYP : ∀ h, ShYP h → Type t} {pidxYP : ∀ h (sh : ShYP h), PosYP h sh → J}
    {oY : ∀ h, IOcc (ShYP h) (PosYP h) (pidxYP h) fun Y : J → Type w => GP h X fun i => Y (ι i)}
    {oY' : ∀ h, IOcc (ShYP h) (PosYP h) (pidxYP h)
      fun Y : J → Type w' => GP' h X fun i => Y (ι i)}
    (h : ∀ h, AgreeY (o h) (o' h) X ι (oY h) (oY' h)) :
    AgreeY (IOcc₂.piP P o) (IOcc₂.piP P o') X ι (IOcc.piP P oY) (IOcc.piP P oY') :=
  fun g k => funext fun h' => h h' g (k h')

theorem comp {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {PX' : Sh' → Type p'}
    {PY' : Sh' → Type q'} {pidx' : (sh : Sh') → PY' sh → I} {G : Type w'' → Type v}
    {G' : Type u'' → Type v'} {H : Type u → (I → Type w) → Type w''}
    {H' : Type u → (I → Type w') → Type u''} (oG : Occ Sh Pos G) (oG' : Occ Sh Pos G')
    {oH : IOcc₂ Sh' PX' PY' pidx' H} {oH' : IOcc₂ Sh' PX' PY' pidx' H'} {ShY : Type r}
    {PosY : ShY → Type t} {pidxY : (sh : ShY) → PosY sh → J}
    {oY : IOcc ShY PosY pidxY fun Y : J → Type w => H X fun i => Y (ι i)}
    {oY' : IOcc ShY PosY pidxY fun Y : J → Type w' => H' X fun i => Y (ι i)}
    (h : AgreeY oH oH' X ι oY oY') :
    AgreeY (IOcc₂.comp oG oH) (IOcc₂.comp oG' oH') X ι (IOcc.compC oG oY) (IOcc.compC oG' oY') :=
  fun g x => congrArg (fun k => Occ.map oG oG' k x) (funext fun y => h g y)

end AgreeY

/-! ### Membership

The members of a value in `X` are the contents of its positions in `X` (`MemX`), its members in
`Y` the contents of its positions in `Y` with their indices, as dependent pairs (`MemY`), defined
from the presentation as `PolyIso.Mem` and `IPolyIso.Mem` are. A member is a pair so that `simp`
eliminates it from `∃ t, MemY o t y ∧ P t.1 t.2` once it has computed `MemY` down to the leaves:
a part in `X` alone has the members of its structure (`Occ.Mem`), an occurrence at an index its
value with that index (`memY_ofY_hole`), a plain structure at an index its members with that
index (`memY_ofOcc₂`). -/

section Mem

variable {J : Type j} {Sh : Type s} {PX : Sh → Type p} {PY : Sh → Type q}
  {pidx : (sh : Sh) → PY sh → J} {G : Type u → (J → Type w) → Type v} {X : Type u}
  {Y : J → Type w}

/-- `x` is a member of `y` in `X`: some position of `y` in `X` holds `x`. -/
def MemX (o : IOcc₂ Sh PX PY pidx G) (x : X) (y : G X Y) : Prop :=
  ∃ q, (o.toC y).2.1 q = x

/-- `t` is a member of `y` in `Y`, with its index: some position of `y` in `Y` is at `t.1` and
holds `t.2`. -/
def MemY (o : IOcc₂ Sh PX PY pidx G) (t : Σ j, Y j) (y : G X Y) : Prop :=
  ∃ q, (⟨_, (o.toC y).2.2 q⟩ : Σ j, Y j) = t

theorem memX_iff (o : IOcc₂ Sh PX PY pidx G) {x : X} {y : G X Y} :
    MemX o x y ↔ ∃ q, (o.toC y).2.1 q = x := Iff.rfl

theorem memY_iff (o : IOcc₂ Sh PX PY pidx G) {t : Σ j, Y j} {y : G X Y} :
    MemY o t y ↔ ∃ q, (⟨_, (o.toC y).2.2 q⟩ : Σ j, Y j) = t := Iff.rfl

/-- The content of a position in `Y` is a member at its index. -/
theorem memY_pos (o : IOcc₂ Sh PX PY pidx G) (y : G X Y) (q : PY (o.toC y).1) :
    MemY o ⟨_, (o.toC y).2.2 q⟩ y :=
  ⟨q, rfl⟩

end Mem

section MemCompute

variable {J : Type j} {X : Type u} {Y : J → Type w}

@[simp] theorem not_memX_const (A : Type v) (x : X) (a : A) :
    ¬ MemX (const A) (Y := Y) x a :=
  fun ⟨q, _⟩ => q.elim

@[simp] theorem not_memY_const (A : Type v) (t : Σ j, Y j) (a : A) :
    ¬ MemY (const A) (X := X) t a :=
  fun ⟨q, _⟩ => q.elim

@[simp] theorem not_memX_ofY {ShY : Type s} {PosY : ShY → Type q}
    {pidxY : (sh : ShY) → PosY sh → J} {GY : (J → Type w) → Type v} (o : IOcc ShY PosY pidxY GY)
    (x : X) (y : GY Y) : ¬ MemX (ofY o) x y :=
  fun ⟨q, _⟩ => q.elim

@[simp] theorem not_memY_ofX {ShX : Type s} {PosX : ShX → Type p} {GX : Type u → Type v}
    (o : Occ ShX PosX GX) (t : Σ j, Y j) (y : GX X) : ¬ MemY (ofX o) t y :=
  fun ⟨q, _⟩ => q.elim

/-- The members of a part in `X` alone are those of its structure. -/
@[simp] theorem memX_ofX {ShX : Type s} {PosX : ShX → Type p} {GX : Type u → Type v}
    (o : Occ ShX PosX GX) (x : X) (y : GX X) : MemX (Y := Y) (ofX o) x y ↔ Occ.Mem o x y :=
  Iff.rfl

theorem memY_ofY {ShY : Type s} {PosY : ShY → Type q} {pidxY : (sh : ShY) → PosY sh → J}
    {GY : (J → Type w) → Type v} (o : IOcc ShY PosY pidxY GY) (t : Σ j, Y j) (y : GY Y) :
    MemY (X := X) (ofY o) t y ↔ ∃ q, (⟨_, (o.toC y).2 q⟩ : Σ j, Y j) = t :=
  Iff.rfl

/-- The member at an occurrence: its value, with its index. -/
@[simp] theorem memY_ofY_hole (i : J) (t : Σ j, Y j) (y : Y i) :
    MemY (X := X) (ofY (IOcc.hole i)) t y ↔ (⟨i, y⟩ : Σ j, Y j) = t :=
  ⟨fun ⟨_, e⟩ => e, fun e => ⟨(), e⟩⟩

/-- The members through a plain leaf at an index: those of the leaf, at that index. -/
@[simp] theorem memY_ofY_ofOcc {ShF : Type s} {PosF : ShF → Type q} {F : Type w → Type v}
    (oF : Occ ShF PosF F) (i : J) (t : Σ j, Y j) (y : F (Y i)) :
    MemY (X := X) (ofY (IOcc.ofOcc oF i)) t y ↔
      ∃ z, Occ.Mem oF z y ∧ (⟨i, z⟩ : Σ j, Y j) = t :=
  ⟨fun ⟨q, e⟩ => ⟨_, ⟨q, rfl⟩, e⟩, fun ⟨_, ⟨q, e⟩, e'⟩ => by subst e; exact ⟨q, e'⟩⟩

/-- The members through a functor on families: those of its instance. -/
@[simp] theorem memY_ofY_ofIso (F : (J → Type w) → Type v) {ShF : Type s} {PosF : ShF → Type q}
    {pidxF : (sh : ShF) → PosF sh → J} [IPolyIso F ShF PosF pidxF] (t : Σ j, Y j) (y : F Y) :
    MemY (X := X) (ofY (IOcc.ofIso F)) t y ↔ IPolyIso.Mem F t.1 t.2 y :=
  Iff.rfl

/-- The members in `X` of a plain structure at an index: those of the plain structure. -/
@[simp] theorem memX_ofOcc₂ {Sh : Type s} {PX : Sh → Type p} {PY : Sh → Type q}
    {G : Type u → Type w → Type v} (o : Occ₂ Sh PX PY G) (i : J) (x : X) (y : G X (Y i)) :
    MemX (ofOcc₂ o i) x y ↔ Occ₂.MemX o x y :=
  Iff.rfl

/-- The members in `Y` of a plain structure at an index: those of the plain structure, with that
index. -/
@[simp] theorem memY_ofOcc₂ {Sh : Type s} {PX : Sh → Type p} {PY : Sh → Type q}
    {G : Type u → Type w → Type v} (o : Occ₂ Sh PX PY G) (i : J) (t : Σ j, Y j)
    (y : G X (Y i)) :
    MemY (ofOcc₂ o i) t y ↔ ∃ z, Occ₂.MemY o z y ∧ (⟨i, z⟩ : Σ j, Y j) = t :=
  ⟨fun ⟨q, e⟩ => ⟨_, ⟨q, rfl⟩, e⟩, fun ⟨_, ⟨q, e⟩, e'⟩ => by subst e; exact ⟨q, e'⟩⟩

section Forms

variable {Sh₁ : Type s} {PX₁ : Sh₁ → Type p} {PY₁ : Sh₁ → Type q}
  {pidx₁ : (sh : Sh₁) → PY₁ sh → J} {Sh₂ : Type s'} {PX₂ : Sh₂ → Type p'} {PY₂ : Sh₂ → Type q'}
  {pidx₂ : (sh : Sh₂) → PY₂ sh → J}
  {G₁ : Type u → (J → Type w) → Type v} {G₂ : Type u → (J → Type w) → Type v'}
  (o₁ : IOcc₂ Sh₁ PX₁ PY₁ pidx₁ G₁) (o₂ : IOcc₂ Sh₂ PX₂ PY₂ pidx₂ G₂)

@[simp] theorem memX_prod (x : X) (y : G₁ X Y × G₂ X Y) :
    MemX (prod o₁ o₂) x y ↔ MemX o₁ x y.1 ∨ MemX o₂ x y.2 :=
  ⟨fun ⟨q, e⟩ => match q, e with
    | .inl q, e => .inl ⟨q, e⟩
    | .inr q, e => .inr ⟨q, e⟩,
    fun h => h.elim (fun ⟨q, e⟩ => ⟨.inl q, e⟩) (fun ⟨q, e⟩ => ⟨.inr q, e⟩)⟩

@[simp] theorem memY_prod (t : Σ j, Y j) (y : G₁ X Y × G₂ X Y) :
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

@[simp] theorem memY_sum_inl (t : Σ j, Y j) (y : G₁ X Y) :
    MemY (sum o₁ o₂) t (.inl y) ↔ MemY o₁ t y :=
  ⟨fun ⟨q, e⟩ => ⟨q.down, e⟩, fun ⟨q, e⟩ => ⟨⟨q⟩, e⟩⟩

@[simp] theorem memY_sum_inr (t : Σ j, Y j) (y : G₂ X Y) :
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
@[simp] theorem memY_sum (t : Σ j, Y j) (y : G₁ X Y ⊕ G₂ X Y) :
    MemY (sum o₁ o₂) t y ↔
      (∃ a, y = .inl a ∧ MemY o₁ t a) ∨ ∃ b, y = .inr b ∧ MemY o₂ t b := by
  cases y with
  | inl a => simp only [memY_sum_inl, Sum.inl.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, or_false]
  | inr b => simp only [memY_sum_inr, Sum.inr.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, false_or]

end Forms

section Dependent

variable {A : Type a} {ShA : A → Type s} {PXA : ∀ x, ShA x → Type p}
  {PYA : ∀ x, ShA x → Type q} {pidxA : ∀ x (sh : ShA x), PYA x sh → J}
  {GA : A → Type u → (J → Type w) → Type v}
  (o : ∀ x, IOcc₂ (ShA x) (PXA x) (PYA x) (pidxA x) (GA x))

@[simp] theorem memX_pi (x : X) (k : ∀ a, GA a X Y) :
    MemX (pi A o) x k ↔ ∃ a, MemX (o a) x (k a) :=
  ⟨fun ⟨q, e⟩ => ⟨q.1, q.2, e⟩, fun ⟨a, q, e⟩ => ⟨⟨a, q⟩, e⟩⟩

@[simp] theorem memY_pi (t : Σ j, Y j) (k : ∀ a, GA a X Y) :
    MemY (pi A o) t k ↔ ∃ a, MemY (o a) t (k a) :=
  ⟨fun ⟨q, e⟩ => ⟨q.1, q.2, e⟩, fun ⟨a, q, e⟩ => ⟨⟨a, q⟩, e⟩⟩

@[simp] theorem memX_sigma (x : X) (z : Σ a, GA a X Y) :
    MemX (sigma A o) x z ↔ MemX (o z.1) x z.2 :=
  Iff.rfl

@[simp] theorem memY_sigma (t : Σ j, Y j) (z : Σ a, GA a X Y) :
    MemY (sigma A o) t z ↔ MemY (o z.1) t z.2 :=
  Iff.rfl

end Dependent

section DependentP

variable {P : Prop} {ShP : P → Type s} {PXP : ∀ h, ShP h → Type p}
  {PYP : ∀ h, ShP h → Type q} {pidxP : ∀ h (sh : ShP h), PYP h sh → J}
  {GP : P → Type u → (J → Type w) → Type v}
  (o : ∀ h, IOcc₂ (ShP h) (PXP h) (PYP h) (pidxP h) (GP h))

@[simp] theorem memX_piP (x : X) (k : ∀ h, GP h X Y) :
    MemX (piP P o) x k ↔ ∃ h, MemX (o h) x (k h) :=
  ⟨fun ⟨q, e⟩ => ⟨q.1, q.2, e⟩, fun ⟨h, q, e⟩ => ⟨⟨h, q⟩, e⟩⟩

@[simp] theorem memY_piP (t : Σ j, Y j) (k : ∀ h, GP h X Y) :
    MemY (piP P o) t k ↔ ∃ h, MemY (o h) t (k h) :=
  ⟨fun ⟨q, e⟩ => ⟨q.1, q.2, e⟩, fun ⟨h, q, e⟩ => ⟨⟨h, q⟩, e⟩⟩

end DependentP

section Comp

variable {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {PX' : Sh' → Type p'}
  {PY' : Sh' → Type q'} {pidx' : (sh : Sh') → PY' sh → J} {G : Type w' → Type v}
  {H : Type u → (J → Type w) → Type w'} (oG : Occ Sh Pos G) (oH : IOcc₂ Sh' PX' PY' pidx' H)

/-- Through a composite: a member of a member of the outer structure. -/
@[simp] theorem memX_comp (x : X) (y : G (H X Y)) :
    MemX (comp oG oH) x y ↔ ∃ z, Occ.Mem oG z y ∧ MemX oH x z :=
  ⟨fun ⟨r, e⟩ => ⟨_, ⟨r.1, rfl⟩, r.2, e⟩, fun ⟨_, ⟨q, e⟩, r, e'⟩ => by subst e; exact ⟨⟨q, r⟩, e'⟩⟩

/-- Through a composite: a member of a member of the outer structure. -/
@[simp] theorem memY_comp (t : Σ j, Y j) (y : G (H X Y)) :
    MemY (comp oG oH) t y ↔ ∃ z, Occ.Mem oG z y ∧ MemY oH t z :=
  ⟨fun ⟨r, e⟩ => ⟨_, ⟨r.1, rfl⟩, r.2, e⟩, fun ⟨_, ⟨q, e⟩, r, e'⟩ => by subst e; exact ⟨⟨q, r⟩, e'⟩⟩

end Comp

end MemCompute

/-! ### A member in `Y` with a property

What `simp` makes of `∃ t, MemY o t y ∧ P t`, the members in `Y` of a nested argument with a
property, before it computes `MemY` (`simp ↓`): the combinators are gone through first, so that
the member is eliminated at each leaf also where positions at several indices make a disjunction
(`List (α × T n × T (n + 1))`), which `MemY` computed first would leave under an existential. -/

section ExistsMem

variable {J : Type j} {X : Type u} {Y : J → Type w} (P : (Σ j, Y j) → Prop)

@[simp ↓] theorem exists_memY_const (A : Type v) (a : A) :
    (∃ t, MemY (const A) (X := X) t a ∧ P t) ↔ False :=
  ⟨fun ⟨_, h, _⟩ => not_memY_const A _ a h, False.elim⟩

@[simp ↓] theorem exists_memY_ofX {ShX : Type s} {PosX : ShX → Type p} {GX : Type u → Type v}
    (o : Occ ShX PosX GX) (y : GX X) : (∃ t, MemY (Y := Y) (ofX o) t y ∧ P t) ↔ False :=
  ⟨fun ⟨_, h, _⟩ => not_memY_ofX o _ y h, False.elim⟩

@[simp ↓] theorem exists_memY_ofY_hole (i : J) (y : Y i) :
    (∃ t, MemY (X := X) (ofY (IOcc.hole i)) t y ∧ P t) ↔ P ⟨i, y⟩ :=
  ⟨fun ⟨_, ⟨_, e⟩, h⟩ => e ▸ h, fun h => ⟨_, ⟨(), rfl⟩, h⟩⟩

@[simp ↓] theorem exists_memY_ofY_ofOcc {ShF : Type s} {PosF : ShF → Type q}
    {F : Type w → Type v} (oF : Occ ShF PosF F) (i : J) (y : F (Y i)) :
    (∃ t, MemY (X := X) (ofY (IOcc.ofOcc oF i)) t y ∧ P t) ↔
      ∃ z, Occ.Mem oF z y ∧ P ⟨i, z⟩ :=
  ⟨fun ⟨_, ⟨q, e⟩, h⟩ => ⟨_, ⟨q, rfl⟩, e ▸ h⟩, fun ⟨_, ⟨q, e⟩, h⟩ => ⟨_, ⟨q, by subst e; rfl⟩, h⟩⟩

@[simp ↓] theorem exists_memY_ofOcc₂ {Sh : Type s} {PX : Sh → Type p} {PY : Sh → Type q}
    {G : Type u → Type w → Type v} (o : Occ₂ Sh PX PY G) (i : J) (y : G X (Y i)) :
    (∃ t, MemY (ofOcc₂ o i) t y ∧ P t) ↔ ∃ z, Occ₂.MemY o z y ∧ P ⟨i, z⟩ :=
  ⟨fun ⟨_, ⟨q, e⟩, h⟩ => ⟨_, ⟨q, rfl⟩, e ▸ h⟩, fun ⟨_, ⟨q, e⟩, h⟩ => ⟨_, ⟨q, by subst e; rfl⟩, h⟩⟩

section Forms

variable {Sh₁ : Type s} {PX₁ : Sh₁ → Type p} {PY₁ : Sh₁ → Type q}
  {pidx₁ : (sh : Sh₁) → PY₁ sh → J} {Sh₂ : Type s'} {PX₂ : Sh₂ → Type p'} {PY₂ : Sh₂ → Type q'}
  {pidx₂ : (sh : Sh₂) → PY₂ sh → J}
  {G₁ : Type u → (J → Type w) → Type v} {G₂ : Type u → (J → Type w) → Type v'}
  (o₁ : IOcc₂ Sh₁ PX₁ PY₁ pidx₁ G₁) (o₂ : IOcc₂ Sh₂ PX₂ PY₂ pidx₂ G₂)

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
  {PYA : ∀ x, ShA x → Type q} {pidxA : ∀ x (sh : ShA x), PYA x sh → J}
  {GA : A → Type u → (J → Type w) → Type v}
  (o : ∀ x, IOcc₂ (ShA x) (PXA x) (PYA x) (pidxA x) (GA x))

@[simp ↓] theorem exists_memY_pi (k : ∀ a, GA a X Y) :
    (∃ t, MemY (pi A o) t k ∧ P t) ↔ ∃ a, ∃ t, MemY (o a) t (k a) ∧ P t := by
  simp only [memY_pi]
  exact ⟨fun ⟨t, ⟨a, h⟩, h'⟩ => ⟨a, t, h, h'⟩, fun ⟨a, t, h, h'⟩ => ⟨t, ⟨a, h⟩, h'⟩⟩

@[simp ↓] theorem exists_memY_sigma (z : Σ a, GA a X Y) :
    (∃ t, MemY (sigma A o) t z ∧ P t) ↔ ∃ t, MemY (o z.1) t z.2 ∧ P t :=
  Iff.rfl

end Dependent

@[simp ↓] theorem exists_memY_piP {Q : Prop} {ShP : Q → Type s} {PXP : ∀ h, ShP h → Type p}
    {PYP : ∀ h, ShP h → Type q} {pidxP : ∀ h (sh : ShP h), PYP h sh → J}
    {GP : Q → Type u → (J → Type w) → Type v}
    (o : ∀ h, IOcc₂ (ShP h) (PXP h) (PYP h) (pidxP h) (GP h)) (k : ∀ h, GP h X Y) :
    (∃ t, MemY (piP Q o) t k ∧ P t) ↔ ∃ h, ∃ t, MemY (o h) t (k h) ∧ P t := by
  simp only [memY_piP]
  exact ⟨fun ⟨t, ⟨h, m⟩, h'⟩ => ⟨h, t, m, h'⟩, fun ⟨h, t, m, h'⟩ => ⟨t, ⟨h, m⟩, h'⟩⟩

@[simp ↓] theorem exists_memY_comp {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'}
    {PX' : Sh' → Type p'} {PY' : Sh' → Type q'} {pidx' : (sh : Sh') → PY' sh → J}
    {G : Type w' → Type v} {H : Type u → (J → Type w) → Type w'} (oG : Occ Sh Pos G)
    (oH : IOcc₂ Sh' PX' PY' pidx' H) (y : G (H X Y)) :
    (∃ t, MemY (comp oG oH) t y ∧ P t) ↔
      ∃ z, Occ.Mem oG z y ∧ ∃ t, MemY oH t z ∧ P t := by
  simp only [memY_comp]
  exact ⟨fun ⟨t, ⟨z, hz, m⟩, h⟩ => ⟨z, hz, t, m, h⟩, fun ⟨z, hz, t, m, h⟩ => ⟨t, ⟨z, hz, m⟩, h⟩⟩

end ExistsMem

end IOcc₂

end Codata
