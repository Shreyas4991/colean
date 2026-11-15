import Mathlib.Data.List.Forall2
import Colean.PolyIso

/-!
# The model, nested occurrences: occurrence structures

*Spec.* Input: nothing but the syntax of an argument type, mirrored by the combinators. Output:
for a type expression `G` with holes, a structure `Occ Sh Pos G` (or `IOcc`), its `map` and
`Rel`, their laws, and computation lemmas through every combinator. Used by the command to
reduce a nested argument to a shape with positions, and by users to compute `map`/`Rel`.

A constructor argument whose type mentions the type being defined other than as a plain
occurrence or under a telescope of arrows, `children : List (T i)`, `p : T i × T j`,
`k : A → List (T i)`, is a *nested* argument. The command reduces it to the position family of
`Codata.lean` through the *occurrence structure* of its type: an equivalence
`G X ≃ Σ sh, Pos sh → X` between the argument type, as a function `G` of the occurrence `X`, and
a shape (everything outside the occurrences) with the contents at its positions. The shape is
non-recursive data of the constructor, the positions are recursive positions, and the generic
theory needs nothing new. The command keeps `G X` in the user-facing functor `F` and goes through
the equivalence in `toC`/`ofC`, with the action on functions `Occ.map` and the lifting to
relations `Occ.Rel`, whose laws are proved here once.

An occurrence structure is a value `Occ Sh Pos G`, *built* by the command by recursion on the
syntax of the argument type with the combinators below, one per way the occurrence can appear:
a constant (`const`), the occurrence itself (`hole`), a product (`prod`), a sum (`sum`), a
function from a constant type (`pi`, `piP` for a proposition), a dependent pair over a constant
type (`sigma`), and a named type constructor applied to an expression with occurrences (`comp`),
where the structure of the named constructor is a *leaf*: `Occ.ofIso F`, the structure of a
functor with a `PolyIso` instance (`PolyIso.lean`), which is what users provide. Instance search
happens at leaves only.

`map` and `Rel` go between two structures with the same shapes and positions, for `G` at one
universe and `G'` at another (`List.{u}` and `List.{v}`): this is what keeps the state of `corec`
and `fold` in any universe. The simp lemmas `map_list`, `map_prod`, `map_sum`, `map_comp`, …
compute `map` through the combinators back to the usual maps (`List.map`, pairs, `Sum.map`,
composition), the `rel_*` lemmas do the same for `Rel` (`rel_prod`, `rel_comp`, …, down to
`List.Forall₂` and `Option.Rel` at the leaves, a map on either side moved into the relation,
`rel_map_left`, and a value related to itself related at its members, `rel_self`), and
`forall_toC_*` turn "for every position" into membership or components; the members of a value
(`Mem`) are computed by `simp` the same way. The instances of `PolyIso.lean` for products, sums,
functions, dependent pairs and composites are these combinators by definition (`ofIso_prod`, …,
at the end, simp lemmas too), so a hypothesis at every position of a structure is one by
membership for the instance (`PolyIso.memRec`): this is how the recursor states the induction
hypotheses of nested arguments.

The indexed version `IOcc` is for occurrences of a *family*: every position carries an index,
`G X ≃ Σ sh, (q : Pos sh) → X (pidx sh q)`, so that occurrences at different indices may live
in one argument (`T i × T j`), and a functor on families with an `IPolyIso` instance is an
indexed leaf (`IOcc.ofIso`). `Occ` is the case of a single index; `IOcc.ofOcc` puts a plain
structure at a fixed index, `IOcc.reidx` and `Occ.ofI` reindex a family leaf, and `compC`,
`compI`, `Occ.compI` are the compositions across the two kinds. `simp` computes `IOcc.map` through
the combinators as `Occ.map` (`IOcc.map_prod`, …), and the map of an indexed structure whose
positions are all at one index is that of the plain one at that index (`IOcc.map_flat_sum`, …).
-/

universe u u' u'' v v' v'' w w' s s' p p' j k a

namespace Codata

/-- An occurrence structure on `G`: an equivalence `G X ≃ Σ sh, Pos sh → X` for every `X`, with
the shapes `Sh` and the positions `Pos` independent of `X`. The right-hand side is
`PFunctor.Obj ⟨Sh, Pos⟩ X`: `G` is the polynomial functor with these shapes and positions, and
`Occ.map` (defined through the equivalence) is its action on functions. -/
structure Occ (Sh : Type s) (Pos : Sh → Type p) (G : Type u → Type v) where
  equiv {X : Type u} : G X ≃ Σ sh, Pos sh → X

/-- An occurrence structure on a functor of families over `J`: every position carries an index.
-/
structure IOcc {J : Type j} (Sh : Type s) (Pos : Sh → Type p) (pidx : (sh : Sh) → Pos sh → J)
    (G : (J → Type u) → Type v) where
  equiv {X : J → Type u} : G X ≃ Σ sh, (q : Pos sh) → X (pidx sh q)

/-! ### The generic laws, plain -/

namespace Occ

variable {Sh : Type s} {Pos : Sh → Type p}
variable {G : Type u → Type v} (o : Occ Sh Pos G) {G' : Type u' → Type v'} (o' : Occ Sh Pos G')
  {G'' : Type u'' → Type v''} (o'' : Occ Sh Pos G'')
variable {X : Type u} {Y : Type u'} {Z : Type u''}

/-- The layer of a value: its shape and its contents. -/
def toC (x : G X) : Σ sh, Pos sh → X := o.equiv x

/-- The value of a layer. -/
def ofC (z : Σ sh, Pos sh → X) : G X := o.equiv.symm z

theorem ofC_toC (x : G X) : o.ofC (o.toC x) = x := o.equiv.symm_apply_apply x

theorem toC_ofC (z : Σ sh, Pos sh → X) : o.toC (o.ofC z) = z := o.equiv.apply_symm_apply z

/-- The action on functions, between two structures with the same shapes and positions. -/
def map (f : X → Y) (x : G X) : G' Y := o'.ofC ⟨(o.toC x).1, fun q => f ((o.toC x).2 q)⟩

/-- `ofC_toC` with the layer written out, as it appears in the generated `ofC (toC a)`. -/
theorem ofC_toC' (x : G X) : o.ofC ⟨(o.toC x).1, fun q => (o.toC x).2 q⟩ = x := o.ofC_toC x

theorem map_id (x : G X) : map o o (fun x => x) x = x := o.ofC_toC x

theorem map_id' (x : G X) : map o o id x = x := o.ofC_toC x

theorem map_ofC (f : X → Y) (sh : Sh) (c : Pos sh → X) :
    map o o' f (o.ofC ⟨sh, c⟩) = o'.ofC ⟨sh, fun q => f (c q)⟩ := by
  unfold map
  rw [toC_ofC]

/-- The layer of a mapped value: the same shape, the contents mapped. -/
theorem toC_map (f : X → Y) (x : G X) :
    o'.toC (map o o' f x) = ⟨(o.toC x).1, fun q => f ((o.toC x).2 q)⟩ := by
  unfold map
  rw [toC_ofC]

theorem map_map (g : Y → Z) (f : X → Y) (x : G X) :
    map o' o'' g (map o o' f x) = map o o'' (fun x => g (f x)) x := by
  unfold map
  rw [toC_ofC]

/-- The lifting to relations: the same shape and related contents. -/
def Rel (R : X → Y → Prop) (x : G X) (y : G' Y) : Prop :=
  ∃ (sh : Sh) (c : Pos sh → X) (c' : Pos sh → Y),
    o.toC x = ⟨sh, c⟩ ∧ o'.toC y = ⟨sh, c'⟩ ∧ ∀ q, R (c q) (c' q)

theorem rel_map (R : Y → Z → Prop) (f : X → Y) (g : X → Z) (x : G X)
    (h : ∀ x, R (f x) (g x)) : Rel o' o'' R (map o o' f x) (map o o'' g x) :=
  ⟨(o.toC x).1, fun q => f ((o.toC x).2 q), fun q => g ((o.toC x).2 q),
    by unfold map; rw [toC_ofC], by unfold map; rw [toC_ofC], fun q => h _⟩

/-- Two layers with the same shape and related contents are related. -/
theorem rel_intro {R : X → Y → Prop} (sh : Sh) (c : Pos sh → X) (c' : Pos sh → Y)
    (h : ∀ q, R (c q) (c' q)) : Rel o o' R (o.ofC ⟨sh, c⟩) (o'.ofC ⟨sh, c'⟩) :=
  ⟨sh, c, c', o.toC_ofC _, o'.toC_ofC _, h⟩

/-- A value is related to itself by a reflexive relation. -/
theorem rel_refl {R : X → X → Prop} (h : ∀ x, R x x) (x : G X) : Rel o o R x x :=
  ⟨(o.toC x).1, (o.toC x).2, (o.toC x).2, rfl, rfl, fun _ => h _⟩

/-- Related values are the two images of one value, once every related pair is: the elimination
of `Rel`, used by the generated `rel_ctorᵢ` lemmas with the pairs `{p // R p.1 p.2}` and, for
nested arguments, with the images given by the inner lemma. -/
theorem exists_map_of_rel' {R : X → Y → Prop} {W : Type u''} (fst : W → X) (snd : W → Y)
    (hR : ∀ x y, R x y → ∃ w, fst w = x ∧ snd w = y) {x : G X} {y : G' Y} (h : Rel o o' R x y) :
    ∃ z : G'' W, map o'' o fst z = x ∧ map o'' o' snd z = y := by
  obtain ⟨sh, c, c', hx, hy, hR'⟩ := h
  choose w hw using fun q => hR _ _ (hR' q)
  refine ⟨o''.ofC ⟨sh, w⟩, ?_, ?_⟩
  · rw [map_ofC, ← o.ofC_toC x, hx]
    exact congrArg (fun c => o.ofC ⟨sh, c⟩) (funext fun q => (hw q).1)
  · rw [map_ofC, ← o'.ofC_toC y, hy]
    exact congrArg (fun c => o'.ofC ⟨sh, c⟩) (funext fun q => (hw q).2)

theorem exists_map_of_rel {G'' : Type (max u u') → Type v''} (o'' : Occ Sh Pos G'')
    {R : X → Y → Prop} {x : G X} {y : G' Y} (h : Rel o o' R x y) :
    ∃ z : G'' {p : X × Y // R p.1 p.2},
      map o'' o (fun p => p.1.1) z = x ∧ map o'' o' (fun p => p.1.2) z = y :=
  exists_map_of_rel' o o' o'' _ _ (fun x y h => ⟨⟨(x, y), h⟩, rfl, rfl⟩) h

/-- The layer of a value, on the contents: `toC x = ⟨(toC x).1, fun q => (toC x).2 q⟩`. -/
theorem toC_eta (x : G X) : o.toC x = ⟨(o.toC x).1, fun q => (o.toC x).2 q⟩ := rfl

end Occ

/-! ### The generic laws, indexed -/

namespace IOcc

variable {J : Type j} {Sh : Type s} {Pos : Sh → Type p} {pidx : (sh : Sh) → Pos sh → J}
variable {G : (J → Type u) → Type v} (o : IOcc Sh Pos pidx G)
  {G' : (J → Type u') → Type v'} (o' : IOcc Sh Pos pidx G')
  {G'' : (J → Type u'') → Type v''} (o'' : IOcc Sh Pos pidx G'')
variable {X : J → Type u} {Y : J → Type u'} {Z : J → Type u''}

def toC (x : G X) : Σ sh, (q : Pos sh) → X (pidx sh q) := o.equiv x

def ofC (z : Σ sh, (q : Pos sh) → X (pidx sh q)) : G X := o.equiv.symm z

theorem ofC_toC (x : G X) : o.ofC (o.toC x) = x := o.equiv.symm_apply_apply x

theorem toC_ofC (z : Σ sh, (q : Pos sh) → X (pidx sh q)) : o.toC (o.ofC z) = z :=
  o.equiv.apply_symm_apply z

def map (f : ∀ j, X j → Y j) (x : G X) : G' Y :=
  o'.ofC ⟨(o.toC x).1, fun q => f _ ((o.toC x).2 q)⟩

theorem ofC_toC' (x : G X) : o.ofC ⟨(o.toC x).1, fun q => (o.toC x).2 q⟩ = x := o.ofC_toC x

theorem map_id (x : G X) : map o o (fun _ x => x) x = x := o.ofC_toC x

theorem map_id' (x : G X) : map o o (fun _ => id) x = x := o.ofC_toC x

/-- The map from a family to an equal one, by a function that leaves every element as it is,
leaves a value as it is. -/
theorem map_heq_self {Y : J → Type u} (h : X = Y) (f : ∀ j, X j → Y j)
    (hf : ∀ j x, HEq (f j x) x) (x : G X) : HEq (map o o f x) x := by
  subst h
  obtain rfl : f = fun _ x => x := funext fun j => funext fun x => eq_of_heq (hf j x)
  exact heq_of_eq (map_id o x)

theorem map_ofC (f : ∀ j, X j → Y j) (sh : Sh) (c : (q : Pos sh) → X (pidx sh q)) :
    map o o' f (o.ofC ⟨sh, c⟩) = o'.ofC ⟨sh, fun q => f _ (c q)⟩ := by
  unfold map
  rw [toC_ofC]

theorem toC_map (f : ∀ j, X j → Y j) (x : G X) :
    o'.toC (map o o' f x) = ⟨(o.toC x).1, fun q => f _ ((o.toC x).2 q)⟩ := by
  unfold map
  rw [toC_ofC]

theorem map_map (g : ∀ j, Y j → Z j) (f : ∀ j, X j → Y j) (x : G X) :
    map o' o'' g (map o o' f x) = map o o'' (fun j x => g j (f j x)) x := by
  unfold map
  rw [toC_ofC]

def Rel (R : ∀ j, X j → Y j → Prop) (x : G X) (y : G' Y) : Prop :=
  ∃ (sh : Sh) (c : (q : Pos sh) → X (pidx sh q)) (c' : (q : Pos sh) → Y (pidx sh q)),
    o.toC x = ⟨sh, c⟩ ∧ o'.toC y = ⟨sh, c'⟩ ∧ ∀ q, R _ (c q) (c' q)

theorem rel_map (R : ∀ j, Y j → Z j → Prop) (f : ∀ j, X j → Y j) (g : ∀ j, X j → Z j) (x : G X)
    (h : ∀ j x, R j (f j x) (g j x)) : Rel o' o'' R (map o o' f x) (map o o'' g x) :=
  ⟨(o.toC x).1, fun q => f _ ((o.toC x).2 q), fun q => g _ ((o.toC x).2 q),
    by unfold map; rw [toC_ofC], by unfold map; rw [toC_ofC], fun q => h _ _⟩

theorem rel_intro {R : ∀ j, X j → Y j → Prop} (sh : Sh) (c : (q : Pos sh) → X (pidx sh q))
    (c' : (q : Pos sh) → Y (pidx sh q)) (h : ∀ q, R _ (c q) (c' q)) :
    Rel o o' R (o.ofC ⟨sh, c⟩) (o'.ofC ⟨sh, c'⟩) :=
  ⟨sh, c, c', o.toC_ofC _, o'.toC_ofC _, h⟩

/-- A value is related to itself by a reflexive relation. -/
theorem rel_refl {R : ∀ j, X j → X j → Prop} (h : ∀ j x, R j x x) (x : G X) : Rel o o R x x :=
  ⟨(o.toC x).1, (o.toC x).2, (o.toC x).2, rfl, rfl, fun _ => h _ _⟩

theorem exists_map_of_rel' {R : ∀ j, X j → Y j → Prop} {W : J → Type u''}
    (fst : ∀ j, W j → X j) (snd : ∀ j, W j → Y j)
    (hR : ∀ j x y, R j x y → ∃ w, fst j w = x ∧ snd j w = y) {x : G X} {y : G' Y}
    (h : Rel o o' R x y) : ∃ z : G'' W, map o'' o fst z = x ∧ map o'' o' snd z = y := by
  obtain ⟨sh, c, c', hx, hy, hR'⟩ := h
  choose w hw using fun q => hR _ _ _ (hR' q)
  refine ⟨o''.ofC ⟨sh, w⟩, ?_, ?_⟩
  · rw [map_ofC, ← o.ofC_toC x, hx]
    exact congrArg (fun c => o.ofC ⟨sh, c⟩) (funext fun q => (hw q).1)
  · rw [map_ofC, ← o'.ofC_toC y, hy]
    exact congrArg (fun c => o'.ofC ⟨sh, c⟩) (funext fun q => (hw q).2)

theorem exists_map_of_rel {G'' : (J → Type (max u u')) → Type v''} (o'' : IOcc Sh Pos pidx G'')
    {R : ∀ j, X j → Y j → Prop} {x : G X} {y : G' Y} (h : Rel o o' R x y) :
    ∃ z : G'' (fun j => {p : X j × Y j // R j p.1 p.2}),
      map o'' o (fun _ p => p.1.1) z = x ∧ map o'' o' (fun _ p => p.1.2) z = y :=
  exists_map_of_rel' o o' o'' _ _ (fun _ x y h => ⟨⟨(x, y), h⟩, rfl, rfl⟩) h

/-- The index of a position, as a function of the structure (for generated code). -/
abbrev idx (_ : IOcc Sh Pos pidx G) (sh : Sh) (q : Pos sh) : J := pidx sh q

end IOcc

/-! ### The leaves: the structures of `PolyIso` -/

/-- The structure of a functor with a `PolyIso` instance: the leaf of the structures the command
builds. -/
def Occ.ofIso (F : Type u → Type v) {Sh : Type s} {Pos : Sh → Type p} [h : PolyIso F Sh Pos] :
    Occ Sh Pos F := ⟨h.equiv⟩

/-- The structure of a functor on families with an `IPolyIso` instance. -/
def IOcc.ofIso {J : Type j} (G : (J → Type u) → Type v) {Sh : Type s} {Pos : Sh → Type p}
    {pidx : (sh : Sh) → Pos sh → J} [h : IPolyIso G Sh Pos pidx] : IOcc Sh Pos pidx G := ⟨h.equiv⟩

/-- The map of a family leaf is the intended one. -/
theorem IOcc.map_ofIso {J : Type j} {G : (J → Type u) → Type v}
    {G' : (J → Type u') → Type v'} {Sh : Type s} {Pos : Sh → Type p}
    {pidx : (sh : Sh) → Pos sh → J} [hG : IPolyIso G Sh Pos pidx] [hG' : IPolyIso G' Sh Pos pidx]
    [IPolyMap G G'] {X : J → Type u} {Y : J → Type u'} (f : ∀ j, X j → Y j) (x : G X) :
    map (ofIso G) (ofIso G') f x = @IPolyMap.map _ _ _ _ _ _ hG hG' _ _ _ f x := by
  refine (hG'.equiv.symm_apply_eq.mpr ?_)
  exact (@IPolyMap.equiv_map _ _ _ _ _ _ hG hG' _ _ _ f x).symm

namespace Occ

variable {X : Type u} {Y : Type u'}

/-- The map of a leaf is the intended one: this is what `PolyMap` is for. -/
theorem map_ofIso {F : Type u → Type v} {F' : Type u' → Type v'} {Sh : Type s}
    {Pos : Sh → Type p} [hF : PolyIso F Sh Pos] [hF' : PolyIso F' Sh Pos] [PolyMap F F']
    (f : X → Y) (x : F X) :
    map (ofIso F) (ofIso F') f x = @PolyMap.map _ _ _ _ hF hF' _ _ _ f x := by
  refine (hF'.equiv.symm_apply_eq.mpr ?_)
  exact (@PolyMap.equiv_map _ _ _ _ hF hF' _ _ _ f x).symm

/-- Lists. -/
abbrev list : Occ Nat Fin List.{u} := ofIso List

@[simp] theorem toC_list (l : List X) : list.toC l = ⟨l.length, l.get⟩ := rfl

@[simp] theorem ofC_list {n : Nat} (f : Fin n → X) : list.ofC ⟨n, f⟩ = List.ofFn f := rfl

@[simp] theorem map_list (f : X → Y) (l : List X) : map list list f l = l.map f :=
  map_ofIso f l

/-- The element at a position of a list is a member. -/
theorem toC_list_mem (l : List X) (q : Fin (list.toC l).1) : (list.toC l).2 q ∈ l :=
  List.get_mem l q

/-- A member of a list is the element at some position. -/
theorem mem_toC_list {l : List X} {x : X} (hx : x ∈ l) : ∃ q, (list.toC l).2 q = x :=
  List.mem_iff_get.mp hx

/-- The induction hypothesis of a nested list, in terms of membership. -/
theorem forall_toC_list {P : X → Prop} (l : List X) :
    (∀ q, P ((list.toC l).2 q)) ↔ ∀ x ∈ l, P x :=
  ⟨fun h x hx => by obtain ⟨q, rfl⟩ := mem_toC_list hx; exact h q,
    fun h q => h _ (toC_list_mem l q)⟩

/-- Options. -/
abbrev option : Occ Bool OptionPos Option.{u} := ofIso Option

theorem toC_option_none : option.toC (none : Option X) = ⟨false, fun q => nomatch q⟩ := rfl

theorem toC_option_some (x : X) : option.toC (some x) = ⟨true, fun _ => x⟩ := rfl

@[simp] theorem map_option (f : X → Y) (x : Option X) : map option option f x = x.map f :=
  map_ofIso f x

/-- Arrays. -/
abbrev array : Occ Nat Fin Array.{u} := ofIso Array

@[simp] theorem map_array (f : X → Y) (a : Array X) : map array array f a = a.map f :=
  map_ofIso f a

/-! ### The combinators, plain

Every combinator is defined by its two maps directly, so that `toC`, `ofC` and `map` compute
through it by `rfl` (the `toC_*` and `map_*` lemmas below). The inverse laws rewrite
`toC (ofC z)` in dependent positions, which `rw` cannot do; the layer is generalised first, or
the extensionality lemmas `pi_ext`, `piP_ext`, `comp_ext` apply. These, `sumRec` and `SumPos`
are in `PolyIso.lean`, shared with the instances of the same forms. -/

/-- A constant: the value is the shape, there are no positions. -/
def const (A : Type v) : Occ A (fun _ => Empty) (fun _ : Type u => A) where
  equiv := {
    toFun a := ⟨a, Empty.elim⟩
    invFun z := z.1
    left_inv _ := rfl
    right_inv := fun ⟨_, _⟩ => congrArg _ (funext fun x => x.elim) }

/-- The occurrence itself: one shape, one position. -/
def hole : Occ Unit (fun _ => Unit) (fun X : Type u => X) where
  equiv := {
    toFun x := ⟨(), fun _ => x⟩
    invFun z := z.2 ()
    left_inv _ := rfl
    right_inv _ := rfl }

section Combinators

variable {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p} {Sh₂ : Type s'} {Pos₂ : Sh₂ → Type p'}
  {G₁ : Type u → Type v} {G₂ : Type u → Type v'}

/-- A product of two expressions with occurrences: a pair of shapes, the sum of the positions.
-/
def prod (o₁ : Occ Sh₁ Pos₁ G₁) (o₂ : Occ Sh₂ Pos₂ G₂) :
    Occ (Sh₁ × Sh₂) (fun sh => Pos₁ sh.1 ⊕ Pos₂ sh.2) (fun X => G₁ X × G₂ X) where
  equiv := {
    toFun x := ⟨((o₁.toC x.1).1, (o₂.toC x.2).1), sumRec (o₁.toC x.1).2 (o₂.toC x.2).2⟩
    invFun z := (o₁.ofC ⟨z.1.1, fun q => z.2 (.inl q)⟩, o₂.ofC ⟨z.1.2, fun q => z.2 (.inr q)⟩)
    left_inv x := by
      show (o₁.ofC ⟨(o₁.toC x.1).1, fun q => (o₁.toC x.1).2 q⟩,
        o₂.ofC ⟨(o₂.toC x.2).1, fun q => (o₂.toC x.2).2 q⟩) = x
      rw [ofC_toC', ofC_toC']
    right_inv := fun ⟨⟨s₁, s₂⟩, c⟩ => by
      dsimp only
      generalize h₁ : o₁.toC (o₁.ofC ⟨s₁, fun q => c (.inl q)⟩) = z₁
      generalize h₂ : o₂.toC (o₂.ofC ⟨s₂, fun q => c (.inr q)⟩) = z₂
      rw [toC_ofC] at h₁ h₂
      subst h₁ h₂
      exact congrArg (Sigma.mk (s₁, s₂)) (funext fun q => by cases q <;> rfl) }

/-- A sum of two expressions with occurrences: a shape of either side, its positions. -/
def sum (o₁ : Occ Sh₁ Pos₁ G₁) (o₂ : Occ Sh₂ Pos₂ G₂) :
    Occ (Sh₁ ⊕ Sh₂) (SumPos Pos₁ Pos₂) (fun X => G₁ X ⊕ G₂ X) where
  equiv := {
    toFun
      | .inl x => ⟨.inl (o₁.toC x).1, fun q => (o₁.toC x).2 q.down⟩
      | .inr x => ⟨.inr (o₂.toC x).1, fun q => (o₂.toC x).2 q.down⟩
    invFun
      | ⟨.inl sh, c⟩ => .inl (o₁.ofC ⟨sh, fun q => c ⟨q⟩⟩)
      | ⟨.inr sh, c⟩ => .inr (o₂.ofC ⟨sh, fun q => c ⟨q⟩⟩)
    left_inv
      | .inl x => by
        show Sum.inl (o₁.ofC ⟨(o₁.toC x).1, fun q => (o₁.toC x).2 q⟩) = _
        rw [ofC_toC']
      | .inr x => by
        show Sum.inr (o₂.ofC ⟨(o₂.toC x).1, fun q => (o₂.toC x).2 q⟩) = _
        rw [ofC_toC']
    right_inv
      | ⟨.inl sh, c⟩ => by
        dsimp only
        generalize h : o₁.toC (o₁.ofC ⟨sh, fun q => c ⟨q⟩⟩) = z
        rw [toC_ofC] at h
        subst h
        rfl
      | ⟨.inr sh, c⟩ => by
        dsimp only
        generalize h : o₂.toC (o₂.ofC ⟨sh, fun q => c ⟨q⟩⟩) = z
        rw [toC_ofC] at h
        subst h
        rfl }

end Combinators

section Dependent

variable (A : Type a) {ShA : A → Type s} {PosA : ∀ x, ShA x → Type p} {GA : A → Type u → Type v}

/-- A function from a constant type: a shape at every point, a point with a position there. -/
def pi (o : ∀ x, Occ (ShA x) (PosA x) (GA x)) :
    Occ (∀ x : A, ShA x) (fun sh => Σ x, PosA x (sh x)) (fun X => ∀ x, GA x X) where
  equiv := {
    toFun k := ⟨fun x => ((o x).toC (k x)).1, fun q => ((o q.1).toC (k q.1)).2 q.2⟩
    invFun z x := (o x).ofC ⟨z.1 x, fun q => z.2 ⟨x, q⟩⟩
    left_inv k := funext fun x => (o x).ofC_toC' (k x)
    right_inv := fun ⟨sh, c⟩ => pi_ext _ sh c fun x => (o x).toC_ofC _ }

/-- A dependent pair over a constant type: a point with a shape there, its positions. -/
def sigma (o : ∀ x, Occ (ShA x) (PosA x) (GA x)) :
    Occ (Σ x : A, ShA x) (fun sh => PosA sh.1 sh.2) (fun X => Σ x, GA x X) where
  equiv := {
    toFun z := ⟨⟨z.1, ((o z.1).toC z.2).1⟩, ((o z.1).toC z.2).2⟩
    invFun w := ⟨w.1.1, (o w.1.1).ofC ⟨w.1.2, w.2⟩⟩
    left_inv := fun ⟨x, y⟩ => by
      show (⟨x, (o x).ofC ((o x).toC y)⟩ : Σ x, GA x _) = _
      rw [ofC_toC]
    right_inv := fun ⟨⟨x, sh⟩, c⟩ => by
      dsimp only
      generalize h : (o x).toC ((o x).ofC ⟨sh, c⟩) = z
      rw [toC_ofC] at h
      subst h
      rfl }

end Dependent

section Prop'

variable (P : Prop) {ShP : P → Type s} {PosP : ∀ h, ShP h → Type p} {GP : P → Type u → Type v}

/-- A function from a proposition. -/
def piP (o : ∀ h, Occ (ShP h) (PosP h) (GP h)) :
    Occ (∀ h : P, ShP h) (fun sh => Σ' h, PosP h (sh h)) (fun X => ∀ h, GP h X) where
  equiv := {
    toFun k := ⟨fun h => ((o h).toC (k h)).1, fun q => ((o q.1).toC (k q.1)).2 q.2⟩
    invFun z h := (o h).ofC ⟨z.1 h, fun q => z.2 ⟨h, q⟩⟩
    left_inv k := funext fun h => (o h).ofC_toC' (k h)
    right_inv := fun ⟨sh, c⟩ => piP_ext _ sh c fun h => (o h).toC_ofC _ }

end Prop'

section Comp

variable {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {Pos' : Sh' → Type p'}

/-- A named type constructor applied to an expression with occurrences: the shapes are a shape
of the outer structure with a shape of the inner one at each of its positions, the positions a
position of the outer with a position of the inner shape there. -/
def comp {G : Type u' → Type v} (oG : Occ Sh Pos G) {H : Type u → Type u'} (oH : Occ Sh' Pos' H) :
    Occ (Σ sh, Pos sh → Sh') (fun z => Σ q, Pos' (z.2 q)) (fun X => G (H X)) where
  equiv {X} := {
    toFun x := ⟨⟨(oG.toC x).1, fun q => (oH.toC ((oG.toC x).2 q)).1⟩,
      fun r => (oH.toC ((oG.toC x).2 r.1)).2 r.2⟩
    invFun z := oG.ofC ⟨z.1.1, fun q => oH.ofC ⟨z.1.2 q, fun r => z.2 ⟨q, r⟩⟩⟩
    left_inv x := by
      show oG.ofC ⟨(oG.toC x).1, fun q => oH.ofC ⟨(oH.toC ((oG.toC x).2 q)).1,
        fun r => (oH.toC ((oG.toC x).2 q)).2 r⟩⟩ = x
      simp only [ofC_toC']
    right_inv := fun ⟨⟨sh, t⟩, c⟩ => by
      dsimp only
      generalize hU : oG.toC (oG.ofC ⟨sh, fun q => oH.ofC ⟨t q, fun r => c ⟨q, r⟩⟩⟩) = U
      rw [toC_ofC] at hU
      subst hU
      dsimp only at c
      refine comp_ext (Sh' := fun _ _ => Sh') (Pos' := fun _ _ s => Pos' s) (X := fun _ _ _ _ => X) sh _ t c ?_
      intro q
      exact oH.toC_ofC _ }

end Comp

end Occ

/-! ### The combinators, indexed -/

namespace IOcc

variable {J : Type j} {K : Type k}

/-- A constant, as a functor of families. -/
def const (A : Type v) : IOcc (J := J) A (fun _ => Empty) (fun _ e => e.elim) (fun _ => A) where
  equiv := {
    toFun a := ⟨a, fun e => e.elim⟩
    invFun z := z.1
    left_inv _ := rfl
    right_inv := fun ⟨_, _⟩ => congrArg _ (funext fun x => x.elim) }

/-- The occurrence of the family at an index. -/
def hole (i : J) : IOcc Unit (fun _ => Unit) (fun _ _ => i) (fun X : J → Type u => X i) where
  equiv := {
    toFun x := ⟨(), fun _ => x⟩
    invFun z := z.2 ()
    left_inv _ := rfl
    right_inv _ := rfl }

section Reindex

variable {Sh : Type s} {Pos : Sh → Type p}

/-- A plain structure at a fixed index of the family. -/
def ofOcc {G : Type u → Type v} (o : Occ Sh Pos G) (i : J) :
    IOcc Sh Pos (fun _ _ => i) (fun X : J → Type u => G (X i)) :=
  ⟨o.equiv⟩

/-- A structure on families over `K`, at a family reindexed along `g : K → J`. -/
def reidx {pidx : (sh : Sh) → Pos sh → K} {G : (K → Type u) → Type v} (o : IOcc Sh Pos pidx G)
    (g : K → J) :
    IOcc Sh Pos (fun sh q => g (pidx sh q)) (fun X : J → Type u => G fun k => X (g k)) :=
  ⟨o.equiv⟩

/-- The map of a plain structure at a fixed index is its map at that index: with it, `simp`
reaches the rules of a declared family nested at its own index (`Vec (T n) n`). -/
@[simp] theorem map_ofOcc {G : Type u → Type v} {G' : Type u' → Type v'} (o : Occ Sh Pos G)
    (o' : Occ Sh Pos G') (i : J) {X : J → Type u} {Y : J → Type u'} (f : ∀ j, X j → Y j)
    (x : G (X i)) : map (ofOcc o i) (ofOcc o' i) f x = Occ.map o o' (f i) x := rfl

end Reindex

section Combinators

variable {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p} {pidx₁ : (sh : Sh₁) → Pos₁ sh → J}
  {Sh₂ : Type s'} {Pos₂ : Sh₂ → Type p'} {pidx₂ : (sh : Sh₂) → Pos₂ sh → J}
  {G₁ : (J → Type u) → Type v} {G₂ : (J → Type u) → Type v'}

/-- A product: a pair of shapes, the sum of the positions. -/
def prod (o₁ : IOcc Sh₁ Pos₁ pidx₁ G₁) (o₂ : IOcc Sh₂ Pos₂ pidx₂ G₂) :
    IOcc (Sh₁ × Sh₂) (fun sh => Pos₁ sh.1 ⊕ Pos₂ sh.2)
      (fun sh q => Sum.elim (pidx₁ sh.1) (pidx₂ sh.2) q) (fun X => G₁ X × G₂ X) where
  equiv := {
    toFun x := ⟨((o₁.toC x.1).1, (o₂.toC x.2).1), Occ.sumRec (o₁.toC x.1).2 (o₂.toC x.2).2⟩
    invFun z := (o₁.ofC ⟨z.1.1, fun q => z.2 (.inl q)⟩, o₂.ofC ⟨z.1.2, fun q => z.2 (.inr q)⟩)
    left_inv x := by
      show (o₁.ofC ⟨(o₁.toC x.1).1, fun q => (o₁.toC x.1).2 q⟩,
        o₂.ofC ⟨(o₂.toC x.2).1, fun q => (o₂.toC x.2).2 q⟩) = x
      rw [ofC_toC', ofC_toC']
    right_inv := fun ⟨⟨s₁, s₂⟩, c⟩ => by
      dsimp only
      generalize h₁ : o₁.toC (o₁.ofC ⟨s₁, fun q => c (.inl q)⟩) = z₁
      generalize h₂ : o₂.toC (o₂.ofC ⟨s₂, fun q => c (.inr q)⟩) = z₂
      rw [toC_ofC] at h₁ h₂
      subst h₁ h₂
      exact congrArg (Sigma.mk (s₁, s₂)) (funext fun q => by cases q <;> rfl) }

/-- A sum: a shape of either side, its positions (lifted to one universe). -/
def sum (o₁ : IOcc Sh₁ Pos₁ pidx₁ G₁) (o₂ : IOcc Sh₂ Pos₂ pidx₂ G₂) :
    IOcc (Sh₁ ⊕ Sh₂) (Occ.SumPos Pos₁ Pos₂) (sumIdx pidx₁ pidx₂) (fun X => G₁ X ⊕ G₂ X) where
  equiv := {
    toFun
      | .inl x => ⟨.inl (o₁.toC x).1, fun q => (o₁.toC x).2 q.down⟩
      | .inr x => ⟨.inr (o₂.toC x).1, fun q => (o₂.toC x).2 q.down⟩
    invFun
      | ⟨.inl sh, c⟩ => .inl (o₁.ofC ⟨sh, fun q => c ⟨q⟩⟩)
      | ⟨.inr sh, c⟩ => .inr (o₂.ofC ⟨sh, fun q => c ⟨q⟩⟩)
    left_inv
      | .inl x => by
        show Sum.inl (o₁.ofC ⟨(o₁.toC x).1, fun q => (o₁.toC x).2 q⟩) = _
        rw [ofC_toC']
      | .inr x => by
        show Sum.inr (o₂.ofC ⟨(o₂.toC x).1, fun q => (o₂.toC x).2 q⟩) = _
        rw [ofC_toC']
    right_inv
      | ⟨.inl sh, c⟩ => by
        dsimp only
        generalize h : o₁.toC (o₁.ofC ⟨sh, fun q => c ⟨q⟩⟩) = z
        rw [toC_ofC] at h
        subst h
        rfl
      | ⟨.inr sh, c⟩ => by
        dsimp only
        generalize h : o₂.toC (o₂.ofC ⟨sh, fun q => c ⟨q⟩⟩) = z
        rw [toC_ofC] at h
        subst h
        rfl }

end Combinators

section Dependent

variable (A : Type a) {ShA : A → Type s} {PosA : ∀ x, ShA x → Type p}
  {pidxA : ∀ x (sh : ShA x), PosA x sh → J} {GA : A → (J → Type u) → Type v}

/-- A function from a constant type. -/
def pi (o : ∀ x, IOcc (ShA x) (PosA x) (pidxA x) (GA x)) :
    IOcc (∀ x : A, ShA x) (fun sh => Σ x, PosA x (sh x)) (fun sh q => pidxA q.1 (sh q.1) q.2)
      (fun X => ∀ x, GA x X) where
  equiv := {
    toFun k := ⟨fun x => ((o x).toC (k x)).1, fun q => ((o q.1).toC (k q.1)).2 q.2⟩
    invFun z x := (o x).ofC ⟨z.1 x, fun q => z.2 ⟨x, q⟩⟩
    left_inv k := funext fun x => (o x).ofC_toC' (k x)
    right_inv := fun ⟨sh, c⟩ => Occ.pi_ext _ sh c fun x => (o x).toC_ofC _ }

/-- A dependent pair over a constant type. -/
def sigma (o : ∀ x, IOcc (ShA x) (PosA x) (pidxA x) (GA x)) :
    IOcc (Σ x : A, ShA x) (fun sh => PosA sh.1 sh.2) (fun sh q => pidxA sh.1 sh.2 q)
      (fun X => Σ x, GA x X) where
  equiv := {
    toFun z := ⟨⟨z.1, ((o z.1).toC z.2).1⟩, ((o z.1).toC z.2).2⟩
    invFun w := ⟨w.1.1, (o w.1.1).ofC ⟨w.1.2, w.2⟩⟩
    left_inv := fun ⟨x, y⟩ => by
      show (⟨x, (o x).ofC ((o x).toC y)⟩ : Σ x, GA x _) = _
      rw [ofC_toC]
    right_inv := fun ⟨⟨x, sh⟩, c⟩ => by
      dsimp only
      generalize h : (o x).toC ((o x).ofC ⟨sh, c⟩) = z
      rw [toC_ofC] at h
      subst h
      rfl }

end Dependent

section Prop'

variable (P : Prop) {ShP : P → Type s} {PosP : ∀ h, ShP h → Type p}
  {pidxP : ∀ h (sh : ShP h), PosP h sh → J} {GP : P → (J → Type u) → Type v}

/-- A function from a proposition. -/
def piP (o : ∀ h, IOcc (ShP h) (PosP h) (pidxP h) (GP h)) :
    IOcc (∀ h : P, ShP h) (fun sh => Σ' h, PosP h (sh h)) (fun sh q => pidxP q.1 (sh q.1) q.2)
      (fun X => ∀ h, GP h X) where
  equiv := {
    toFun k := ⟨fun h => ((o h).toC (k h)).1, fun q => ((o q.1).toC (k q.1)).2 q.2⟩
    invFun z h := (o h).ofC ⟨z.1 h, fun q => z.2 ⟨h, q⟩⟩
    left_inv k := funext fun h => (o h).ofC_toC' (k h)
    right_inv := fun ⟨sh, c⟩ => Occ.piP_ext _ sh c fun h => (o h).toC_ofC _ }

end Prop'

section Comp

variable {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {Pos' : Sh' → Type p'}

/-- A plain type constructor applied to an expression with occurrences of the family. -/
def compC {G : Type u' → Type v} (oG : Occ Sh Pos G) {pidx' : (sh : Sh') → Pos' sh → J}
    {H : (J → Type u) → Type u'} (oH : IOcc Sh' Pos' pidx' H) :
    IOcc (Σ sh, Pos sh → Sh') (fun z => Σ q, Pos' (z.2 q)) (fun z r => pidx' (z.2 r.1) r.2)
      (fun X => G (H X)) where
  equiv {X} := {
    toFun x := ⟨⟨(oG.toC x).1, fun q => (oH.toC ((oG.toC x).2 q)).1⟩,
      fun r => (oH.toC ((oG.toC x).2 r.1)).2 r.2⟩
    invFun z := oG.ofC ⟨z.1.1, fun q => oH.ofC ⟨z.1.2 q, fun r => z.2 ⟨q, r⟩⟩⟩
    left_inv x := by
      show oG.ofC ⟨(oG.toC x).1, fun q => oH.ofC ⟨(oH.toC ((oG.toC x).2 q)).1,
        fun r => (oH.toC ((oG.toC x).2 q)).2 r⟩⟩ = x
      simp only [ofC_toC', Occ.ofC_toC']
    right_inv := fun ⟨⟨sh, t⟩, c⟩ => by
      dsimp only
      generalize hU : oG.toC (oG.ofC ⟨sh, fun q => oH.ofC ⟨t q, fun r => c ⟨q, r⟩⟩⟩) = U
      rw [Occ.toC_ofC] at hU
      subst hU
      dsimp only at c
      refine Occ.comp_ext (Sh' := fun _ _ => Sh') (Pos' := fun _ _ s => Pos' s)
        (X := fun _ _ s r => X (pidx' s r)) sh _ t c ?_
      intro q
      exact oH.toC_ofC _ }

variable {pidx : (sh : Sh) → Pos sh → K}

/-- A functor of families over `K` applied to a family of expressions with occurrences of the
family over `J`. -/
def compI {G : (K → Type u') → Type v} (oG : IOcc Sh Pos pidx G) {Sh' : K → Type s'}
    {Pos' : ∀ k, Sh' k → Type p'} {pidx' : ∀ k (sh : Sh' k), Pos' k sh → J}
    {H : K → (J → Type u) → Type u'} (oH : ∀ k, IOcc (Sh' k) (Pos' k) (pidx' k) (H k)) :
    IOcc (Σ sh, (q : Pos sh) → Sh' (pidx sh q)) (fun z => Σ q, Pos' _ (z.2 q))
      (fun z r => pidx' _ (z.2 r.1) r.2) (fun X => G fun k => H k X) where
  equiv {X} := {
    toFun x := ⟨⟨(oG.toC x).1, fun q => ((oH _).toC ((oG.toC x).2 q)).1⟩,
      fun r => ((oH _).toC ((oG.toC x).2 r.1)).2 r.2⟩
    invFun z := oG.ofC ⟨z.1.1, fun q => (oH _).ofC ⟨z.1.2 q, fun r => z.2 ⟨q, r⟩⟩⟩
    left_inv x := by
      show oG.ofC ⟨(oG.toC x).1, fun q => (oH _).ofC ⟨((oH _).toC ((oG.toC x).2 q)).1,
        fun r => ((oH _).toC ((oG.toC x).2 q)).2 r⟩⟩ = x
      simp only [ofC_toC']
    right_inv := fun ⟨⟨sh, t⟩, c⟩ => by
      dsimp only
      generalize hU : oG.toC (oG.ofC (X := fun k => H k X) ⟨sh, fun q => (oH _).ofC ⟨t q, fun r => c ⟨q, r⟩⟩⟩) = U
      rw [toC_ofC] at hU
      subst hU
      dsimp only at c
      refine Occ.comp_ext (Sh' := fun sh q => Sh' (pidx sh q)) (Pos' := fun sh q s => Pos' (pidx sh q) s)
        (X := fun sh q s r => X (pidx' (pidx sh q) s r)) sh _ t c ?_
      intro q
      exact (oH _).toC_ofC _ }

end Comp

end IOcc

namespace Occ

section CompI

variable {J : Type j} {Sh : Type s} {Pos : Sh → Type p} {pidx : (sh : Sh) → Pos sh → J}

/-- A functor of families at a constant family: a plain structure. -/
def ofI {G : (J → Type u) → Type v} (o : IOcc Sh Pos pidx G) :
    Occ Sh Pos (fun X : Type u => G fun _ => X) :=
  ⟨o.equiv⟩

/-- A functor of families applied to a family of expressions with a plain occurrence. -/
def compI {G : (J → Type u') → Type v} (oG : IOcc Sh Pos pidx G) {Sh' : J → Type s'}
    {Pos' : ∀ j, Sh' j → Type p'} {H : J → Type u → Type u'}
    (oH : ∀ j, Occ (Sh' j) (Pos' j) (H j)) :
    Occ (Σ sh, (q : Pos sh) → Sh' (pidx sh q)) (fun z => Σ q, Pos' _ (z.2 q))
      (fun X => G fun j => H j X) where
  equiv {X} := {
    toFun x := ⟨⟨(oG.toC x).1, fun q => ((oH _).toC ((oG.toC x).2 q)).1⟩,
      fun r => ((oH _).toC ((oG.toC x).2 r.1)).2 r.2⟩
    invFun z := oG.ofC ⟨z.1.1, fun q => (oH _).ofC ⟨z.1.2 q, fun r => z.2 ⟨q, r⟩⟩⟩
    left_inv x := by
      show oG.ofC ⟨(oG.toC x).1, fun q => (oH _).ofC ⟨((oH _).toC ((oG.toC x).2 q)).1,
        fun r => ((oH _).toC ((oG.toC x).2 q)).2 r⟩⟩ = x
      simp only [ofC_toC', IOcc.ofC_toC']
    right_inv := fun ⟨⟨sh, t⟩, c⟩ => by
      dsimp only
      generalize hU : oG.toC (oG.ofC (X := fun k => H k X) ⟨sh, fun q => (oH _).ofC ⟨t q, fun r => c ⟨q, r⟩⟩⟩) = U
      rw [IOcc.toC_ofC] at hU
      subst hU
      dsimp only at c
      refine comp_ext (Sh' := fun sh q => Sh' (pidx sh q)) (Pos' := fun sh q s => Pos' (pidx sh q) s)
        (X := fun _ _ _ _ => X) sh _ t c ?_
      intro q
      exact (oH _).toC_ofC _ }

end CompI

/-! ### The computation of `map`, `Rel` and the positions through the combinators -/

section Compute

variable {X : Type u} {Y : Type u'}

@[simp] theorem map_const {A : Type v} (f : X → Y) (x : A) :
    map (const A) (const A) f x = x := rfl

@[simp] theorem map_hole (f : X → Y) (x : X) : map hole hole f x = f x := rfl

/-- The map through the hole is the function, also where it is not applied: as the function of
another map (`List.map`). -/
@[simp] theorem map_hole_hole (f : X → Y) : map hole hole f = f := rfl

/-- The map through a constant is the identity, also where it is not applied: as a function of
another map (`Sum.map`). -/
@[simp] theorem map_const_const {A : Type v} (f : X → Y) : map (const A) (const A) f = id := rfl

theorem toC_hole (x : X) : hole.toC x = ⟨(), fun _ => x⟩ := rfl

theorem forall_toC_hole {P : X → Prop} (x : X) : (∀ q, P ((hole.toC x).2 q)) ↔ P x :=
  ⟨fun h => h (), fun h _ => h⟩

variable {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p} {Sh₂ : Type s'} {Pos₂ : Sh₂ → Type p'}
  {G₁ : Type u → Type v} {G₂ : Type u → Type v'} {G₁' : Type u' → Type w} {G₂' : Type u' → Type w'}
  (o₁ : Occ Sh₁ Pos₁ G₁) (o₂ : Occ Sh₂ Pos₂ G₂) (o₁' : Occ Sh₁ Pos₁ G₁') (o₂' : Occ Sh₂ Pos₂ G₂')

theorem toC_prod (x : G₁ X × G₂ X) :
    (prod o₁ o₂).toC x =
      ⟨((o₁.toC x.1).1, (o₂.toC x.2).1), sumRec (o₁.toC x.1).2 (o₂.toC x.2).2⟩ := rfl

@[simp] theorem map_prod (f : X → Y) (x : G₁ X × G₂ X) :
    map (prod o₁ o₂) (prod o₁' o₂') f x = (map o₁ o₁' f x.1, map o₂ o₂' f x.2) := rfl

@[simp] theorem map_sum_inl (f : X → Y) (x : G₁ X) :
    map (sum o₁ o₂) (sum o₁' o₂') f (.inl x) = .inl (map o₁ o₁' f x) := rfl

@[simp] theorem map_sum_inr (f : X → Y) (x : G₂ X) :
    map (sum o₁ o₂) (sum o₁' o₂') f (.inr x) = .inr (map o₂ o₂' f x) := rfl

/-- The map through a sum at any value is `Sum.map` of the maps of the two sides. -/
@[simp] theorem map_sum (f : X → Y) (x : G₁ X ⊕ G₂ X) :
    map (sum o₁ o₂) (sum o₁' o₂') f x = Sum.map (map o₁ o₁' f) (map o₂ o₂' f) x := by
  cases x <;> rfl

theorem forall_toC_prod {P : X → Prop} (x : G₁ X × G₂ X) :
    (∀ q, P (((prod o₁ o₂).toC x).2 q)) ↔
      (∀ q, P ((o₁.toC x.1).2 q)) ∧ ∀ q, P ((o₂.toC x.2).2 q) :=
  ⟨fun h => ⟨fun q => h (.inl q), fun q => h (.inr q)⟩,
    fun h q => by cases q with | inl q => exact h.1 q | inr q => exact h.2 q⟩

@[simp] theorem rel_const {A : Type v} (R : X → Y → Prop) (a b : A) :
    Rel (const A) (const A) R a b ↔ a = b := by
  constructor
  · rintro ⟨sh, c, c', ha, hb, _⟩
    exact (Sigma.mk.inj_iff.mp ha).1.trans (Sigma.mk.inj_iff.mp hb).1.symm
  · rintro rfl
    exact ⟨a, Empty.elim, Empty.elim, rfl, rfl, fun q => q.elim⟩

@[simp] theorem rel_hole (R : X → Y → Prop) (x : X) (y : Y) : Rel hole hole R x y ↔ R x y := by
  constructor
  · rintro ⟨_, c, c', hx, hy, h⟩
    cases hx
    cases hy
    exact h ()
  · exact fun h => ⟨(), fun _ => x, fun _ => y, rfl, rfl, fun _ => h⟩

/-- Related values are related at the hole. -/
theorem rel_hole_intro {R : X → Y → Prop} {x : X} {y : Y} (h : R x y) : Rel hole hole R x y :=
  (rel_hole R x y).mpr h

/-- Pairs related componentwise are related through the product. -/
theorem rel_prod_intro {R : X → Y → Prop} {x : G₁ X × G₂ X} {y : G₁' Y × G₂' Y}
    (h₁ : Rel o₁ o₁' R x.1 y.1) (h₂ : Rel o₂ o₂' R x.2 y.2) :
    Rel (prod o₁ o₂) (prod o₁' o₂') R x y := by
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨y₁, y₂⟩ := y
  obtain ⟨s₁, c₁, c₁', hx₁, hy₁, hR₁⟩ := h₁
  obtain ⟨s₂, c₂, c₂', hx₂, hy₂, hR₂⟩ := h₂
  refine ⟨(s₁, s₂), sumRec c₁ c₂, sumRec c₁' c₂', ?_, ?_, fun q => ?_⟩
  · rw [toC_prod]
    dsimp only
    generalize o₁.toC x₁ = z₁ at hx₁ ⊢
    generalize o₂.toC x₂ = z₂ at hx₂ ⊢
    subst hx₁ hx₂
    rfl
  · rw [toC_prod]
    dsimp only
    generalize o₁'.toC y₁ = z₁ at hy₁ ⊢
    generalize o₂'.toC y₂ = z₂ at hy₂ ⊢
    subst hy₁ hy₂
    rfl
  · cases q with
    | inl q => exact hR₁ q
    | inr q => exact hR₂ q

end Compute

section ComputeDep

variable {X : Type u} {Y : Type u'}
variable {A : Type a} {ShA : A → Type s} {PosA : ∀ x, ShA x → Type p}
  {GA : A → Type u → Type v} {GA' : A → Type u' → Type w}
  (o : ∀ x, Occ (ShA x) (PosA x) (GA x)) (o' : ∀ x, Occ (ShA x) (PosA x) (GA' x))

theorem toC_pi (k : ∀ x, GA x X) :
    (pi A o).toC k = ⟨fun x => ((o x).toC (k x)).1, fun q => ((o q.1).toC (k q.1)).2 q.2⟩ := rfl

@[simp] theorem map_pi (f : X → Y) (k : ∀ x, GA x X) :
    map (pi A o) (pi A o') f k = fun x => map (o x) (o' x) f (k x) := rfl

theorem forall_toC_pi {P : X → Prop} (k : ∀ x, GA x X) :
    (∀ q, P (((pi A o).toC k).2 q)) ↔ ∀ x q, P (((o x).toC (k x)).2 q) :=
  ⟨fun h x q => h ⟨x, q⟩, fun h q => h q.1 q.2⟩

@[simp] theorem map_sigma (f : X → Y) (z : Σ x, GA x X) :
    map (sigma A o) (sigma A o') f z = ⟨z.1, map (o z.1) (o' z.1) f z.2⟩ := rfl

end ComputeDep

section ComputeComp

variable {X : Type u} {Y : Type u'}
variable {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {Pos' : Sh' → Type p'}
  {G : Type u'' → Type v} {G' : Type v'' → Type v'} {H : Type u → Type u''} {H' : Type u' → Type v''}
  (oG : Occ Sh Pos G) (oG' : Occ Sh Pos G') (oH : Occ Sh' Pos' H) (oH' : Occ Sh' Pos' H')

/-- The layer of a value through a composite. -/
theorem toC_comp (x : G (H X)) :
    (comp oG oH).toC x = ⟨⟨(oG.toC x).1, fun q => (oH.toC ((oG.toC x).2 q)).1⟩,
      fun r => (oH.toC ((oG.toC x).2 r.1)).2 r.2⟩ := rfl

theorem ofC_comp (z : Σ z : Σ sh, Pos sh → Sh', (Σ q, Pos' (z.2 q)) → X) :
    (comp oG oH).ofC z = oG.ofC ⟨z.1.1, fun q => oH.ofC ⟨z.1.2 q, fun r => z.2 ⟨q, r⟩⟩⟩ := rfl

/-- The map through a composite is the map of the map. -/
@[simp] theorem map_comp (f : X → Y) (x : G (H X)) :
    map (comp oG oH) (comp oG' oH') f x = map oG oG' (map oH oH' f) x := rfl

theorem forall_toC_comp {P : X → Prop} (x : G (H X)) :
    (∀ r, P (((comp oG oH).toC x).2 r)) ↔ ∀ q r, P ((oH.toC ((oG.toC x).2 q)).2 r) :=
  ⟨fun h q r => h ⟨q, r⟩, fun h r => h r.1 r.2⟩

end ComputeComp

/-! ### Membership

The members of a value are the contents of its positions, as for `PolyIso.Mem`: at a leaf those
of the instance (`mem_ofIso`), and `simp` computes them through the combinators, a sum at any
value too (`mem_sum`). The members of a structure in two variables in each variable
(`Model/Occ2.lean`) are these at its parts in one variable. -/

section Mem

variable {Sh : Type s} {Pos : Sh → Type p} {G : Type u → Type v} {X : Type u}

/-- `x` is a member of `y`: some position of `y` holds `x`. -/
def Mem (o : Occ Sh Pos G) (x : X) (y : G X) : Prop :=
  ∃ q, (o.toC y).2 q = x

theorem mem_iff (o : Occ Sh Pos G) {x : X} {y : G X} : Mem o x y ↔ ∃ q, (o.toC y).2 q = x :=
  Iff.rfl

end Mem

section MemCompute

variable {X : Type u}

/-- At a leaf, the members are those of the instance. -/
@[simp] theorem mem_ofIso (F : Type u → Type v) {ShF : Type s} {PosF : ShF → Type p}
    [PolyIso F ShF PosF] (x : X) (y : F X) : Mem (ofIso F) x y ↔ PolyIso.Mem F x y :=
  Iff.rfl

@[simp] theorem mem_hole (x y : X) : Mem hole x y ↔ x = y :=
  ⟨fun ⟨_, e⟩ => e.symm, fun e => ⟨(), e.symm⟩⟩

@[simp] theorem not_mem_const (A : Type v) (x : X) (a : A) : ¬ Mem (const A) x a :=
  fun ⟨q, _⟩ => q.elim

section Forms

variable {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p} {Sh₂ : Type s'} {Pos₂ : Sh₂ → Type p'}
  {G₁ : Type u → Type v} {G₂ : Type u → Type v'} (o₁ : Occ Sh₁ Pos₁ G₁) (o₂ : Occ Sh₂ Pos₂ G₂)

@[simp] theorem mem_prod (x : X) (y : G₁ X × G₂ X) :
    Mem (prod o₁ o₂) x y ↔ Mem o₁ x y.1 ∨ Mem o₂ x y.2 :=
  ⟨fun ⟨q, e⟩ => match q, e with
    | .inl q, e => .inl ⟨q, e⟩
    | .inr q, e => .inr ⟨q, e⟩,
    fun h => h.elim (fun ⟨q, e⟩ => ⟨.inl q, e⟩) (fun ⟨q, e⟩ => ⟨.inr q, e⟩)⟩

@[simp] theorem mem_sum_inl (x : X) (y : G₁ X) : Mem (sum o₁ o₂) x (.inl y) ↔ Mem o₁ x y :=
  ⟨fun ⟨q, e⟩ => ⟨q.down, e⟩, fun ⟨q, e⟩ => ⟨⟨q⟩, e⟩⟩

@[simp] theorem mem_sum_inr (x : X) (y : G₂ X) : Mem (sum o₁ o₂) x (.inr y) ↔ Mem o₂ x y :=
  ⟨fun ⟨q, e⟩ => ⟨q.down, e⟩, fun ⟨q, e⟩ => ⟨⟨q⟩, e⟩⟩

/-- Through a sum at any value: on the side the value is on. -/
@[simp] theorem mem_sum (x : X) (y : G₁ X ⊕ G₂ X) :
    Mem (sum o₁ o₂) x y ↔ (∃ a, y = .inl a ∧ Mem o₁ x a) ∨ ∃ b, y = .inr b ∧ Mem o₂ x b := by
  cases y with
  | inl a => simp only [mem_sum_inl, Sum.inl.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, or_false]
  | inr b => simp only [mem_sum_inr, Sum.inr.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, false_or]

end Forms

section Dependent

variable {A : Type a} {ShA : A → Type s} {PosA : ∀ x, ShA x → Type p} {GA : A → Type u → Type v}
  (o : ∀ x, Occ (ShA x) (PosA x) (GA x))

@[simp] theorem mem_pi (x : X) (k : ∀ a, GA a X) : Mem (pi A o) x k ↔ ∃ a, Mem (o a) x (k a) :=
  ⟨fun ⟨q, e⟩ => ⟨q.1, q.2, e⟩, fun ⟨a, q, e⟩ => ⟨⟨a, q⟩, e⟩⟩

@[simp] theorem mem_sigma (x : X) (z : Σ a, GA a X) : Mem (sigma A o) x z ↔ Mem (o z.1) x z.2 :=
  Iff.rfl

end Dependent

@[simp] theorem mem_piP {P : Prop} {ShP : P → Type s} {PosP : ∀ h, ShP h → Type p}
    {GP : P → Type u → Type v} (o : ∀ h, Occ (ShP h) (PosP h) (GP h)) (x : X) (k : ∀ h, GP h X) :
    Mem (piP P o) x k ↔ ∃ h, Mem (o h) x (k h) :=
  ⟨fun ⟨q, e⟩ => ⟨q.1, q.2, e⟩, fun ⟨h, q, e⟩ => ⟨⟨h, q⟩, e⟩⟩

/-- Through a composite: a member of a member of the outer structure. -/
@[simp] theorem mem_comp {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {Pos' : Sh' → Type p'}
    {G : Type u' → Type v} {H : Type u → Type u'} (oG : Occ Sh Pos G) (oH : Occ Sh' Pos' H) (x : X)
    (y : G (H X)) : Mem (comp oG oH) x y ↔ ∃ z, Mem oG z y ∧ Mem oH x z :=
  ⟨fun ⟨r, e⟩ => ⟨_, ⟨r.1, rfl⟩, r.2, e⟩, fun ⟨_, ⟨q, e⟩, r, e'⟩ => by subst e; exact ⟨⟨q, r⟩, e'⟩⟩

end MemCompute

/-! What `simp` makes of `∃ t, Mem o t y ∧ P t`, the members of a value with a property, before it
computes the membership (`simp ↓`): the combinators are gone through first, so that the member is
eliminated at each leaf also where several occurrences make a disjunction (`List (α × α)`), which
the membership computed first would leave under an existential. -/

section ExistsMem

variable {X : Type u} (P : X → Prop)

@[simp ↓] theorem exists_mem_hole (y : X) : (∃ t, Mem hole t y ∧ P t) ↔ P y := by
  simp only [mem_hole, exists_eq_left]

@[simp ↓] theorem exists_mem_const (A : Type v) (a : A) : (∃ t, Mem (const A) t a ∧ P t) ↔ False :=
  ⟨fun ⟨_, h, _⟩ => not_mem_const A _ a h, False.elim⟩

section Forms

variable {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p} {Sh₂ : Type s'} {Pos₂ : Sh₂ → Type p'}
  {G₁ : Type u → Type v} {G₂ : Type u → Type v'} (o₁ : Occ Sh₁ Pos₁ G₁) (o₂ : Occ Sh₂ Pos₂ G₂)

@[simp ↓] theorem exists_mem_prod (y : G₁ X × G₂ X) :
    (∃ t, Mem (prod o₁ o₂) t y ∧ P t) ↔ (∃ t, Mem o₁ t y.1 ∧ P t) ∨ ∃ t, Mem o₂ t y.2 ∧ P t := by
  simp only [mem_prod, or_and_right, exists_or]

@[simp ↓] theorem exists_mem_sum (y : G₁ X ⊕ G₂ X) :
    (∃ t, Mem (sum o₁ o₂) t y ∧ P t) ↔
      (∃ a, y = .inl a ∧ ∃ t, Mem o₁ t a ∧ P t) ∨ ∃ b, y = .inr b ∧ ∃ t, Mem o₂ t b ∧ P t := by
  cases y with
  | inl a => simp only [mem_sum_inl, Sum.inl.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, or_false]
  | inr b => simp only [mem_sum_inr, Sum.inr.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, false_or]

end Forms

@[simp ↓] theorem exists_mem_pi {A : Type a} {ShA : A → Type s} {PosA : ∀ x, ShA x → Type p}
    {GA : A → Type u → Type v} (o : ∀ x, Occ (ShA x) (PosA x) (GA x)) (k : ∀ a, GA a X) :
    (∃ t, Mem (pi A o) t k ∧ P t) ↔ ∃ a, ∃ t, Mem (o a) t (k a) ∧ P t := by
  simp only [mem_pi]
  exact ⟨fun ⟨t, ⟨a, h⟩, h'⟩ => ⟨a, t, h, h'⟩, fun ⟨a, t, h, h'⟩ => ⟨t, ⟨a, h⟩, h'⟩⟩

@[simp ↓] theorem exists_mem_sigma {A : Type a} {ShA : A → Type s} {PosA : ∀ x, ShA x → Type p}
    {GA : A → Type u → Type v} (o : ∀ x, Occ (ShA x) (PosA x) (GA x)) (z : Σ a, GA a X) :
    (∃ t, Mem (sigma A o) t z ∧ P t) ↔ ∃ t, Mem (o z.1) t z.2 ∧ P t :=
  Iff.rfl

@[simp ↓] theorem exists_mem_piP {Q : Prop} {ShP : Q → Type s} {PosP : ∀ h, ShP h → Type p}
    {GP : Q → Type u → Type v} (o : ∀ h, Occ (ShP h) (PosP h) (GP h)) (k : ∀ h, GP h X) :
    (∃ t, Mem (piP Q o) t k ∧ P t) ↔ ∃ h, ∃ t, Mem (o h) t (k h) ∧ P t := by
  simp only [mem_piP]
  exact ⟨fun ⟨t, ⟨h, m⟩, h'⟩ => ⟨h, t, m, h'⟩, fun ⟨h, t, m, h'⟩ => ⟨t, ⟨h, m⟩, h'⟩⟩

@[simp ↓] theorem exists_mem_comp {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'}
    {Pos' : Sh' → Type p'} {G : Type u' → Type v} {H : Type u → Type u'} (oG : Occ Sh Pos G)
    (oH : Occ Sh' Pos' H) (y : G (H X)) :
    (∃ t, Mem (comp oG oH) t y ∧ P t) ↔ ∃ z, Mem oG z y ∧ ∃ t, Mem oH t z ∧ P t := by
  simp only [mem_comp]
  exact ⟨fun ⟨t, ⟨z, hz, m⟩, h⟩ => ⟨z, hz, t, m, h⟩, fun ⟨z, hz, t, m, h⟩ => ⟨t, ⟨z, hz, m⟩, h⟩⟩

end ExistsMem

/-! ### The computation of `Rel`

`Rel o o' R x y` says that the layers of `x` and `y` have one shape and related contents. Through
`ofC` the two values are substituted away (`rel_iff_ofC`), and every combinator computes by
definition: `simp` takes the relation through products, sums, functions and composites, down to
the leaves, whose relations are the library's (`List.Forall₂`, `Option.Rel`), with the generated
`T.Poly.rel_cᵢ_cⱼ` for a declared type. A map on either side moves into the relation, and a value
related to itself is a relation at its members (`rel_self`). -/

section RelGeneric

variable {Sh : Type s} {Pos : Sh → Type p}
  {G : Type u → Type v} {G' : Type u' → Type v'} {G'' : Type u'' → Type v''}
  {X : Type u} {Y : Type u'} {W : Type u''}

/-- `Rel` through `ofC`: one shape, related contents. -/
theorem rel_iff_ofC (o : Occ Sh Pos G) (o' : Occ Sh Pos G') {R : X → Y → Prop} {x : G X}
    {y : G' Y} :
    Rel o o' R x y ↔ ∃ (sh : Sh) (c : Pos sh → X) (c' : Pos sh → Y),
      (∀ q, R (c q) (c' q)) ∧ x = o.ofC ⟨sh, c⟩ ∧ y = o'.ofC ⟨sh, c'⟩ := by
  constructor
  · rintro ⟨sh, c, c', hx, hy, h⟩
    exact ⟨sh, c, c', h, by rw [← hx, ofC_toC], by rw [← hy, ofC_toC]⟩
  · rintro ⟨sh, c, c', h, rfl, rfl⟩
    exact rel_intro o o' sh c c' h

/-- `Rel` as the canonical lifting: related values are the two projections of one value over
related pairs, at any third structure with the same shapes. -/
theorem rel_iff_exists_map {G₂ : Type (max u u') → Type w'} (o : Occ Sh Pos G)
    (o' : Occ Sh Pos G') (o₂ : Occ Sh Pos G₂) {R : X → Y → Prop} {x : G X} {y : G' Y} :
    Rel o o' R x y ↔ ∃ z : G₂ {p : X × Y // R p.1 p.2},
      map o₂ o (fun p => p.1.1) z = x ∧ map o₂ o' (fun p => p.1.2) z = y :=
  ⟨exists_map_of_rel o o' o₂,
    fun ⟨z, hx, hy⟩ => hx ▸ hy ▸ rel_map o₂ o o' R _ _ z fun p => p.2⟩

/-- A larger relation relates more. -/
theorem Rel.mono (o : Occ Sh Pos G) (o' : Occ Sh Pos G') {R S : X → Y → Prop}
    (hRS : ∀ x y, R x y → S x y) {x : G X} {y : G' Y} (h : Rel o o' R x y) : Rel o o' S x y := by
  obtain ⟨sh, c, c', hx, hy, h⟩ := h
  exact ⟨sh, c, c', hx, hy, fun q => hRS _ _ (h q)⟩

/-- A map on the left moves into the relation. -/
@[simp] theorem rel_map_left (o : Occ Sh Pos G'') (o₁ : Occ Sh Pos G) (o' : Occ Sh Pos G')
    {R : X → Y → Prop} (f : W → X) (x : G'' W) (y : G' Y) :
    Rel o₁ o' R (map o o₁ f x) y ↔ Rel o o' (fun a b => R (f a) b) x y := by
  constructor
  · rintro ⟨sh, c, c', hx, hy, h⟩
    rw [toC_map] at hx
    obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.mp hx
    cases hc
    exact ⟨_, _, c', rfl, hy, h⟩
  · rintro ⟨sh, c, c', hx, hy, h⟩
    refine ⟨sh, fun q => f (c q), c', ?_, hy, h⟩
    rw [toC_map, hx]

/-- A map on the right moves into the relation. -/
@[simp] theorem rel_map_right (o : Occ Sh Pos G) (o₁ : Occ Sh Pos G'') (o' : Occ Sh Pos G')
    {R : X → Y → Prop} (g : W → Y) (x : G X) (y : G'' W) :
    Rel o o' R x (map o₁ o' g y) ↔ Rel o o₁ (fun a b => R a (g b)) x y := by
  constructor
  · rintro ⟨sh, c, c', hx, hy, h⟩
    rw [toC_map] at hy
    obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.mp hy
    cases hc
    exact ⟨_, c, _, hx, rfl, h⟩
  · rintro ⟨sh, c, c', hx, hy, h⟩
    refine ⟨sh, c, fun q => g (c' q), hx, ?_, h⟩
    rw [toC_map, hy]

/-- A value related to itself: the relation at each of its members. With the two lemmas above,
`Rel R (map f x) (map g x)` becomes `∀ a, Mem a x → R (f a) (g a)`, and `simp` computes the
members. -/
@[simp] theorem rel_self (o : Occ Sh Pos G) {R : X → X → Prop} (x : G X) :
    Rel o o R x x ↔ ∀ a, Mem o a x → R a a := by
  constructor
  · rintro ⟨sh, c, c', hx, hy, h⟩ a ⟨q, rfl⟩
    have hc : c = c' := eq_of_heq (Sigma.mk.inj_iff.mp (hx.symm.trans hy)).2
    subst hc
    revert q
    rw [hx]
    exact h
  · intro h
    exact ⟨_, _, _, rfl, rfl, fun q => h _ ⟨q, rfl⟩⟩

end RelGeneric

section RelForms

variable {X : Type u} {Y : Type u'}
variable {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p} {Sh₂ : Type s'} {Pos₂ : Sh₂ → Type p'}
  {G₁ : Type u → Type v} {G₂ : Type u → Type v'} {G₁' : Type u' → Type w} {G₂' : Type u' → Type w'}
  (o₁ : Occ Sh₁ Pos₁ G₁) (o₂ : Occ Sh₂ Pos₂ G₂) (o₁' : Occ Sh₁ Pos₁ G₁') (o₂' : Occ Sh₂ Pos₂ G₂')

/-- A product, componentwise (the converse of `rel_prod_intro`). -/
@[simp] theorem rel_prod {R : X → Y → Prop} (x : G₁ X × G₂ X) (y : G₁' Y × G₂' Y) :
    Rel (prod o₁ o₂) (prod o₁' o₂') R x y ↔ Rel o₁ o₁' R x.1 y.1 ∧ Rel o₂ o₂' R x.2 y.2 := by
  refine ⟨fun h => ?_, fun h => rel_prod_intro o₁ o₂ o₁' o₂' h.1 h.2⟩
  obtain ⟨⟨s₁, s₂⟩, c, c', hc, rfl, rfl⟩ := (rel_iff_ofC _ _).mp h
  exact ⟨rel_intro o₁ o₁' s₁ _ _ fun q => hc (.inl q), rel_intro o₂ o₂' s₂ _ _ fun q => hc (.inr q)⟩

/-- A sum, by sides: the same side, related values. -/
@[simp] theorem rel_sum_inl_inl {R : X → Y → Prop} (x : G₁ X) (y : G₁' Y) :
    Rel (sum o₁ o₂) (sum o₁' o₂') R (.inl x) (.inl y) ↔ Rel o₁ o₁' R x y := by
  constructor
  · intro h
    obtain ⟨sh | sh, c, c', hc, hx, hy⟩ := (rel_iff_ofC _ _).mp h
    · cases hx; cases hy
      exact rel_intro o₁ o₁' sh _ _ fun q => hc ⟨q⟩
    · cases hx
  · intro h
    obtain ⟨sh, c, c', hc, rfl, rfl⟩ := (rel_iff_ofC _ _).mp h
    exact rel_intro (sum o₁ o₂) (sum o₁' o₂') (.inl sh) (fun q => c q.down) (fun q => c' q.down)
      fun q => hc q.down

@[simp] theorem rel_sum_inr_inr {R : X → Y → Prop} (x : G₂ X) (y : G₂' Y) :
    Rel (sum o₁ o₂) (sum o₁' o₂') R (.inr x) (.inr y) ↔ Rel o₂ o₂' R x y := by
  constructor
  · intro h
    obtain ⟨sh | sh, c, c', hc, hx, hy⟩ := (rel_iff_ofC _ _).mp h
    · cases hx
    · cases hx; cases hy
      exact rel_intro o₂ o₂' sh _ _ fun q => hc ⟨q⟩
  · intro h
    obtain ⟨sh, c, c', hc, rfl, rfl⟩ := (rel_iff_ofC _ _).mp h
    exact rel_intro (sum o₁ o₂) (sum o₁' o₂') (.inr sh) (fun q => c q.down) (fun q => c' q.down)
      fun q => hc q.down

@[simp] theorem rel_sum_inl_inr {R : X → Y → Prop} (x : G₁ X) (y : G₂' Y) :
    Rel (sum o₁ o₂) (sum o₁' o₂') R (.inl x) (.inr y) ↔ False := by
  refine ⟨fun h => ?_, False.elim⟩
  obtain ⟨sh | sh, c, c', hc, hx, hy⟩ := (rel_iff_ofC _ _).mp h
  · cases hy
  · cases hx

@[simp] theorem rel_sum_inr_inl {R : X → Y → Prop} (x : G₂ X) (y : G₁' Y) :
    Rel (sum o₁ o₂) (sum o₁' o₂') R (.inr x) (.inl y) ↔ False := by
  refine ⟨fun h => ?_, False.elim⟩
  obtain ⟨sh | sh, c, c', hc, hx, hy⟩ := (rel_iff_ofC _ _).mp h
  · cases hx
  · cases hy

end RelForms

/-- A function from a constant type, pointwise. -/
@[simp] theorem rel_pi {X : Type u} {Y : Type u'} {A : Type a} {ShA : A → Type s}
    {PosA : ∀ x, ShA x → Type p} {GA : A → Type u → Type v} {GA' : A → Type u' → Type w}
    (o : ∀ x, Occ (ShA x) (PosA x) (GA x)) (o' : ∀ x, Occ (ShA x) (PosA x) (GA' x))
    {R : X → Y → Prop} (k : ∀ x, GA x X) (k' : ∀ x, GA' x Y) :
    Rel (pi A o) (pi A o') R k k' ↔ ∀ x, Rel (o x) (o' x) R (k x) (k' x) := by
  constructor
  · intro h x
    obtain ⟨sh, c, c', hc, rfl, rfl⟩ := (rel_iff_ofC _ _).mp h
    exact rel_intro (o x) (o' x) (sh x) _ _ fun q => hc ⟨x, q⟩
  · intro h
    choose sh c c' hc hk hk' using fun x => (rel_iff_ofC _ _).mp (h x)
    exact (rel_iff_ofC _ _).mpr ⟨sh, fun q => c q.1 q.2, fun q => c' q.1 q.2,
      fun q => hc q.1 q.2, funext hk, funext hk'⟩

/-- A composite: the outer relation at the inner one. -/
@[simp] theorem rel_comp {X : Type u} {Y : Type u'} {Sh : Type s} {Pos : Sh → Type p}
    {Sh' : Type s'} {Pos' : Sh' → Type p'} {G : Type u'' → Type v} {G' : Type v'' → Type v'}
    {H : Type u → Type u''} {H' : Type u' → Type v''} (oG : Occ Sh Pos G) (oG' : Occ Sh Pos G')
    (oH : Occ Sh' Pos' H) (oH' : Occ Sh' Pos' H') {R : X → Y → Prop} (x : G (H X))
    (y : G' (H' Y)) :
    Rel (comp oG oH) (comp oG' oH') R x y ↔ Rel oG oG' (Rel oH oH' R) x y := by
  constructor
  · intro h
    obtain ⟨⟨sh, t⟩, c, c', hc, rfl, rfl⟩ := (rel_iff_ofC _ _).mp h
    exact rel_intro oG oG' sh _ _ fun q => rel_intro oH oH' (t q) _ _ fun r => hc ⟨q, r⟩
  · intro h
    obtain ⟨sh, c, c', hc, rfl, rfl⟩ := (rel_iff_ofC _ _).mp h
    choose t d d' hd hdc hdc' using fun q => (rel_iff_ofC _ _).mp (hc q)
    refine (rel_iff_ofC _ _).mpr ⟨⟨sh, t⟩, fun r => d r.1 r.2, fun r => d' r.1 r.2,
      fun r => hd r.1 r.2, ?_, ?_⟩
    · rw [ofC_comp]; exact congrArg (fun c => oG.ofC ⟨sh, c⟩) (funext hdc)
    · rw [ofC_comp]; exact congrArg (fun c => oG'.ofC ⟨sh, c⟩) (funext hdc')

/-- `List`: `List.Forall₂`, with Mathlib's `simp` lemmas (`List.forall₂_cons`,
`List.forall₂_map_left_iff`, `List.forall₂_same`, …). -/
@[simp] theorem rel_list {X : Type u} {Y : Type u'} {R : X → Y → Prop} (l : List X)
    (l' : List Y) : Rel (ofIso List) (ofIso List) R l l' ↔ List.Forall₂ R l l' := by
  rw [rel_iff_ofC]
  constructor
  · rintro ⟨n, c, c', hc, rfl, rfl⟩
    show List.Forall₂ R (List.ofFn c) (List.ofFn c')
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [List.ofFn_succ, List.forall₂_cons]
      exact ⟨hc 0, ih _ _ fun q => hc _⟩
  · intro h
    induction h with
    | nil => exact ⟨0, Fin.elim0, Fin.elim0, fun q => q.elim0, rfl, rfl⟩
    | @cons a b l l' hab _ ih =>
      obtain ⟨n, c, c', hc, rfl, rfl⟩ := ih
      refine ⟨n + 1, Fin.cons a c, Fin.cons b c', fun q => Fin.cases hab hc q, ?_, ?_⟩
      all_goals simp [List.ofFn_succ]

/-- `Option`: `Option.Rel`, with its `simp` lemmas (`Option.rel_some_some`,
`Option.rel_none_none`). -/
@[simp] theorem rel_option {X : Type u} {Y : Type u'} {R : X → Y → Prop} (o : Option X)
    (o' : Option Y) : Rel (ofIso Option) (ofIso Option) R o o' ↔ Option.Rel R o o' := by
  rw [rel_iff_ofC]
  constructor
  · rintro ⟨_ | _, c, c', hc, rfl, rfl⟩
    · exact .none
    · exact .some (hc .unit)
  · rintro (⟨h⟩ | _)
    · exact ⟨true, fun _ => _, fun _ => _, fun _ => h, rfl, rfl⟩
    · have e (q : OptionPos false) : False := nomatch q
      exact ⟨false, fun q => (e q).elim, fun q => (e q).elim, fun q => (e q).elim, rfl, rfl⟩


end Occ

/-! ### The computation of `map` through the indexed combinators

The same lemmas as for `Occ`, so that `simp` computes the rules of a family whose nested argument
has an indexed structure (`T n × T (n + 1)`, `IOcc.prod`). -/

namespace IOcc

section Compute

variable {J : Type j} {K : Type k} {X : J → Type u} {Y : J → Type u'}

@[simp] theorem map_const {A : Type v} (f : ∀ j, X j → Y j) (x : A) :
    map (const A) (const A) f x = x := rfl

@[simp] theorem map_hole (i : J) (f : ∀ j, X j → Y j) (x : X i) :
    map (hole i) (hole i) f x = f i x := rfl

/-- The map through a hole is the function at its index, also where it is not applied. -/
@[simp] theorem map_hole_hole (i : J) (f : ∀ j, X j → Y j) : map (hole i) (hole i) f = f i :=
  rfl

/-- The map through a constant is the identity, also where it is not applied. -/
@[simp] theorem map_const_const {A : Type v} (f : ∀ j, X j → Y j) :
    map (const A) (const A) f = id := rfl

variable {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p} {pidx₁ : (sh : Sh₁) → Pos₁ sh → J}
  {Sh₂ : Type s'} {Pos₂ : Sh₂ → Type p'} {pidx₂ : (sh : Sh₂) → Pos₂ sh → J}
  {G₁ : (J → Type u) → Type v} {G₂ : (J → Type u) → Type v'}
  {G₁' : (J → Type u') → Type w} {G₂' : (J → Type u') → Type w'}
  (o₁ : IOcc Sh₁ Pos₁ pidx₁ G₁) (o₂ : IOcc Sh₂ Pos₂ pidx₂ G₂)
  (o₁' : IOcc Sh₁ Pos₁ pidx₁ G₁') (o₂' : IOcc Sh₂ Pos₂ pidx₂ G₂')

@[simp] theorem map_prod (f : ∀ j, X j → Y j) (x : G₁ X × G₂ X) :
    map (prod o₁ o₂) (prod o₁' o₂') f x = (map o₁ o₁' f x.1, map o₂ o₂' f x.2) := rfl

@[simp] theorem map_sum_inl (f : ∀ j, X j → Y j) (x : G₁ X) :
    map (sum o₁ o₂) (sum o₁' o₂') f (.inl x) = .inl (map o₁ o₁' f x) := rfl

@[simp] theorem map_sum_inr (f : ∀ j, X j → Y j) (x : G₂ X) :
    map (sum o₁ o₂) (sum o₁' o₂') f (.inr x) = .inr (map o₂ o₂' f x) := rfl

/-- The map through a sum at any value is `Sum.map` of the maps of the two sides. -/
@[simp] theorem map_sum (f : ∀ j, X j → Y j) (x : G₁ X ⊕ G₂ X) :
    map (sum o₁ o₂) (sum o₁' o₂') f x = Sum.map (map o₁ o₁' f) (map o₂ o₂' f) x := by
  cases x <;> rfl

end Compute

section ComputeDep

variable {J : Type j} {X : J → Type u} {Y : J → Type u'}
variable {A : Type a} {ShA : A → Type s} {PosA : ∀ x, ShA x → Type p}
  {pidxA : ∀ x (sh : ShA x), PosA x sh → J} {GA : A → (J → Type u) → Type v}
  {GA' : A → (J → Type u') → Type w}
  (o : ∀ x, IOcc (ShA x) (PosA x) (pidxA x) (GA x))
  (o' : ∀ x, IOcc (ShA x) (PosA x) (pidxA x) (GA' x))

@[simp] theorem map_pi (f : ∀ j, X j → Y j) (k : ∀ x, GA x X) :
    map (pi A o) (pi A o') f k = fun x => map (o x) (o' x) f (k x) := rfl

@[simp] theorem map_sigma (f : ∀ j, X j → Y j) (z : Σ x, GA x X) :
    map (sigma A o) (sigma A o') f z = ⟨z.1, map (o z.1) (o' z.1) f z.2⟩ := rfl

end ComputeDep

section ComputeComp

variable {J : Type j} {K : Type k} {X : J → Type u} {Y : J → Type u'}
  {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {Pos' : Sh' → Type p'}

/-- The map through a plain constructor applied to an indexed expression is the map of the map.
-/
@[simp] theorem map_compC {G : Type u'' → Type v} {G' : Type v'' → Type v'}
    {pidx' : (sh : Sh') → Pos' sh → J} {H : (J → Type u) → Type u''}
    {H' : (J → Type u') → Type v''} (oG : Occ Sh Pos G) (oG' : Occ Sh Pos G')
    (oH : IOcc Sh' Pos' pidx' H) (oH' : IOcc Sh' Pos' pidx' H') (f : ∀ j, X j → Y j)
    (x : G (H X)) :
    map (compC oG oH) (compC oG' oH') f x = Occ.map oG oG' (map oH oH' f) x := rfl

/-- The map through a functor of families applied to a family of indexed expressions is the map
of the maps. -/
@[simp] theorem map_compI {pidx : (sh : Sh) → Pos sh → K} {G : (K → Type u'') → Type v}
    {G' : (K → Type v'') → Type v'} (oG : IOcc Sh Pos pidx G) (oG' : IOcc Sh Pos pidx G')
    {Sh'' : K → Type s'} {Pos'' : ∀ k, Sh'' k → Type p'}
    {pidx'' : ∀ k (sh : Sh'' k), Pos'' k sh → J}
    {H : K → (J → Type u) → Type u''} {H' : K → (J → Type u') → Type v''}
    (oH : ∀ k, IOcc (Sh'' k) (Pos'' k) (pidx'' k) (H k))
    (oH' : ∀ k, IOcc (Sh'' k) (Pos'' k) (pidx'' k) (H' k)) (f : ∀ j, X j → Y j)
    (x : G fun k => H k X) :
    map (compI oG oH) (compI oG' oH') f x = map oG oG' (fun k => map (oH k) (oH' k) f) x := rfl

end ComputeComp

/-! ### An indexed structure at one index

The map of an indexed structure whose positions are all at the index `i` is the map at `i` of the
plain structure of the same form: `Occ.hole` for `hole i`, the plain combinators for the indexed
ones. It is so by definition through every combinator but a sum, where the two agree only after
cases on the value, so the agreement goes through the combinators (`map_flat_sum`, …). The
command uses it for a nested argument of a family or of a type of a block whose positions are at
one index after cases on them (`Gen/Derive.lean`). -/

section MapFlat

variable {J : Type j} (i : J)

section Forms

variable {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p} {Sh₂ : Type s'} {Pos₂ : Sh₂ → Type p'}
  {F₁ : Type u → Type v} {F₂ : Type u → Type v'} {F₁' : Type u' → Type w} {F₂' : Type u' → Type w'}
  (p₁ : Occ Sh₁ Pos₁ F₁) (p₁' : Occ Sh₁ Pos₁ F₁') (p₂ : Occ Sh₂ Pos₂ F₂) (p₂' : Occ Sh₂ Pos₂ F₂')
  {pidx₁ : (sh : Sh₁) → Pos₁ sh → J} {pidx₂ : (sh : Sh₂) → Pos₂ sh → J}
  (o₁ : IOcc Sh₁ Pos₁ pidx₁ fun Y : J → Type u => F₁ (Y i))
  (o₁' : IOcc Sh₁ Pos₁ pidx₁ fun Y : J → Type u' => F₁' (Y i))
  (o₂ : IOcc Sh₂ Pos₂ pidx₂ fun Y : J → Type u => F₂ (Y i))
  (o₂' : IOcc Sh₂ Pos₂ pidx₂ fun Y : J → Type u' => F₂' (Y i))

theorem map_flat_prod
    (h₁ : ∀ {Y : J → Type u} {Y' : J → Type u'} (g : ∀ j, Y j → Y' j) (y : F₁ (Y i)),
      map o₁ o₁' g y = Occ.map p₁ p₁' (g i) y)
    (h₂ : ∀ {Y : J → Type u} {Y' : J → Type u'} (g : ∀ j, Y j → Y' j) (y : F₂ (Y i)),
      map o₂ o₂' g y = Occ.map p₂ p₂' (g i) y)
    {Y : J → Type u} {Y' : J → Type u'} (g : ∀ j, Y j → Y' j) (y : F₁ (Y i) × F₂ (Y i)) :
    map (prod o₁ o₂) (prod o₁' o₂') g y = Occ.map (Occ.prod p₁ p₂) (Occ.prod p₁' p₂') (g i) y :=
  Prod.ext (h₁ g y.1) (h₂ g y.2)

/-- Through a sum, by cases on the value. -/
theorem map_flat_sum
    (h₁ : ∀ {Y : J → Type u} {Y' : J → Type u'} (g : ∀ j, Y j → Y' j) (y : F₁ (Y i)),
      map o₁ o₁' g y = Occ.map p₁ p₁' (g i) y)
    (h₂ : ∀ {Y : J → Type u} {Y' : J → Type u'} (g : ∀ j, Y j → Y' j) (y : F₂ (Y i)),
      map o₂ o₂' g y = Occ.map p₂ p₂' (g i) y)
    {Y : J → Type u} {Y' : J → Type u'} (g : ∀ j, Y j → Y' j) :
    ∀ y : F₁ (Y i) ⊕ F₂ (Y i),
      map (sum o₁ o₂) (sum o₁' o₂') g y = Occ.map (Occ.sum p₁ p₂) (Occ.sum p₁' p₂') (g i) y
  | .inl y => congrArg Sum.inl (h₁ g y)
  | .inr y => congrArg Sum.inr (h₂ g y)

end Forms

section Dependent

variable {A : Type a} {ShA : A → Type s} {PosA : ∀ x, ShA x → Type p}
  {FA : A → Type u → Type v} {FA' : A → Type u' → Type w}
  (p : ∀ x, Occ (ShA x) (PosA x) (FA x)) (p' : ∀ x, Occ (ShA x) (PosA x) (FA' x))
  {pidxA : ∀ x (sh : ShA x), PosA x sh → J}
  (o : ∀ x, IOcc (ShA x) (PosA x) (pidxA x) fun Y : J → Type u => FA x (Y i))
  (o' : ∀ x, IOcc (ShA x) (PosA x) (pidxA x) fun Y : J → Type u' => FA' x (Y i))

theorem map_flat_pi
    (h : ∀ x {Y : J → Type u} {Y' : J → Type u'} (g : ∀ j, Y j → Y' j) (y : FA x (Y i)),
      map (o x) (o' x) g y = Occ.map (p x) (p' x) (g i) y)
    {Y : J → Type u} {Y' : J → Type u'} (g : ∀ j, Y j → Y' j) (k : ∀ x, FA x (Y i)) :
    map (pi A o) (pi A o') g k = Occ.map (Occ.pi A p) (Occ.pi A p') (g i) k :=
  funext fun x => h x g (k x)

theorem map_flat_sigma
    (h : ∀ x {Y : J → Type u} {Y' : J → Type u'} (g : ∀ j, Y j → Y' j) (y : FA x (Y i)),
      map (o x) (o' x) g y = Occ.map (p x) (p' x) (g i) y)
    {Y : J → Type u} {Y' : J → Type u'} (g : ∀ j, Y j → Y' j) (z : Σ x, FA x (Y i)) :
    map (sigma A o) (sigma A o') g z = Occ.map (Occ.sigma A p) (Occ.sigma A p') (g i) z :=
  congrArg (Sigma.mk z.1) (h z.1 g z.2)

end Dependent

theorem map_flat_piP {P : Prop} {ShP : P → Type s} {PosP : ∀ h, ShP h → Type p}
    {FP : P → Type u → Type v} {FP' : P → Type u' → Type w}
    (p : ∀ h, Occ (ShP h) (PosP h) (FP h)) (p' : ∀ h, Occ (ShP h) (PosP h) (FP' h))
    {pidxP : ∀ h (sh : ShP h), PosP h sh → J}
    (o : ∀ h, IOcc (ShP h) (PosP h) (pidxP h) fun Y : J → Type u => FP h (Y i))
    (o' : ∀ h, IOcc (ShP h) (PosP h) (pidxP h) fun Y : J → Type u' => FP' h (Y i))
    (hy : ∀ h {Y : J → Type u} {Y' : J → Type u'} (g : ∀ j, Y j → Y' j) (y : FP h (Y i)),
      map (o h) (o' h) g y = Occ.map (p h) (p' h) (g i) y)
    {Y : J → Type u} {Y' : J → Type u'} (g : ∀ j, Y j → Y' j) (k : ∀ h, FP h (Y i)) :
    map (piP P o) (piP P o') g k = Occ.map (Occ.piP P p) (Occ.piP P p') (g i) k :=
  funext fun h => hy h g (k h)

/-- Through a plain type constructor applied to an indexed expression: inside it. -/
theorem map_flat_compC {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {Pos' : Sh' → Type p'}
    {G : Type u'' → Type v} {G' : Type v'' → Type v'} (oG : Occ Sh Pos G) (oG' : Occ Sh Pos G')
    {F : Type u → Type u''} {F' : Type u' → Type v''} (p : Occ Sh' Pos' F) (p' : Occ Sh' Pos' F')
    {pidx' : (sh : Sh') → Pos' sh → J}
    (o : IOcc Sh' Pos' pidx' fun Y : J → Type u => F (Y i))
    (o' : IOcc Sh' Pos' pidx' fun Y : J → Type u' => F' (Y i))
    (h : ∀ {Y : J → Type u} {Y' : J → Type u'} (g : ∀ j, Y j → Y' j) (y : F (Y i)),
      map o o' g y = Occ.map p p' (g i) y)
    {Y : J → Type u} {Y' : J → Type u'} (g : ∀ j, Y j → Y' j) (y : G (F (Y i))) :
    map (compC oG o) (compC oG' o') g y = Occ.map (Occ.comp oG p) (Occ.comp oG' p') (g i) y :=
  congrArg (fun k => Occ.map oG oG' k y) (funext fun z => h g z)

end MapFlat

/-! ### The computation of `Rel` through the indexed combinators

The same lemmas as for `Occ`, so that `simp` computes the premises of the lifting of a family or
of a type of a block at a nested argument: a plain structure at one index is the plain relation at
that index (`rel_ofOcc`). -/

section RelGeneric

variable {J : Type j} {Sh : Type s} {Pos : Sh → Type p} {pidx : (sh : Sh) → Pos sh → J}
  {G : (J → Type u) → Type v} {G' : (J → Type u') → Type v'} {G'' : (J → Type u'') → Type v''}
  {X : J → Type u} {Y : J → Type u'} {W : J → Type u''}

/-- `Rel` through `ofC`: one shape, related contents. -/
theorem rel_iff_ofC (o : IOcc Sh Pos pidx G) (o' : IOcc Sh Pos pidx G')
    {R : ∀ j, X j → Y j → Prop} {x : G X} {y : G' Y} :
    Rel o o' R x y ↔ ∃ (sh : Sh) (c : (q : Pos sh) → X (pidx sh q))
      (c' : (q : Pos sh) → Y (pidx sh q)),
      (∀ q, R _ (c q) (c' q)) ∧ x = o.ofC ⟨sh, c⟩ ∧ y = o'.ofC ⟨sh, c'⟩ := by
  constructor
  · rintro ⟨sh, c, c', hx, hy, h⟩
    exact ⟨sh, c, c', h, by rw [← hx, ofC_toC], by rw [← hy, ofC_toC]⟩
  · rintro ⟨sh, c, c', h, rfl, rfl⟩
    exact rel_intro o o' sh c c' h

/-- A larger relation relates more. -/
theorem Rel.mono (o : IOcc Sh Pos pidx G) (o' : IOcc Sh Pos pidx G')
    {R S : ∀ j, X j → Y j → Prop} (hRS : ∀ j x y, R j x y → S j x y) {x : G X} {y : G' Y}
    (h : Rel o o' R x y) : Rel o o' S x y := by
  obtain ⟨sh, c, c', hx, hy, h⟩ := h
  exact ⟨sh, c, c', hx, hy, fun q => hRS _ _ _ (h q)⟩

/-- A map on the left moves into the relation. -/
@[simp] theorem rel_map_left (o : IOcc Sh Pos pidx G'') (o₁ : IOcc Sh Pos pidx G)
    (o' : IOcc Sh Pos pidx G') {R : ∀ j, X j → Y j → Prop} (f : ∀ j, W j → X j) (x : G'' W)
    (y : G' Y) : Rel o₁ o' R (map o o₁ f x) y ↔ Rel o o' (fun j a b => R j (f j a) b) x y := by
  constructor
  · rintro ⟨sh, c, c', hx, hy, h⟩
    rw [toC_map] at hx
    obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.mp hx
    cases hc
    exact ⟨_, _, c', rfl, hy, h⟩
  · rintro ⟨sh, c, c', hx, hy, h⟩
    refine ⟨sh, fun q => f _ (c q), c', ?_, hy, h⟩
    rw [toC_map, hx]

/-- A map on the right moves into the relation. -/
@[simp] theorem rel_map_right (o : IOcc Sh Pos pidx G) (o₁ : IOcc Sh Pos pidx G'')
    (o' : IOcc Sh Pos pidx G') {R : ∀ j, X j → Y j → Prop} (g : ∀ j, W j → Y j) (x : G X)
    (y : G'' W) : Rel o o' R x (map o₁ o' g y) ↔ Rel o o₁ (fun j a b => R j a (g j b)) x y := by
  constructor
  · rintro ⟨sh, c, c', hx, hy, h⟩
    rw [toC_map] at hy
    obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.mp hy
    cases hc
    exact ⟨_, c, _, hx, rfl, h⟩
  · rintro ⟨sh, c, c', hx, hy, h⟩
    refine ⟨sh, c, fun q => g _ (c' q), hx, ?_, h⟩
    rw [toC_map, hy]

end RelGeneric

section RelForms

variable {J : Type j} {X : J → Type u} {Y : J → Type u'}

/-- A plain structure at one index: the plain relation at that index. -/
@[simp] theorem rel_ofOcc {Sh : Type s} {Pos : Sh → Type p} {G : Type u → Type v}
    {G' : Type u' → Type v'} (o : Occ Sh Pos G) (o' : Occ Sh Pos G') (i : J)
    {R : ∀ j, X j → Y j → Prop} (x : G (X i)) (y : G' (Y i)) :
    Rel (ofOcc o i) (ofOcc o' i) R x y ↔ Occ.Rel o o' (R i) x y := Iff.rfl

@[simp] theorem rel_hole (i : J) (R : ∀ j, X j → Y j → Prop) (x : X i) (y : Y i) :
    Rel (hole i) (hole i) R x y ↔ R i x y := by
  constructor
  · rintro ⟨_, c, c', hx, hy, h⟩
    cases hx
    cases hy
    exact h ()
  · exact fun h => ⟨(), fun _ => x, fun _ => y, rfl, rfl, fun _ => h⟩

@[simp] theorem rel_const {A : Type v} (R : ∀ j, X j → Y j → Prop) (a b : A) :
    Rel (const (J := J) A) (const A) R a b ↔ a = b := by
  constructor
  · rintro ⟨sh, c, c', ha, hb, _⟩
    exact (Sigma.mk.inj_iff.mp ha).1.trans (Sigma.mk.inj_iff.mp hb).1.symm
  · rintro rfl
    exact ⟨a, fun e => e.elim, fun e => e.elim, rfl, rfl, fun q => q.elim⟩

variable {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p} {pidx₁ : (sh : Sh₁) → Pos₁ sh → J}
  {Sh₂ : Type s'} {Pos₂ : Sh₂ → Type p'} {pidx₂ : (sh : Sh₂) → Pos₂ sh → J}
  {G₁ : (J → Type u) → Type v} {G₂ : (J → Type u) → Type v'}
  {G₁' : (J → Type u') → Type w} {G₂' : (J → Type u') → Type w'}
  (o₁ : IOcc Sh₁ Pos₁ pidx₁ G₁) (o₂ : IOcc Sh₂ Pos₂ pidx₂ G₂)
  (o₁' : IOcc Sh₁ Pos₁ pidx₁ G₁') (o₂' : IOcc Sh₂ Pos₂ pidx₂ G₂')

/-- A product, componentwise. -/
@[simp] theorem rel_prod {R : ∀ j, X j → Y j → Prop} (x : G₁ X × G₂ X) (y : G₁' Y × G₂' Y) :
    Rel (prod o₁ o₂) (prod o₁' o₂') R x y ↔ Rel o₁ o₁' R x.1 y.1 ∧ Rel o₂ o₂' R x.2 y.2 := by
  constructor
  · intro h
    obtain ⟨⟨s₁, s₂⟩, c, c', hc, rfl, rfl⟩ := (rel_iff_ofC _ _).mp h
    exact ⟨rel_intro o₁ o₁' s₁ _ _ fun q => hc (.inl q),
      rel_intro o₂ o₂' s₂ _ _ fun q => hc (.inr q)⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨s₁, c₁, c₁', hc₁, hx₁, hy₁⟩ := (rel_iff_ofC _ _).mp h₁
    obtain ⟨s₂, c₂, c₂', hc₂, hx₂, hy₂⟩ := (rel_iff_ofC _ _).mp h₂
    obtain ⟨x₁, x₂⟩ := x
    obtain ⟨y₁, y₂⟩ := y
    dsimp only at hx₁ hx₂ hy₁ hy₂
    subst hx₁ hx₂ hy₁ hy₂
    refine (rel_iff_ofC _ _).mpr ⟨(s₁, s₂), Occ.sumRec c₁ c₂, Occ.sumRec c₁' c₂', ?_, rfl, rfl⟩
    rintro (q | q)
    · exact hc₁ q
    · exact hc₂ q

/-- A sum, by sides: the same side, related values. -/
@[simp] theorem rel_sum_inl_inl {R : ∀ j, X j → Y j → Prop} (x : G₁ X) (y : G₁' Y) :
    Rel (sum o₁ o₂) (sum o₁' o₂') R (.inl x) (.inl y) ↔ Rel o₁ o₁' R x y := by
  constructor
  · intro h
    obtain ⟨sh | sh, c, c', hc, hx, hy⟩ := (rel_iff_ofC _ _).mp h
    · cases hx; cases hy
      exact rel_intro o₁ o₁' sh _ _ fun q => hc ⟨q⟩
    · cases hx
  · intro h
    obtain ⟨sh, c, c', hc, rfl, rfl⟩ := (rel_iff_ofC _ _).mp h
    exact rel_intro (sum o₁ o₂) (sum o₁' o₂') (.inl sh) (fun q => c q.down) (fun q => c' q.down)
      fun q => hc q.down

@[simp] theorem rel_sum_inr_inr {R : ∀ j, X j → Y j → Prop} (x : G₂ X) (y : G₂' Y) :
    Rel (sum o₁ o₂) (sum o₁' o₂') R (.inr x) (.inr y) ↔ Rel o₂ o₂' R x y := by
  constructor
  · intro h
    obtain ⟨sh | sh, c, c', hc, hx, hy⟩ := (rel_iff_ofC _ _).mp h
    · cases hx
    · cases hx; cases hy
      exact rel_intro o₂ o₂' sh _ _ fun q => hc ⟨q⟩
  · intro h
    obtain ⟨sh, c, c', hc, rfl, rfl⟩ := (rel_iff_ofC _ _).mp h
    exact rel_intro (sum o₁ o₂) (sum o₁' o₂') (.inr sh) (fun q => c q.down) (fun q => c' q.down)
      fun q => hc q.down

@[simp] theorem rel_sum_inl_inr {R : ∀ j, X j → Y j → Prop} (x : G₁ X) (y : G₂' Y) :
    Rel (sum o₁ o₂) (sum o₁' o₂') R (.inl x) (.inr y) ↔ False := by
  refine ⟨fun h => ?_, False.elim⟩
  obtain ⟨sh | sh, c, c', hc, hx, hy⟩ := (rel_iff_ofC _ _).mp h
  · cases hy
  · cases hx

@[simp] theorem rel_sum_inr_inl {R : ∀ j, X j → Y j → Prop} (x : G₂ X) (y : G₁' Y) :
    Rel (sum o₁ o₂) (sum o₁' o₂') R (.inr x) (.inl y) ↔ False := by
  refine ⟨fun h => ?_, False.elim⟩
  obtain ⟨sh | sh, c, c', hc, hx, hy⟩ := (rel_iff_ofC _ _).mp h
  · cases hx
  · cases hy

end RelForms

/-- A function from a constant type, pointwise. -/
@[simp] theorem rel_pi {J : Type j} {X : J → Type u} {Y : J → Type u'} {A : Type a}
    {ShA : A → Type s} {PosA : ∀ x, ShA x → Type p} {pidxA : ∀ x (sh : ShA x), PosA x sh → J}
    {GA : A → (J → Type u) → Type v} {GA' : A → (J → Type u') → Type w}
    (o : ∀ x, IOcc (ShA x) (PosA x) (pidxA x) (GA x))
    (o' : ∀ x, IOcc (ShA x) (PosA x) (pidxA x) (GA' x)) {R : ∀ j, X j → Y j → Prop}
    (k : ∀ x, GA x X) (k' : ∀ x, GA' x Y) :
    Rel (pi A o) (pi A o') R k k' ↔ ∀ x, Rel (o x) (o' x) R (k x) (k' x) := by
  constructor
  · intro h x
    obtain ⟨sh, c, c', hc, rfl, rfl⟩ := (rel_iff_ofC _ _).mp h
    exact rel_intro (o x) (o' x) (sh x) _ _ fun q => hc ⟨x, q⟩
  · intro h
    choose sh c c' hc hk hk' using fun x => (rel_iff_ofC _ _).mp (h x)
    exact (rel_iff_ofC _ _).mpr ⟨sh, fun q => c q.1 q.2, fun q => c' q.1 q.2,
      fun q => hc q.1 q.2, funext hk, funext hk'⟩

/-- A plain type constructor applied to an expression with occurrences: the outer relation at the
inner one. -/
@[simp] theorem rel_compC {J : Type j} {X : J → Type u} {Y : J → Type u'} {Sh : Type s}
    {Pos : Sh → Type p} {Sh' : Type s'} {Pos' : Sh' → Type p'} {pidx' : (sh : Sh') → Pos' sh → J}
    {G : Type u'' → Type v} {G' : Type v'' → Type v'} {H : (J → Type u) → Type u''}
    {H' : (J → Type u') → Type v''} (oG : Occ Sh Pos G) (oG' : Occ Sh Pos G')
    (oH : IOcc Sh' Pos' pidx' H) (oH' : IOcc Sh' Pos' pidx' H') {R : ∀ j, X j → Y j → Prop}
    (x : G (H X)) (y : G' (H' Y)) :
    Rel (compC oG oH) (compC oG' oH') R x y ↔ Occ.Rel oG oG' (Rel oH oH' R) x y := by
  constructor
  · intro h
    obtain ⟨⟨sh, t⟩, c, c', hc, rfl, rfl⟩ := (rel_iff_ofC _ _).mp h
    exact Occ.rel_intro oG oG' sh _ _ fun q => rel_intro oH oH' (t q) _ _ fun r => hc ⟨q, r⟩
  · intro h
    obtain ⟨sh, c, c', hc, rfl, rfl⟩ := (Occ.rel_iff_ofC _ _).mp h
    choose t d d' hd hdc hdc' using fun q => (rel_iff_ofC _ _).mp (hc q)
    refine (rel_iff_ofC _ _).mpr ⟨⟨sh, t⟩, fun r => d r.1 r.2, fun r => d' r.1 r.2,
      fun r => hd r.1 r.2, ?_, ?_⟩
    · exact congrArg (fun c => oG.ofC ⟨sh, c⟩) (funext hdc)
    · exact congrArg (fun c => oG'.ofC ⟨sh, c⟩) (funext hdc')


end IOcc

/-! ### The instances of the forms are the combinators

The instances of `PolyIso.lean` for products, sums, functions, dependent pairs and composites
are, by definition, the structures the command builds for these forms from the instances of the
parts. So a nested argument's induction hypothesis at the positions of its structure is one by
membership for the instance of its type (`PolyIso.memRec`), with no proof in between.

They are `simp` lemmas, so that `simp` computes the map of a leaf that is a built-in form, as the
premise of a declared type's rules (`(Occ.ofIso fun X => X × Nat).map …`). The identity's leaf
becomes `hole`, whose map `map_hole_hole` makes the function also where it is not applied, as the
function of another map (`List.map`). -/

namespace Occ

section Agree

variable {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p} {Sh₂ : Type s'} {Pos₂ : Sh₂ → Type p'}
  {G₁ : Type u → Type v} {G₂ : Type u → Type v'} [PolyIso G₁ Sh₁ Pos₁] [PolyIso G₂ Sh₂ Pos₂]

@[simp] theorem ofIso_id : ofIso (fun X : Type u => X) = hole := rfl

@[simp] theorem ofIso_const (A : Type v) : ofIso (fun _ : Type u => A) = const A := rfl

/-- The map of the identity's instance is the function: the map of a field `x : α` in the rules
of a declared type at the identity premise (`Gen/Derive.lean`). -/
@[simp] theorem map_ofIso_id {X : Type u} {Y : Type u'} (f : X → Y) :
    map (ofIso fun X : Type u => X) (ofIso fun X : Type u' => X) f = f := rfl

/-- The map of a constant's instance is the identity. -/
@[simp] theorem map_ofIso_const (A : Type v) {X : Type u} {Y : Type u'} (f : X → Y) (a : A) :
    map (ofIso fun _ : Type u => A) (ofIso fun _ : Type u' => A) f a = a := rfl

@[simp] theorem ofIso_prod : ofIso (fun X => G₁ X × G₂ X) = prod (ofIso G₁) (ofIso G₂) := rfl

@[simp] theorem ofIso_sum : ofIso (fun X => G₁ X ⊕ G₂ X) = sum (ofIso G₁) (ofIso G₂) := rfl

variable {A : Type a} {ShA : A → Type s} {PosA : ∀ x, ShA x → Type p} {GA : A → Type u → Type v}
  [∀ x, PolyIso (GA x) (ShA x) (PosA x)]

@[simp] theorem ofIso_pi : ofIso (fun X => ∀ x, GA x X) = pi A fun x => ofIso (GA x) := rfl

@[simp] theorem ofIso_sigma : ofIso (fun X => Σ x, GA x X) = sigma A fun x => ofIso (GA x) := rfl

@[simp] theorem ofIso_piP {P : Prop} {ShP : P → Type s} {PosP : ∀ h, ShP h → Type p}
    {GP : P → Type u → Type v} [∀ h, PolyIso (GP h) (ShP h) (PosP h)] :
    ofIso (fun X => ∀ h, GP h X) = piP P fun h => ofIso (GP h) := rfl

@[simp] theorem ofIso_comp {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {Pos' : Sh' → Type p'}
    {G : Type u' → Type v} {H : Type u → Type u'} [PolyIso G Sh Pos] [PolyIso H Sh' Pos'] :
    ofIso (fun X => G (H X)) = comp (ofIso G) (ofIso H) := rfl

theorem ofIso_ofI {J : Type j} {Sh : Type s} {Pos : Sh → Type p} {pidx : (sh : Sh) → Pos sh → J}
    {G : (J → Type u) → Type v} [IPolyIso G Sh Pos pidx] :
    ofIso (fun X : Type u => G fun _ => X) = ofI (IOcc.ofIso G) := rfl

theorem ofIso_compI {J : Type j} {Sh : Type s} {Pos : Sh → Type p}
    {pidx : (sh : Sh) → Pos sh → J} {G : (J → Type u') → Type v} [IPolyIso G Sh Pos pidx]
    {Sh' : J → Type s'} {Pos' : ∀ j, Sh' j → Type p'} {H : J → Type u → Type u'}
    [∀ j, PolyIso (H j) (Sh' j) (Pos' j)] :
    ofIso (fun X => G fun j => H j X) = compI (IOcc.ofIso G) fun j => ofIso (H j) := rfl

end Agree

end Occ

namespace IOcc

section Agree

variable {J : Type j} {K : Type k}

@[simp] theorem ofIso_hole (i : J) : ofIso (fun X : J → Type u => X i) = hole i := rfl

@[simp] theorem ofIso_const (A : Type v) : ofIso (fun _ : J → Type u => A) = const A := rfl

@[simp] theorem ofIso_at {F : Type u → Type v} {Sh : Type s} {Pos : Sh → Type p}
    [PolyIso F Sh Pos] (i : J) :
    ofIso (fun X : J → Type u => F (X i)) = ofOcc (Occ.ofIso F) i := rfl

variable {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p} {pidx₁ : (sh : Sh₁) → Pos₁ sh → J}
  {Sh₂ : Type s'} {Pos₂ : Sh₂ → Type p'} {pidx₂ : (sh : Sh₂) → Pos₂ sh → J}
  {G₁ : (J → Type u) → Type v} {G₂ : (J → Type u) → Type v'} [IPolyIso G₁ Sh₁ Pos₁ pidx₁]
  [IPolyIso G₂ Sh₂ Pos₂ pidx₂]

@[simp] theorem ofIso_prod : ofIso (fun X => G₁ X × G₂ X) = prod (ofIso G₁) (ofIso G₂) := rfl

@[simp] theorem ofIso_sum : ofIso (fun X => G₁ X ⊕ G₂ X) = sum (ofIso G₁) (ofIso G₂) := rfl

variable {A : Type a} {ShA : A → Type s} {PosA : ∀ x, ShA x → Type p}
  {pidxA : ∀ x (sh : ShA x), PosA x sh → J} {GA : A → (J → Type u) → Type v}
  [∀ x, IPolyIso (GA x) (ShA x) (PosA x) (pidxA x)]

@[simp] theorem ofIso_pi : ofIso (fun X => ∀ x, GA x X) = pi A fun x => ofIso (GA x) := rfl

@[simp] theorem ofIso_sigma : ofIso (fun X => Σ x, GA x X) = sigma A fun x => ofIso (GA x) := rfl

@[simp] theorem ofIso_piP {P : Prop} {ShP : P → Type s} {PosP : ∀ h, ShP h → Type p}
    {pidxP : ∀ h (sh : ShP h), PosP h sh → J} {GP : P → (J → Type u) → Type v}
    [∀ h, IPolyIso (GP h) (ShP h) (PosP h) (pidxP h)] :
    ofIso (fun X => ∀ h, GP h X) = piP P fun h => ofIso (GP h) := rfl

variable {Sh : Type s} {Pos : Sh → Type p} {Sh' : Type s'} {Pos' : Sh' → Type p'}

@[simp] theorem ofIso_compC {G : Type u' → Type v} [PolyIso G Sh Pos]
    {pidx' : (sh : Sh') → Pos' sh → J} {H : (J → Type u) → Type u'} [IPolyIso H Sh' Pos' pidx'] :
    ofIso (fun X => G (H X)) = compC (Occ.ofIso G) (ofIso H) := rfl

@[simp] theorem ofIso_reidx {pidx : (sh : Sh) → Pos sh → K} {G : (K → Type u) → Type v}
    [IPolyIso G Sh Pos pidx] (g : K → J) :
    ofIso (fun X : J → Type u => G fun k => X (g k)) = reidx (ofIso G) g := rfl

@[simp] theorem ofIso_compI {pidx : (sh : Sh) → Pos sh → K} {G : (K → Type u') → Type v}
    [IPolyIso G Sh Pos pidx] {Sh' : K → Type s'} {Pos' : ∀ k, Sh' k → Type p'}
    {pidx' : ∀ k (sh : Sh' k), Pos' k sh → J} {H : K → (J → Type u) → Type u'}
    [∀ k, IPolyIso (H k) (Sh' k) (Pos' k) (pidx' k)] :
    ofIso (fun X => G fun k => H k X) = compI (ofIso G) fun k => ofIso (H k) := rfl

end Agree

end IOcc

/-- Images under a function of a family of values, chosen pointwise: the elimination of the
hypotheses on arguments under a telescope in the generated `rel_ctorᵢ` lemmas. -/
theorem exists_fn_of_forall {A : Sort u} {W : A → Sort u'} {X : A → Sort u''} {Y : A → Sort v}
    (fst : ∀ a, W a → X a) (snd : ∀ a, W a → Y a) {g : ∀ a, X a} {g' : ∀ a, Y a}
    (h : ∀ a, ∃ w, fst a w = g a ∧ snd a w = g' a) :
    ∃ w : ∀ a, W a, (fun a => fst a (w a)) = g ∧ (fun a => snd a (w a)) = g' := by
  choose w hw using h
  exact ⟨w, funext fun a => (hw a).1, funext fun a => (hw a).2⟩

end Codata
