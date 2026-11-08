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
and `fold` in any universe. The simp lemmas `map_list`, `map_prod`, `map_comp`, … compute `map`
through the combinators back to the usual maps (`List.map`, pairs, composition), the `rel_*`
lemmas do the same for `Rel`, and `forall_toC_*` turn "for every position" into membership or
components, for induction hypotheses.

The indexed version `IOcc` is for occurrences of a *family*: every position carries an index,
`G X ≃ Σ sh, (q : Pos sh) → X (pidx sh q)`, so that occurrences at different indices may live
in one argument (`T i × T j`), and a functor on families with an `IPolyIso` instance is an
indexed leaf (`IOcc.ofIso`). `Occ` is the case of a single index; `IOcc.ofOcc` puts a plain
structure at a fixed index, `IOcc.reidx` and `Occ.ofI` reindex a family leaf, and `compC`,
`compI`, `Occ.compI` are the compositions across the two kinds.
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

/-! ### The combinators, plain

Every combinator is defined by its two maps directly, so that `toC`, `ofC` and `map` compute
through it by `rfl` (the `toC_*` and `map_*` lemmas below). The inverse laws rewrite
`toC (ofC z)` in dependent positions, which `rw` cannot do; the layer is generalised first. -/

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

/-- Dependent case analysis on a sum, for the positions of a product. -/
def sumRec {α : Type u} {β : Type v} {γ : α ⊕ β → Sort s} (f : ∀ a, γ (.inl a))
    (g : ∀ b, γ (.inr b)) : ∀ x, γ x
  | .inl a => f a
  | .inr b => g b

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

/-- The positions of a sum, lifted to one universe. -/
def SumPos (Pos₁ : Sh₁ → Type p) (Pos₂ : Sh₂ → Type p') : Sh₁ ⊕ Sh₂ → Type (max p p')
  | .inl sh => ULift.{p'} (Pos₁ sh)
  | .inr sh => ULift.{p} (Pos₂ sh)

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

/-- The indices of the positions of a sum. -/
def sumIdx (pidx₁ : (sh : Sh₁) → Pos₁ sh → J) (pidx₂ : (sh : Sh₂) → Pos₂ sh → J) :
    (sh : Sh₁ ⊕ Sh₂) → Occ.SumPos Pos₁ Pos₂ sh → J
  | .inl sh, q => pidx₁ sh q.down
  | .inr sh, q => pidx₂ sh q.down

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

theorem forall_toC_prod {P : X → Prop} (x : G₁ X × G₂ X) :
    (∀ q, P (((prod o₁ o₂).toC x).2 q)) ↔
      (∀ q, P ((o₁.toC x.1).2 q)) ∧ ∀ q, P ((o₂.toC x.2).2 q) :=
  ⟨fun h => ⟨fun q => h (.inl q), fun q => h (.inr q)⟩,
    fun h q => by cases q with | inl q => exact h.1 q | inr q => exact h.2 q⟩

theorem rel_const {A : Type v} (R : X → Y → Prop) (a b : A) :
    Rel (const A) (const A) R a b ↔ a = b := by
  constructor
  · rintro ⟨sh, c, c', ha, hb, _⟩
    exact (Sigma.mk.inj_iff.mp ha).1.trans (Sigma.mk.inj_iff.mp hb).1.symm
  · rintro rfl
    exact ⟨a, Empty.elim, Empty.elim, rfl, rfl, fun q => q.elim⟩

theorem rel_hole (R : X → Y → Prop) (x : X) (y : Y) : Rel hole hole R x y ↔ R x y := by
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

end Occ

/-- Images under a function of a family of values, chosen pointwise: the elimination of the
hypotheses on arguments under a telescope in the generated `rel_ctorᵢ` lemmas. -/
theorem exists_fn_of_forall {A : Sort u} {W : A → Sort u'} {X : A → Sort u''} {Y : A → Sort v}
    (fst : ∀ a, W a → X a) (snd : ∀ a, W a → Y a) {g : ∀ a, X a} {g' : ∀ a, Y a}
    (h : ∀ a, ∃ w, fst a w = g a ∧ snd a w = g' a) :
    ∃ w : ∀ a, W a, (fun a => fst a (w a)) = g ∧ (fun a => snd a (w a)) = g' := by
  choose w hw using h
  exact ⟨w, funext fun a => (hw a).1, funext fun a => (hw a).2⟩

end Codata
