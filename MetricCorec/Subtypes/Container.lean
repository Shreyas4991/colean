import Mathlib.Data.List.OfFn
import MetricCorec.Subtypes.Codata

/-!
# Containers, for nested occurrences

A constructor argument `children : List (T i)` is a nested occurrence of the type being defined,
through `List`. Any type constructor `G` with an isomorphism `G X ≅ Σ sh, Pos sh → X`, natural
in `X` and with shapes and positions independent of `X`, is a *container*, and a nested
occurrence through it is reduced to the position family of `Codata.lean`: the container's shape
is non-recursive data of the constructor, and its positions are recursive positions. So the
generic theory needs nothing new; the command keeps `G X` in the user-facing functor `F` and
goes through the container's isomorphism in `toC`/`ofC` (`Container.toC`, `Container.ofC`),
with the action on functions `Container.map` and the lifting to relations `Container.Rel`, whose
laws are proved here once.

`map` and `Rel` go between two instances of the class, `G` at one universe and `G'` at another
(`List.{u}` and `List.{v}`), with the same shapes and positions: this is what keeps the state of
`corec` and `fold` in any universe. The instances below (`List`, `Option`, `Prod α`) are the
registry of types allowed in nested positions, together with every type declared by `data` or
`codata` with a type parameter used only at parameter positions (`Param.lean`); the simp lemmas
`map_list`, `map_option`, `map_prod` bring `Container.map` back to the usual maps, and
`mem_toC_list`, `toC_list_mem` relate the positions of a list to membership, for induction
hypotheses.
-/

universe u u' u'' v v' v'' s p j

namespace Codata

/-- A container structure on a type constructor `G`: an equivalence `G X ≃ Σ sh, Pos sh → X`
for every `X`, with the shapes `Sh` and the positions `Pos` independent of `X`. The right-hand
side is `PFunctor.Obj ⟨Sh, Pos⟩ X`: `G` is the polynomial functor with these shapes and
positions, and `Container.map` (defined through the equivalence) is its action on functions. -/
class Container (G : Type u → Type v) (Sh : outParam (Type s)) (Pos : outParam (Sh → Type p)) where
  equiv {X : Type u} : G X ≃ Σ sh, Pos sh → X

namespace Container

variable {Sh : Type s} {Pos : Sh → Type p}
variable {G : Type u → Type v} [Container G Sh Pos] {G' : Type u' → Type v'} [Container G' Sh Pos]
  {G'' : Type u'' → Type v''} [Container G'' Sh Pos]
variable {X : Type u} {Y : Type u'} {Z : Type u''}

/-- The layer of a container value: its shape and its contents. -/
def toC (x : G X) : Σ sh, Pos sh → X := equiv x

/-- The container value of a layer. -/
def ofC (z : Σ sh, Pos sh → X) : G X := equiv.symm z

theorem ofC_toC (x : G X) : ofC (toC x) = x := equiv.symm_apply_apply x

theorem toC_ofC (z : Σ sh, Pos sh → X) : toC (G := G) (ofC z) = z := equiv.apply_symm_apply z

/-- The action on functions, through the containers: the target `G'` is determined by the
expected type. -/
def map (f : X → Y) (x : G X) : G' Y := ofC ⟨(toC x).1, fun q => f ((toC x).2 q)⟩

/-- `ofC_toC` with the layer written out, as it appears in the generated `ofC (toC a)`. -/
theorem ofC_toC' (x : G X) : ofC ⟨(toC x).1, fun q => (toC x).2 q⟩ = x := ofC_toC x

theorem map_id (x : G X) : map (G' := G) (fun x => x) x = x := ofC_toC x

theorem map_id' (x : G X) : map (G' := G) id x = x := ofC_toC x

theorem map_ofC (f : X → Y) (sh : Sh) (c : Pos sh → X) :
    map (G' := G') f (ofC (G := G) ⟨sh, c⟩) = ofC ⟨sh, fun q => f (c q)⟩ := by
  unfold map
  rw [toC_ofC]

theorem map_map (g : Y → Z) (f : X → Y) (x : G X) :
    map (G' := G'') g (map (G' := G') f x) = map (fun x => g (f x)) x := by
  unfold map
  rw [toC_ofC]

/-- The lifting to relations: the same shape and related contents. -/
def Rel (R : X → Y → Prop) (x : G X) (y : G' Y) : Prop :=
  ∃ (sh : Sh) (c : Pos sh → X) (c' : Pos sh → Y),
    toC x = ⟨sh, c⟩ ∧ toC y = ⟨sh, c'⟩ ∧ ∀ q, R (c q) (c' q)

theorem rel_map (R : Y → Z → Prop) (f : X → Y) (g : X → Z) (x : G X)
    (h : ∀ x, R (f x) (g x)) : Rel R (map (G' := G') f x) (map (G' := G'') g x) :=
  ⟨(toC x).1, fun q => f ((toC x).2 q), fun q => g ((toC x).2 q),
    by unfold map; rw [toC_ofC], by unfold map; rw [toC_ofC], fun q => h _⟩

/-- Two layers with the same shape and related contents are related. -/
theorem rel_intro {R : X → Y → Prop} (sh : Sh) (c : Pos sh → X) (c' : Pos sh → Y)
    (h : ∀ q, R (c q) (c' q)) : Rel R (ofC (G := G) ⟨sh, c⟩) (ofC (G := G') ⟨sh, c'⟩) :=
  ⟨sh, c, c', toC_ofC _, toC_ofC _, h⟩

/-- Related layers have the same shape and related contents; used by the generated `rel_ofC`,
where the shapes are pattern variables and the equation is substituted. -/
theorem rel_ofC {R : X → Y → Prop} {sh sh' : Sh} {f : Pos sh → X} {f' : Pos sh' → Y}
    (h : Rel R (ofC (G := G) ⟨sh, f⟩) (ofC (G := G') ⟨sh', f'⟩)) :
    ∃ e : sh = sh', ∀ q, R (f q) (f' (e ▸ q)) := by
  obtain ⟨sh₀, c, c', h1, h2, hR⟩ := h
  rw [toC_ofC] at h1 h2
  cases h1
  cases h2
  exact ⟨rfl, hR⟩

/-! ### The registry: `List`, `Option`, `Prod α` -/

instance : Container List Nat Fin where
  equiv := List.equivSigmaTuple

@[simp] theorem toC_list (l : List X) : toC l = ⟨l.length, l.get⟩ := rfl

@[simp] theorem ofC_list {n : Nat} (f : Fin n → X) : ofC ⟨n, f⟩ = List.ofFn f := rfl

@[simp] theorem map_list (f : X → Y) (l : List X) : map (G' := List) f l = l.map f :=
  calc map (G' := List) f l = List.ofFn (f ∘ l.get) := rfl
    _ = List.map f (List.ofFn l.get) := (List.map_ofFn _ _).symm
    _ = l.map f := by rw [List.ofFn_get]

/-- The element at a position of a list is a member. -/
theorem toC_list_mem (l : List X) (q : Fin (toC l).1) : (toC l).2 q ∈ l := List.get_mem l q

/-- A member of a list is the element at some position. -/
theorem mem_toC_list {l : List X} {x : X} (hx : x ∈ l) : ∃ q, (toC l).2 q = x :=
  List.mem_iff_get.mp hx

/-- The induction hypothesis of a nested list, in terms of membership. -/
theorem forall_toC_list {P : X → Prop} (l : List X) :
    (∀ q, P ((toC l).2 q)) ↔ ∀ x ∈ l, P x :=
  ⟨fun h x hx => by obtain ⟨q, rfl⟩ := mem_toC_list hx; exact h q,
    fun h q => h _ (toC_list_mem l q)⟩

/-- The positions of `Option`: one when the shape is `true`, none when it is `false`. -/
inductive OptionPos : Bool → Type
  | unit : OptionPos true

instance : Container Option Bool OptionPos where
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

@[simp] theorem map_option (f : X → Y) (o : Option X) : map (G' := Option) f o = o.map f := by
  cases o <;> rfl

instance {α : Type u} : Container (Prod α) α (fun _ => Unit) where
  equiv := ⟨fun x => ⟨x.1, fun _ => x.2⟩, fun z => (z.1, z.2 ()), fun _ => rfl, fun _ => rfl⟩

@[simp] theorem map_prod {α : Type v} (f : X → Y) (x : α × X) :
    map (G' := Prod α) f x = (x.1, f x.2) := rfl

end Container

/-! ### Indexed containers, for nested occurrences of families

A type constructor on families, `G : (J → Type u) → Type v`, with `G X ≃ Σ sh, (q : Pos sh) → X
(pidx sh q)`: every position carries an index of the family. A `Container` is the case
`J = Unit`. A nested occurrence `G (fun j => T params (idx j))` of a family being defined is
reduced to recursive positions `q : Pos sh` at the index `idx (pidx sh q)`. -/

class IContainer {J : Type j} (G : (J → Type u) → Type v) (Sh : outParam (Type s))
    (Pos : outParam (Sh → Type p)) (pidx : outParam ((sh : Sh) → Pos sh → J)) where
  equiv {X : J → Type u} : G X ≃ Σ sh, (q : Pos sh) → X (pidx sh q)

namespace IContainer

variable {J : Type j} {Sh : Type s} {Pos : Sh → Type p} {pidx : (sh : Sh) → Pos sh → J}
variable {G : (J → Type u) → Type v} [IContainer G Sh Pos pidx]
  {G' : (J → Type u') → Type v'} [IContainer G' Sh Pos pidx]
  {G'' : (J → Type u'') → Type v''} [IContainer G'' Sh Pos pidx]
variable {X : J → Type u} {Y : J → Type u'} {Z : J → Type u''}

def toC (x : G X) : Σ sh, (q : Pos sh) → X (pidx sh q) := equiv x

def ofC (z : Σ sh, (q : Pos sh) → X (pidx sh q)) : G X := equiv.symm z

theorem ofC_toC (x : G X) : ofC (toC x) = x := equiv.symm_apply_apply x

theorem toC_ofC (z : Σ sh, (q : Pos sh) → X (pidx sh q)) : toC (G := G) (ofC z) = z :=
  equiv.apply_symm_apply z

def map (f : ∀ j, X j → Y j) (x : G X) : G' Y := ofC ⟨(toC x).1, fun q => f _ ((toC x).2 q)⟩

theorem ofC_toC' (x : G X) : ofC ⟨(toC x).1, fun q => (toC x).2 q⟩ = x := ofC_toC x

theorem map_id (x : G X) : map (G' := G) (fun _ x => x) x = x := ofC_toC x

theorem map_id' (x : G X) : map (G' := G) (fun _ => id) x = x := ofC_toC x

theorem map_ofC (f : ∀ j, X j → Y j) (sh : Sh) (c : (q : Pos sh) → X (pidx sh q)) :
    map (G' := G') f (ofC (G := G) ⟨sh, c⟩) = ofC ⟨sh, fun q => f _ (c q)⟩ := by
  unfold map
  rw [toC_ofC]

theorem map_map (g : ∀ j, Y j → Z j) (f : ∀ j, X j → Y j) (x : G X) :
    map (G' := G'') g (map (G' := G') f x) = map (fun j x => g j (f j x)) x := by
  unfold map
  rw [toC_ofC]

def Rel (R : ∀ j, X j → Y j → Prop) (x : G X) (y : G' Y) : Prop :=
  ∃ (sh : Sh) (c : (q : Pos sh) → X (pidx sh q)) (c' : (q : Pos sh) → Y (pidx sh q)),
    toC x = ⟨sh, c⟩ ∧ toC y = ⟨sh, c'⟩ ∧ ∀ q, R _ (c q) (c' q)

theorem rel_map (R : ∀ j, Y j → Z j → Prop) (f : ∀ j, X j → Y j) (g : ∀ j, X j → Z j) (x : G X)
    (h : ∀ j x, R j (f j x) (g j x)) : Rel R (map (G' := G') f x) (map (G' := G'') g x) :=
  ⟨(toC x).1, fun q => f _ ((toC x).2 q), fun q => g _ ((toC x).2 q),
    by unfold map; rw [toC_ofC], by unfold map; rw [toC_ofC], fun q => h _ _⟩

theorem rel_intro {R : ∀ j, X j → Y j → Prop} (sh : Sh) (c : (q : Pos sh) → X (pidx sh q))
    (c' : (q : Pos sh) → Y (pidx sh q)) (h : ∀ q, R _ (c q) (c' q)) :
    Rel R (ofC (G := G) ⟨sh, c⟩) (ofC (G := G') ⟨sh, c'⟩) :=
  ⟨sh, c, c', toC_ofC _, toC_ofC _, h⟩

theorem rel_ofC {R : ∀ j, X j → Y j → Prop} {sh sh' : Sh} {f : (q : Pos sh) → X (pidx sh q)}
    {f' : (q : Pos sh') → Y (pidx sh' q)}
    (h : Rel R (ofC (G := G) ⟨sh, f⟩) (ofC (G := G') ⟨sh', f'⟩)) :
    ∃ e : sh = sh', ∀ q, R _ (f q) ((e ▸ f') q) := by
  obtain ⟨sh₀, c, c', h1, h2, hR⟩ := h
  rw [toC_ofC] at h1 h2
  cases h1
  cases h2
  exact ⟨rfl, hR⟩

end IContainer

end Codata
