import Colean.Model.Occ
import Colean.Model.Intype

/-! # Scratch: one occurrence structure per constructor argument

The mechanism explored here. The command does not look for a `Container` instance for the
whole argument type of a constructor (`fun X => List X`, `fun X => X × X`, …). It builds, by
recursion on the syntax of the argument type, its *occurrence structure* `Occ`: a shape (the
part of a value outside the holes), positions (the holes) and the equivalence, composed from a
few combinators, one per way the recursive type can occur:

* a constant, a hole, a product, a sum, a `Π`, a `Σ`;
* a named functor applied to an expression with holes (`List (…)`, `Option (…)`, a previously
  declared type), where a container instance for the named functor alone is the leaf.

So `X × X`, `A → X × List X`, `Option (List X)`, … are all handled, and instance search happens
only at named functors. The occurrence structure of the whole constructor list is the
signature: one index, its shapes, its positions. From there the existing theory applies
unchanged: `Raw`, the fixpoint predicates, `Intype`/`Cotype`, `ctorI`/`foldI`/`recI`,
`corecC`/`dtorC`, and their transports to the user-facing functor. `Occ` is a container, bundled;
what changes is who builds it.

The file instantiates this by hand for rose trees (inductive and coinductive) and, for the
`X × X` case, for binary trees, with the type parameter fixed. The multi-hole version, with
the parameter as one more hole, is what makes a declared type a container in its parameter. -/

universe u v s p u' v' s' p' a

open Codata Codata.Signature

namespace OccSketch

/-- The occurrence structure of a type expression `F` with a hole: values are a shape and,
over the positions of that shape, the contents of the hole. -/
structure Occ (F : Type u → Type v) where
  Sh : Type s
  Pos : Sh → Type p
  equiv (X : Type u) : F X ≃ Σ sh, Pos sh → X

namespace Occ

/-! ### The combinators -/

/-- A constant: the value is the shape, there are no positions. -/
def const (A : Type v) : Occ.{u, v, v, 0} fun _ => A where
  Sh := A
  Pos _ := Empty
  equiv _ := {
    toFun a := ⟨a, Empty.elim⟩
    invFun z := z.1
    left_inv _ := rfl
    right_inv := fun ⟨_, _⟩ => congrArg _ (funext fun x => x.elim) }

/-- The hole: one shape, one position. -/
def hole : Occ.{u, u, 0, 0} fun X => X where
  Sh := Unit
  Pos _ := Unit
  equiv _ := {
    toFun x := ⟨(), fun _ => x⟩
    invFun z := z.2 ()
    left_inv _ := rfl
    right_inv _ := rfl }

/-- The layers of a product: a pair of shapes, the sum of the positions. -/
def prodEquiv {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p} {Sh₂ : Type s'} {Pos₂ : Sh₂ → Type p'}
    (X : Type u) :
    (Σ sh, Pos₁ sh → X) × (Σ sh, Pos₂ sh → X) ≃ Σ sh : Sh₁ × Sh₂, Pos₁ sh.1 ⊕ Pos₂ sh.2 → X where
  toFun z := ⟨(z.1.1, z.2.1), Sum.elim z.1.2 z.2.2⟩
  invFun z := (⟨z.1.1, fun q => z.2 (.inl q)⟩, ⟨z.1.2, fun q => z.2 (.inr q)⟩)
  left_inv _ := rfl
  right_inv := fun ⟨_, _⟩ => congrArg _ (funext fun | .inl _ => rfl | .inr _ => rfl)

def prod {F₁ : Type u → Type v} {F₂ : Type u → Type v'} (o₁ : Occ.{u, v, s, p} F₁)
    (o₂ : Occ.{u, v', s', p'} F₂) : Occ fun X => F₁ X × F₂ X where
  Sh := o₁.Sh × o₂.Sh
  Pos sh := o₁.Pos sh.1 ⊕ o₂.Pos sh.2
  equiv X := (Equiv.prodCongr (o₁.equiv X) (o₂.equiv X)).trans (prodEquiv X)

/-- The layers of a sum: a shape of either side, its positions. -/
def sumEquiv {Sh₁ : Type s} {Pos₁ : Sh₁ → Type p} {Sh₂ : Type s'} {Pos₂ : Sh₂ → Type p}
    (X : Type u) :
    (Σ sh, Pos₁ sh → X) ⊕ (Σ sh, Pos₂ sh → X) ≃ Σ sh : Sh₁ ⊕ Sh₂, Sum.elim Pos₁ Pos₂ sh → X where
  toFun
    | .inl ⟨sh, c⟩ => ⟨.inl sh, c⟩
    | .inr ⟨sh, c⟩ => ⟨.inr sh, c⟩
  invFun
    | ⟨.inl sh, c⟩ => .inl ⟨sh, c⟩
    | ⟨.inr sh, c⟩ => .inr ⟨sh, c⟩
  left_inv
    | .inl _ => rfl
    | .inr _ => rfl
  right_inv
    | ⟨.inl _, _⟩ => rfl
    | ⟨.inr _, _⟩ => rfl

def sum {F₁ : Type u → Type v} {F₂ : Type u → Type v'} (o₁ : Occ.{u, v, s, p} F₁)
    (o₂ : Occ.{u, v', s', p} F₂) : Occ fun X => F₁ X ⊕ F₂ X where
  Sh := o₁.Sh ⊕ o₂.Sh
  Pos := Sum.elim o₁.Pos o₂.Pos
  equiv X := (Equiv.sumCongr (o₁.equiv X) (o₂.equiv X)).trans (sumEquiv X)

/-- A `Π` over a constant type: a shape at every point, a point with a position there. -/
def pi (A : Type a) {F : A → Type u → Type v} (o : ∀ x, Occ.{u, v, s, p} (F x)) :
    Occ fun X => ∀ x, F x X where
  Sh := ∀ x, (o x).Sh
  Pos sh := Σ x, (o x).Pos (sh x)
  equiv X := (piCongrRightT fun x => (o x).equiv X).trans
    ((piSigmaEquiv' fun x sh => (o x).Pos sh → X).trans
      (Equiv.sigmaCongrRight fun _ => (sigmaCurryEquiv fun _ _ => X).symm))

/-- A `Σ` over a constant type: a point with a shape there, its positions. -/
def sigma (A : Type a) {F : A → Type u → Type v} (o : ∀ x, Occ.{u, v, s, p} (F x)) :
    Occ fun X => Σ x, F x X where
  Sh := Σ x, (o x).Sh
  Pos sh := (o sh.1).Pos sh.2
  equiv X := (Equiv.sigmaCongrRight fun x => (o x).equiv X).trans
    (Equiv.sigmaAssoc fun x sh => (o x).Pos sh → X).symm

/-- A named functor applied to an expression with holes: composition of the structures. -/
def comp {G : Type u' → Type v} (oG : Occ.{u', v, s, p} G) {F : Type u → Type u'}
    (o : Occ.{u, u', s', p'} F) : Occ fun X => G (F X) where
  Sh := Σ sh, oG.Pos sh → o.Sh
  Pos z := Σ q, o.Pos (z.2 q)
  equiv X := compEquiv (oG.equiv (F X)) (o.equiv X)

/-- The leaf: a named functor with a container instance. -/
def ofContainer (G : Type u → Type v) {Sh : Type s} {Pos : Sh → Type p} [Container G Sh Pos] :
    Occ G :=
  ⟨Sh, Pos, fun _ => Container.equiv⟩

/-! ### What a structure gives: the map, the signature, the transports -/

variable {F : Type u → Type v} (o : Occ.{u, v, s, p} F)

/-- The action on functions induced by the structure. -/
def map {X Y : Type u} (f : X → Y) (y : F X) : F Y :=
  (o.equiv Y).symm ⟨(o.equiv X y).1, fun q => f ((o.equiv X y).2 q)⟩

/-- The signature: one index, the shapes and positions of the structure. -/
def sig : Signature.{0, s, s, p} where
  I := PUnit
  Shape _ := o.Sh
  Shape₀ _ := o.Sh
  sh₀ := id
  B _ sh := o.Pos sh
  idx {i} {_s} _ := i

/-- The container of the signature is the layer type of the structure. -/
def objEquiv {X : PUnit → Type u} {i : PUnit} : o.sig.Obj X i ≃ Σ sh, o.Pos sh → X i where
  toFun z := ⟨z.shape, z.child⟩
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The transport of a layer of `F` to the container of the signature. -/
def layerEquiv {X : PUnit → Type u} {i : PUnit} : F (X i) ≃ o.sig.Obj X i :=
  (o.equiv _).trans o.objEquiv.symm

def toC {X : PUnit → Type u} {i : PUnit} (y : F (X i)) : o.sig.Obj X i := o.layerEquiv y

def ofC {X : PUnit → Type u} {i : PUnit} (z : o.sig.Obj X i) : F (X i) := o.layerEquiv.symm z

theorem toC_ofC {X : PUnit → Type u} {i : PUnit} (z : o.sig.Obj X i) : o.toC (o.ofC z) = z :=
  o.layerEquiv.apply_symm_apply z

theorem ofC_toC {X : PUnit → Type u} {i : PUnit} (y : F (X i)) : o.ofC (o.toC y) = y :=
  o.layerEquiv.symm_apply_apply y

/-- The map on a layer given by its shape and contents. -/
theorem map_symm {X Y : Type u} (f : X → Y) (sh : o.Sh) (c : o.Pos sh → X) :
    o.map f ((o.equiv X).symm ⟨sh, c⟩) = (o.equiv Y).symm ⟨sh, fun q => f (c q)⟩ := by
  have key : ∀ w : Σ sh, o.Pos sh → X, w = ⟨sh, c⟩ →
      (o.equiv Y).symm ⟨w.1, fun q => f (w.2 q)⟩ = (o.equiv Y).symm ⟨sh, fun q => f (c q)⟩ := by
    rintro w rfl; rfl
  exact key _ ((o.equiv X).apply_symm_apply _)

theorem ofC_map {X Y : PUnit → Type u} (f : ∀ j, X j → Y j) {i : PUnit} (z : o.sig.Obj X i) :
    o.ofC (Obj.map f z) = o.map (f i) (o.ofC z) :=
  (o.map_symm (f i) z.shape z.child).symm

/-! ### The types, from the generic theory -/

section Types

variable {F : Type (max s p) → Type v} (o : Occ.{max s p, v, s, p} F)

/-- The inductive type. -/
def Intype : Type (max s p) := o.sig.Intype ⟨⟩

/-- The coinductive type. -/
def Cotype : Type (max s p) := o.sig.Cotype ⟨⟩

noncomputable def ctor (y : F o.Intype) : o.Intype := ctorI (o.toC (X := fun _ => o.Intype) y)

noncomputable def fold {S : Type (max s p)} (alg : F S → S) (t : o.Intype) : S :=
  foldI (S := fun _ => S) (fun _ z => alg (o.ofC z)) t

theorem fold_ctor {S : Type (max s p)} (alg : F S → S) (y : F o.Intype) :
    o.fold alg (o.ctor y) = alg (o.map (o.fold alg) y) :=
  fold_ctor_of (FT := fun _ => F o.Intype) (FS := fun _ => F S) (fun {_} y => o.toC y)
    (fun {_} z => o.ofC z) (fun {_} z => o.ofC z) (fun f {i} y => o.map (f i) y)
    (fun {i} y => o.ofC_toC (X := o.sig.Intype) (i := i) y) (fun f {_} z => o.ofC_map f z)
    (fun _ => alg) y

/-- Induction, with the hypotheses at the positions. -/
theorem induction {motive : o.Intype → Prop}
    (H : ∀ y : F o.Intype,
      (∀ q, motive ((o.toC (X := fun _ => o.Intype) (i := ⟨⟩) y).child q)) →
      motive (o.ctor y)) (t : o.Intype) : motive t :=
  rec_of (FT := fun _ => F o.Intype) (motive := fun _ t => motive t) (fun {_} y => o.toC y)
    (fun {_} z => o.ofC z) (fun {_} z => o.toC_ofC z) (fun _ y ih => H y ih) t

noncomputable def corec {S : Type (max s p)} (c : S → F S) (st : S) : o.Cotype :=
  corecC (S := fun _ => S) (fun _ st => o.toC (X := fun _ => S) (c st)) st

def dtor (t : o.Cotype) : F o.Cotype := o.ofC (X := fun _ => o.Cotype) (dtorC t)

theorem dtor_corec {S : Type (max s p)} (c : S → F S) (st : S) :
    o.dtor (o.corec c st) = o.map (o.corec c) (c st) :=
  dtor_corec_of (FS := fun _ => F S) (FT := fun _ => F o.Cotype) (fun {_} y => o.toC y)
    (fun {_} z => o.ofC z) (fun {_} z => o.ofC z) (fun f {i} y => o.map (f i) y)
    (fun {i} y => o.ofC_toC (X := fun _ => S) (i := i) y) (fun f {_} z => o.ofC_map f z)
    (fun _ => c) st

end Types

end Occ

/-! ## Rose trees: `node (a : α) (children : List (Rose α))` -/

section Rose

variable (α : Type u)

/-- The layer functor. -/
abbrev RoseF (X : Type u) : Type u := α × List X

/-- Its occurrence structure: the product of a constant and of the named functor `List` at
the hole. -/
def roseOcc : Occ.{u, u, u, 0} (RoseF α) := Occ.prod (Occ.const α) (Occ.ofContainer List)

def Rose : Type u := (roseOcc α).Intype

variable {α}

/-- The transport computed on a layer: the shape is the value and the length, the positions
are the indices of the list. -/
theorem roseOcc_equiv (a : α) {X : Type u} (cs : List X) :
    (roseOcc α).equiv X (a, cs) = ⟨(a, cs.length), Sum.elim Empty.elim cs.get⟩ := rfl

/-- The induced map is the expected one. -/
theorem roseOcc_map {X Y : Type u} (f : X → Y) (a : α) (cs : List X) :
    (roseOcc α).map f (a, cs) = (a, cs.map f) := by
  show (a, List.ofFn (f ∘ cs.get)) = _
  rw [← List.map_ofFn, List.ofFn_get]

namespace Rose

noncomputable def node (a : α) (cs : List (Rose α)) : Rose α := (roseOcc α).ctor (a, cs)

noncomputable def fold {S : Type u} (alg : α → List S → S) (t : Rose α) : S :=
  (roseOcc α).fold (fun y => alg y.1 y.2) t

theorem fold_node {S : Type u} (alg : α → List S → S) (a : α) (cs : List (Rose α)) :
    fold alg (node a cs) = alg a (cs.map (fold alg)) := by
  rw [fold, node, Occ.fold_ctor, roseOcc_map]
  rfl

/-- Induction with membership: the positions of the layer `(a, cs)` are the indices of `cs`. -/
theorem induction {motive : Rose α → Prop}
    (H : ∀ a (cs : List (Rose α)), (∀ c ∈ cs, motive c) → motive (node a cs)) (t : Rose α) :
    motive t :=
  (roseOcc α).induction (motive := motive)
    (fun y ih => H y.1 y.2 fun c hc => by
      obtain ⟨q, rfl⟩ := List.mem_iff_get.mp hc
      exact ih (.inr q))
    t

/-- The labels in preorder. -/
noncomputable def flatten (t : Rose α) : List α := fold (fun a ls => a :: ls.flatten) t

theorem flatten_node (a : α) (cs : List (Rose α)) :
    flatten (node a cs) = a :: (cs.map flatten).flatten :=
  fold_node _ a cs

end Rose

/-! ### The coinductive rose trees, from the same structure -/

def CoRose (α : Type u) : Type u := (roseOcc α).Cotype

namespace CoRose

noncomputable def corec {S : Type u} (c : S → α × List S) (st : S) : CoRose α :=
  (roseOcc α).corec c st

noncomputable def dtor (t : CoRose α) : α × List (CoRose α) := (roseOcc α).dtor t

theorem dtor_corec {S : Type u} (c : S → α × List S) (st : S) :
    dtor (corec c st) = ((c st).1, (c st).2.map (corec c)) := by
  rw [dtor, corec, Occ.dtor_corec]
  exact roseOcc_map _ _ _

/-- Every node carries `a` and has one child, itself. -/
noncomputable def spine (a : α) : CoRose α := corec (fun _ : PUnit => (a, [PUnit.unit])) ⟨⟩

theorem dtor_spine (a : α) : dtor (spine a) = (a, [spine a]) := dtor_corec _ _

end CoRose

end Rose

/-! ## Binary trees: `leaf | node (children : BinTree × BinTree)`, the `X × X` case -/

section Bin

/-- The layer functor. -/
abbrev BinF (X : Type u) : Type u := PUnit ⊕ X × X

/-- Its occurrence structure: a sum of a constant and of a product of two holes. -/
def binOcc : Occ.{u, u, u, 0} BinF := Occ.sum (Occ.const PUnit) (Occ.prod Occ.hole Occ.hole)

def BinTree : Type u := binOcc.{u}.Intype

namespace BinTree

noncomputable def leaf : BinTree.{u} := binOcc.ctor (.inl ⟨⟩)

noncomputable def node (l r : BinTree.{u}) : BinTree.{u} := binOcc.ctor (.inr (l, r))

noncomputable def fold {S : Type u} (leaf : S) (node : S → S → S) (t : BinTree.{u}) : S :=
  binOcc.fold (fun | .inl _ => leaf | .inr (x, y) => node x y) t

theorem fold_leaf {S : Type u} (leaf : S) (node : S → S → S) : fold leaf node .leaf = leaf :=
  binOcc.fold_ctor _ _

theorem fold_node {S : Type u} (leaf : S) (node : S → S → S) (l r : BinTree.{u}) :
    fold leaf node (.node l r) = node (fold leaf node l) (fold leaf node r) :=
  binOcc.fold_ctor _ _

theorem induction {motive : BinTree.{u} → Prop} (leaf : motive leaf)
    (node : ∀ l r, motive l → motive r → motive (node l r)) (t : BinTree.{u}) : motive t :=
  binOcc.induction (motive := motive)
    (fun y ih => match y with
      | .inl _ => leaf
      | .inr (l, r) => node l r (ih (.inl ())) (ih (.inr ())))
    t

end BinTree

end Bin

end OccSketch
