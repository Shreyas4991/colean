import Colean.Model.Cotype

/-!
# Hand-written template of what `codata` generates for an indexed family

```
codata Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)
```

Kept as reference for `CodataCmd.lean`; `ColeanTest/Vec.lean` uses the command. Constructor
applications are written with all arguments explicit, as the command does.
-/

universe u

namespace IdxVec

open Codata

inductive Vec.F (α : Type u) (X : Nat → Type _) : Nat → Type _ where
  | nil : Vec.F α X 0
  | cons {n : Nat} (a : α) (v : X n) : Vec.F α X (n + 1)

def Vec.F.map {α : Type u} {X Y : Nat → Type _} (f : ∀ j, X j → Y j) {i} (a : Vec.F α X i) :
    Vec.F α Y i :=
  match a with
  | @Vec.F.nil _ _ => @Vec.F.nil α Y
  | @Vec.F.cons _ _ n a v => @Vec.F.cons α Y n a (f _ v)

@[simp] theorem Vec.F.map_cons {α : Type u} {X Y : Nat → Type _} (f : ∀ j, X j → Y j) {n : Nat}
    (a : α) (v : X n) : Vec.F.map f (@Vec.F.cons α X n a v : Vec.F α X (n + 1)) =
      @Vec.F.cons α Y n a (f _ v) := rfl

inductive Vec.F.Rel {α : Type u} {X Y : Nat → Type _} (R : ∀ j, X j → Y j → Prop) :
    ∀ {i}, Vec.F α X i → Vec.F α Y i → Prop where
  | nil : Vec.F.Rel R (@Vec.F.nil α X) (@Vec.F.nil α Y)
  | cons {n : Nat} (a : α) (v : X n) (v' : Y n) (_ : R _ v v') :
    Vec.F.Rel R (@Vec.F.cons α X n a v) (@Vec.F.cons α Y n a v')

theorem Vec.F.map_id {α : Type u} {X : Nat → Type _} {i} (a : Vec.F α X i) :
    Vec.F.map (fun _ x => x) a = a := by
  cases a
  all_goals rfl

theorem Vec.F.map_comp {α : Type u} {X Y Z : Nat → Type _} (g : ∀ j, Y j → Z j)
    (f : ∀ j, X j → Y j) {i} (a : Vec.F α X i) :
    Vec.F.map (fun j x => g j (f j x)) a = Vec.F.map g (Vec.F.map f a) := by
  cases a
  all_goals rfl

theorem Vec.F.rel_map {α : Type u} {X Y Z : Nat → Type _} (R : ∀ j, Y j → Z j → Prop)
    (f : ∀ j, X j → Y j) (g : ∀ j, X j → Z j) {i} (a : Vec.F α X i)
    (h : ∀ j x, R j (f j x) (g j x)) : Vec.F.Rel R (Vec.F.map f a) (Vec.F.map g a) := by
  cases a
  all_goals simp only [Vec.F.map]
  all_goals constructor
  all_goals apply h

inductive Vec.Shape (α : Type u) : Nat → Type _ where
  | nil : Vec.Shape α 0
  | cons {n : Nat} (a : α) : Vec.Shape α (n + 1)

/-- Positions, one per recursive argument; the index of the argument is computed by `idx`. -/
inductive Vec.B (α : Type u) : (i : Nat) → Vec.Shape α i → Type _ where
  | cons_v {n : Nat} {a : α} : Vec.B α (n + 1) (@Vec.Shape.cons α n a)

def Vec.idx {α : Type u} {i : Nat} {s : Vec.Shape α i} (b : Vec.B α i s) : Nat :=
  match b with
  | @Vec.B.cons_v _ n _ => n

abbrev Vec.sig (α : Type u) : Signature where
  I := Nat
  Shape := Vec.Shape α
  B := Vec.B α
  idx := fun b => Vec.idx b

def Vec.toC {α : Type u} {X : Nat → Type _} {i} (a : Vec.F α X i) : Signature.Obj (Vec.sig α) X i :=
  match a with
  | @Vec.F.nil _ _ => ⟨@Vec.Shape.nil α, fun b => nomatch b⟩
  | @Vec.F.cons _ _ n a v => ⟨@Vec.Shape.cons α n a, fun b => match b with | Vec.B.cons_v => v⟩

def Vec.ofC {α : Type u} {X : Nat → Type _} {i} (z : Signature.Obj (Vec.sig α) X i) :
    Vec.F α X i :=
  match i, z with
  | _, ⟨@Vec.Shape.nil _, _⟩ => @Vec.F.nil α _
  | _, ⟨@Vec.Shape.cons _ n a, ch⟩ => @Vec.F.cons α _ n a (ch Vec.B.cons_v)

theorem Vec.ofC_toC {α : Type u} {X : Nat → Type _} {i} (a : Vec.F α X i) :
    Vec.ofC (Vec.toC a) = a := by
  cases a
  all_goals rfl

theorem Vec.ofC_map {α : Type u} {X Y : Nat → Type _} (f : ∀ q, X q → Y q) {i}
    (z : Signature.Obj (Vec.sig α) X i) :
    Vec.ofC (Signature.Obj.map f z) = Vec.F.map f (Vec.ofC z) := by
  obtain ⟨s, ch⟩ := z
  cases s
  all_goals rfl

theorem Vec.rel_ofC {α : Type u} {X Y : Nat → Type _} (R : ∀ q, X q → Y q → Prop) {i}
    (z : Signature.Obj (Vec.sig α) X i) (z' : Signature.Obj (Vec.sig α) Y i)
    (h : Vec.F.Rel R (Vec.ofC z) (Vec.ofC z')) : Signature.Obj.Rel R z z' := by
  obtain ⟨s, ch⟩ := z
  obtain ⟨s', ch'⟩ := z'
  cases s
  all_goals cases s'
  all_goals try simp only [Vec.ofC] at h
  all_goals cases h
  all_goals refine ⟨_, _, _, rfl, rfl, fun b => ?_⟩
  all_goals cases b
  all_goals solve_by_elim

noncomputable section

def Vec (α : Type u) : Nat → Type u := Signature.Cotype (Vec.sig α)

def Vec.dtor {α : Type u} {i} (t : Vec α i) : Vec.F α (Vec α) i := Vec.ofC (Signature.dtorC t)

def Vec.corec {α : Type u} {S : Nat → Type _} (c : ∀ j, S j → Vec.F α S j) {i} (s : S i) :
    Vec α i :=
  Signature.corecC (fun j s => Vec.toC (c j s)) s

theorem Vec.dtor_corec {α : Type u} {S : Nat → Type _} (c : ∀ j, S j → Vec.F α S j) {i}
    (s : S i) : Vec.dtor (Vec.corec c s) = Vec.F.map (fun _ s => Vec.corec c s) (c i s) :=
  Signature.dtor_corec_of Vec.toC Vec.ofC Vec.ofC Vec.F.map Vec.ofC_toC Vec.ofC_map c s

theorem Vec.bisim {α : Type u} (R : ∀ j, Vec α j → Vec α j → Prop)
    (H : ∀ i x y, R i x y → Vec.F.Rel R (Vec.dtor x) (Vec.dtor y)) {i} {x y : Vec α i}
    (h : R i x y) : x = y :=
  Signature.bisim_of Vec.ofC Vec.F.Rel Vec.rel_ofC R H h

def Vec.contract {α : Type u} : Contract (Vec α) (Vec.F α) where
  map := Vec.F.map
  Rel := Vec.F.Rel
  map_id := Vec.F.map_id
  map_comp := Vec.F.map_comp
  rel_map := Vec.F.rel_map
  dtor := Vec.dtor
  corec := Vec.corec
  dtor_corec := Vec.dtor_corec
  bisim := Vec.bisim

def Vec.ctor {α : Type u} {i} : Vec.F α (Vec α) i → Vec α i := Contract.ctor Vec.contract

theorem Vec.dtor_ctor {α : Type u} {i} (y : Vec.F α (Vec α) i) : Vec.dtor (Vec.ctor y) = y :=
  Contract.dtor_ctor Vec.contract y

theorem Vec.ctor_dtor {α : Type u} {i} (t : Vec α i) : Vec.ctor (Vec.dtor t) = t :=
  Contract.ctor_dtor Vec.contract t

def Vec.nil {α : Type u} : Vec α 0 := Vec.ctor .nil
def Vec.cons {α : Type u} {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1) := Vec.ctor (.cons a v)

def Vec.casesOnAux {α : Type u} {motive : ∀ j, Vec α j → Sort _} {i} (y : Vec.F α (Vec α) i)
    (nil : motive 0 Vec.nil) (cons : ∀ {n : Nat} (a : α) (v : Vec α n), motive (n + 1) (Vec.cons a v)) :
    motive i (Vec.ctor y) :=
  match y with
  | .nil => nil
  | .cons a v => cons a v

@[elab_as_elim, cases_eliminator]
def Vec.casesOn {α : Type u} {motive : ∀ j, Vec α j → Sort _} {i} (t : Vec α i)
    (nil : motive 0 Vec.nil) (cons : ∀ {n : Nat} (a : α) (v : Vec α n), motive (n + 1) (Vec.cons a v)) :
    motive i t :=
  (congrArg (motive i) (Vec.ctor_dtor t)).mp (Vec.casesOnAux (Vec.dtor t) nil cons)

example {α : Type u} (v : Vec α 0) : v = Vec.nil := by
  cases v with
  | nil => rfl

end

end IdxVec
