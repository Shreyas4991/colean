import Colean.Subtypes.Codata

/-!
# Hand-written template of what `codata` generates for a family with two indices

```
codata Cyc : (n : Nat) → Fin (n + 1) → Type
  | next {n : Nat} {i : Fin (n + 1)} (c : Cyc n (i + 1)) : Cyc n i
  | prev {n : Nat} {i : Fin (n + 1)} (c : Cyc n (i - 1)) : Cyc n i
```

The user-facing declarations are curried; the generic layer is instantiated at the packed index
`Cyc.Ix := (n : Nat) ×' Fin (n + 1)`. The internal isomorphism `toC`/`ofC` keeps the index
binders curried (so that constructor patterns can bind their arguments) and takes the family on
the packed index; the instantiations of the generic theorems convert with lambdas. Since the
constructors' data `n i` are the indices themselves, they are holes in patterns and the index
binders are used on the right-hand sides.
-/

namespace IdxCyc

open Codata

inductive Cyc.F (X : ∀ (n : Nat), Fin (n + 1) → Type _) : ∀ (n : Nat), Fin (n + 1) → Type _ where
  | next {n : Nat} {i : Fin (n + 1)} (c : X n (i + 1)) : Cyc.F X n i
  | prev {n : Nat} {i : Fin (n + 1)} (c : X n (i - 1)) : Cyc.F X n i

def Cyc.F.map {X Y : ∀ (n : Nat), Fin (n + 1) → Type _} (f : ∀ j₁ j₂, X j₁ j₂ → Y j₁ j₂)
    {n : Nat} {i₂ : Fin (n + 1)} (a : Cyc.F X n i₂) : Cyc.F Y n i₂ :=
  match a with
  | @Cyc.F.next _ _ _ c => @Cyc.F.next Y n i₂ (f _ _ c)
  | @Cyc.F.prev _ _ _ c => @Cyc.F.prev Y n i₂ (f _ _ c)

inductive Cyc.F.Rel {X Y : ∀ (n : Nat), Fin (n + 1) → Type _} (R : ∀ j₁ j₂, X j₁ j₂ → Y j₁ j₂ → Prop) :
    ∀ {n : Nat} {i₂ : Fin (n + 1)}, Cyc.F X n i₂ → Cyc.F Y n i₂ → Prop where
  | next {n : Nat} {i : Fin (n + 1)} (c : X n (i + 1)) (c' : Y n (i + 1)) (_ : R _ _ c c') :
    Cyc.F.Rel R (@Cyc.F.next X n i c) (@Cyc.F.next Y n i c')
  | prev {n : Nat} {i : Fin (n + 1)} (c : X n (i - 1)) (c' : Y n (i - 1)) (_ : R _ _ c c') :
    Cyc.F.Rel R (@Cyc.F.prev X n i c) (@Cyc.F.prev Y n i c')

theorem Cyc.F.map_id {X : ∀ (n : Nat), Fin (n + 1) → Type _} {n : Nat} {i₂ : Fin (n + 1)}
    (a : Cyc.F X n i₂) : Cyc.F.map (fun _ _ x => x) a = a := by
  cases a
  all_goals rfl

theorem Cyc.F.map_comp {X Y Z : ∀ (n : Nat), Fin (n + 1) → Type _}
    (g : ∀ j₁ j₂, Y j₁ j₂ → Z j₁ j₂) (f : ∀ j₁ j₂, X j₁ j₂ → Y j₁ j₂) {n : Nat} {i₂ : Fin (n + 1)}
    (a : Cyc.F X n i₂) :
    Cyc.F.map (fun j₁ j₂ x => g j₁ j₂ (f j₁ j₂ x)) a = Cyc.F.map g (Cyc.F.map f a) := by
  cases a
  all_goals rfl

theorem Cyc.F.rel_map {X Y Z : ∀ (n : Nat), Fin (n + 1) → Type _}
    (R : ∀ j₁ j₂, Y j₁ j₂ → Z j₁ j₂ → Prop) (f : ∀ j₁ j₂, X j₁ j₂ → Y j₁ j₂)
    (g : ∀ j₁ j₂, X j₁ j₂ → Z j₁ j₂) {n : Nat} {i₂ : Fin (n + 1)} (a : Cyc.F X n i₂)
    (h : ∀ j₁ j₂ x, R j₁ j₂ (f j₁ j₂ x) (g j₁ j₂ x)) :
    Cyc.F.Rel R (Cyc.F.map f a) (Cyc.F.map g a) := by
  cases a
  all_goals simp only [Cyc.F.map]
  all_goals constructor
  all_goals apply h

inductive Cyc.Shape : ∀ (n : Nat), Fin (n + 1) → Type _ where
  | next {n : Nat} {i : Fin (n + 1)} : Cyc.Shape n i
  | prev {n : Nat} {i : Fin (n + 1)} : Cyc.Shape n i

inductive Cyc.B : ∀ (n : Nat) (i₂ : Fin (n + 1)), Cyc.Shape n i₂ → Type _ where
  | next_c {n : Nat} {i : Fin (n + 1)} : Cyc.B n i (@Cyc.Shape.next n i)
  | prev_c {n : Nat} {i : Fin (n + 1)} : Cyc.B n i (@Cyc.Shape.prev n i)

/-- The packed index. -/
abbrev Cyc.Ix : Type := PSigma fun (n : Nat) => Fin (n + 1)

def Cyc.idx {n : Nat} {i₂ : Fin (n + 1)} {s : Cyc.Shape n i₂} (b : Cyc.B n i₂ s) : Cyc.Ix :=
  match b with
  | @Cyc.B.next_c _ _ => ⟨n, i₂ + 1⟩
  | @Cyc.B.prev_c _ _ => ⟨n, i₂ - 1⟩

abbrev Cyc.sig : Signature where
  I := Cyc.Ix
  Shape := fun p => match p with | ⟨n, i₂⟩ => Cyc.Shape n i₂
  B := fun p s => match p, s with | ⟨n, i₂⟩, s => Cyc.B n i₂ s
  idx := fun {p} {s} b => match p, s, b with | ⟨_, _⟩, _, b => Cyc.idx b

def Cyc.toC {X : Cyc.Ix → Type _} {n : Nat} {i₂ : Fin (n + 1)}
    (a : Cyc.F (fun j₁ j₂ => X ⟨j₁, j₂⟩) n i₂) : Signature.Obj Cyc.sig X ⟨n, i₂⟩ :=
  match a with
  | @Cyc.F.next _ _ _ c => ⟨@Cyc.Shape.next n i₂, fun b => match b with | Cyc.B.next_c => c⟩
  | @Cyc.F.prev _ _ _ c => ⟨@Cyc.Shape.prev n i₂, fun b => match b with | Cyc.B.prev_c => c⟩

def Cyc.ofC {X : Cyc.Ix → Type _} {n : Nat} {i₂ : Fin (n + 1)} (z : Signature.Obj Cyc.sig X ⟨n, i₂⟩) :
    Cyc.F (fun j₁ j₂ => X ⟨j₁, j₂⟩) n i₂ :=
  match n, i₂, z with
  | n, i₂, ⟨@Cyc.Shape.next _ _, ch⟩ => @Cyc.F.next _ n i₂ (ch Cyc.B.next_c)
  | n, i₂, ⟨@Cyc.Shape.prev _ _, ch⟩ => @Cyc.F.prev _ n i₂ (ch Cyc.B.prev_c)

theorem Cyc.ofC_toC {X : Cyc.Ix → Type _} {n : Nat} {i₂ : Fin (n + 1)}
    (a : Cyc.F (fun j₁ j₂ => X ⟨j₁, j₂⟩) n i₂) : Cyc.ofC (Cyc.toC a) = a := by
  cases a
  all_goals rfl

theorem Cyc.ofC_map {X Y : Cyc.Ix → Type _} (f : ∀ q, X q → Y q) {n : Nat} {i₂ : Fin (n + 1)}
    (z : Signature.Obj Cyc.sig X ⟨n, i₂⟩) :
    Cyc.ofC (Signature.Obj.map f z) = Cyc.F.map (fun j₁ j₂ x => f ⟨j₁, j₂⟩ x) (Cyc.ofC z) := by
  obtain ⟨s, ch⟩ := z
  cases s
  all_goals rfl

theorem Cyc.rel_ofC {X Y : Cyc.Ix → Type _} (R : ∀ q, X q → Y q → Prop) {n : Nat}
    {i₂ : Fin (n + 1)} (z : Signature.Obj Cyc.sig X ⟨n, i₂⟩) (z' : Signature.Obj Cyc.sig Y ⟨n, i₂⟩)
    (h : Cyc.F.Rel (fun j₁ j₂ => R ⟨j₁, j₂⟩) (Cyc.ofC z) (Cyc.ofC z')) : Signature.Obj.Rel R z z' := by
  obtain ⟨s, ch⟩ := z
  obtain ⟨s', ch'⟩ := z'
  cases s
  all_goals cases s'
  all_goals try simp only [Cyc.ofC] at h
  all_goals cases h
  all_goals refine ⟨_, _, _, rfl, rfl, fun b => ?_⟩
  all_goals cases b
  all_goals solve_by_elim

noncomputable section

def Cyc : ∀ (n : Nat), Fin (n + 1) → Type := fun n i₂ => Signature.Cotype Cyc.sig ⟨n, i₂⟩

def Cyc.dtor {n : Nat} {i₂ : Fin (n + 1)} (t : Cyc n i₂) : Cyc.F Cyc n i₂ :=
  @Cyc.ofC (Signature.Cotype Cyc.sig) n i₂ (Signature.dtorC t)

def Cyc.corec {S : ∀ (n : Nat), Fin (n + 1) → Type _} (c : ∀ j₁ j₂, S j₁ j₂ → Cyc.F S j₁ j₂)
    {n : Nat} {i₂ : Fin (n + 1)} (s : S n i₂) : Cyc n i₂ :=
  Signature.corecC (σ := Cyc.sig) (S := fun (p : Cyc.Ix) => S p.1 p.2)
    (fun (p : Cyc.Ix) s => @Cyc.toC (fun (p : Cyc.Ix) => S p.1 p.2) p.1 p.2 (c p.1 p.2 s)) s

theorem Cyc.dtor_corec {S : ∀ (n : Nat), Fin (n + 1) → Type _} (c : ∀ j₁ j₂, S j₁ j₂ → Cyc.F S j₁ j₂)
    {n : Nat} {i₂ : Fin (n + 1)} (s : S n i₂) :
    Cyc.dtor (Cyc.corec c s) = Cyc.F.map (fun _ _ s => Cyc.corec c s) (c n i₂ s) :=
  Signature.dtor_corec_of (σ := Cyc.sig) (S := fun (p : Cyc.Ix) => S p.1 p.2)
    (FS := fun (p : Cyc.Ix) => Cyc.F S p.1 p.2) (FT := fun (p : Cyc.Ix) => Cyc.F Cyc p.1 p.2)
    (i := (⟨n, i₂⟩ : Cyc.Ix))
    (fun {p} a => @Cyc.toC (fun (p : Cyc.Ix) => S p.1 p.2) p.1 p.2 a)
    (fun {p} z => @Cyc.ofC (fun (p : Cyc.Ix) => S p.1 p.2) p.1 p.2 z)
    (fun {p} z => @Cyc.ofC (Signature.Cotype Cyc.sig) p.1 p.2 z)
    (fun f {_} a => Cyc.F.map (fun j₁ j₂ x => f ⟨j₁, j₂⟩ x) a)
    (fun {p} a => @Cyc.ofC_toC (fun (p : Cyc.Ix) => S p.1 p.2) p.1 p.2 a)
    (fun f {p} z => @Cyc.ofC_map (fun (p : Cyc.Ix) => S p.1 p.2) (Signature.Cotype Cyc.sig) f p.1 p.2 z)
    (fun (p : Cyc.Ix) s => c p.1 p.2 s) s

theorem Cyc.bisim (R : ∀ j₁ j₂, Cyc j₁ j₂ → Cyc j₁ j₂ → Prop)
    (H : ∀ n i₂ x y, R n i₂ x y → Cyc.F.Rel R (Cyc.dtor x) (Cyc.dtor y)) {n : Nat} {i₂ : Fin (n + 1)}
    {x y : Cyc n i₂} (h : R n i₂ x y) : x = y :=
  Signature.bisim_of (σ := Cyc.sig) (FT := fun (p : Cyc.Ix) => Cyc.F Cyc p.1 p.2) (i := (⟨n, i₂⟩ : Cyc.Ix))
    (fun {p} z => @Cyc.ofC (Signature.Cotype Cyc.sig) p.1 p.2 z)
    (fun R {_} a b => Cyc.F.Rel (fun j₁ j₂ => R ⟨j₁, j₂⟩) a b)
    (fun R {p} z z' h => @Cyc.rel_ofC (Signature.Cotype Cyc.sig) (Signature.Cotype Cyc.sig) R p.1 p.2 z z' h)
    (fun (p : Cyc.Ix) => R p.1 p.2) (fun (p : Cyc.Ix) x y h => H p.1 p.2 x y h) h

def Cyc.contract : Contract (I := Cyc.Ix) (fun p => Cyc p.1 p.2)
    (fun (X : Cyc.Ix → Type _) p => Cyc.F (fun j₁ j₂ => X ⟨j₁, j₂⟩) p.1 p.2) where
  map := fun {_ _} f {_} a => Cyc.F.map (fun j₁ j₂ x => f ⟨j₁, j₂⟩ x) a
  Rel := fun {_ _} R {_} a b => Cyc.F.Rel (fun j₁ j₂ => R ⟨j₁, j₂⟩) a b
  map_id := fun {_ _} a => Cyc.F.map_id a
  map_comp := fun {_ _ _} g f {_} a =>
    Cyc.F.map_comp (fun j₁ j₂ => g ⟨j₁, j₂⟩) (fun j₁ j₂ => f ⟨j₁, j₂⟩) a
  rel_map := fun {_ _ _} R f g {_} a h => Cyc.F.rel_map (fun j₁ j₂ => R ⟨j₁, j₂⟩)
    (fun j₁ j₂ => f ⟨j₁, j₂⟩) (fun j₁ j₂ => g ⟨j₁, j₂⟩) a (fun j₁ j₂ x => h ⟨j₁, j₂⟩ x)
  dtor := fun {_} t => Cyc.dtor t
  corec := fun {_} c {_} s => Cyc.corec (fun j₁ j₂ s => c ⟨j₁, j₂⟩ s) s
  dtor_corec := fun {_} c {_} s => Cyc.dtor_corec (fun j₁ j₂ s => c ⟨j₁, j₂⟩ s) s
  bisim := fun R H {_ _ _} h =>
    Cyc.bisim (fun j₁ j₂ => R ⟨j₁, j₂⟩) (fun i₁ i₂ x y h => H ⟨i₁, i₂⟩ x y h) h

def Cyc.ctor {n : Nat} {i₂ : Fin (n + 1)} : Cyc.F Cyc n i₂ → Cyc n i₂ :=
  Contract.ctor Cyc.contract (i := (⟨n, i₂⟩ : Cyc.Ix))

theorem Cyc.dtor_ctor {n : Nat} {i₂ : Fin (n + 1)} (y : Cyc.F Cyc n i₂) : Cyc.dtor (Cyc.ctor y) = y :=
  Contract.dtor_ctor Cyc.contract (i := (⟨n, i₂⟩ : Cyc.Ix)) y

theorem Cyc.ctor_dtor {n : Nat} {i₂ : Fin (n + 1)} (t : Cyc n i₂) : Cyc.ctor (Cyc.dtor t) = t :=
  Contract.ctor_dtor Cyc.contract (i := (⟨n, i₂⟩ : Cyc.Ix)) t

def Cyc.next {n : Nat} {i : Fin (n + 1)} (c : Cyc n (i + 1)) : Cyc n i := Cyc.ctor (@Cyc.F.next Cyc n i c)
def Cyc.prev {n : Nat} {i : Fin (n + 1)} (c : Cyc n (i - 1)) : Cyc n i := Cyc.ctor (@Cyc.F.prev Cyc n i c)

def Cyc.casesOnAux {motive : ∀ j₁ j₂, Cyc j₁ j₂ → Sort _} {n : Nat} {i₂ : Fin (n + 1)}
    (y : Cyc.F Cyc n i₂) (next : ∀ {n : Nat} {i : Fin (n + 1)} (c : Cyc n (i + 1)), motive n i (Cyc.next c))
    (prev : ∀ {n : Nat} {i : Fin (n + 1)} (c : Cyc n (i - 1)), motive n i (Cyc.prev c)) :
    motive n i₂ (Cyc.ctor y) :=
  match y with
  | @Cyc.F.next _ _ _ c => next c
  | @Cyc.F.prev _ _ _ c => prev c

@[elab_as_elim, cases_eliminator]
def Cyc.casesOn {motive : ∀ j₁ j₂, Cyc j₁ j₂ → Sort _} {n : Nat} {i₂ : Fin (n + 1)} (t : Cyc n i₂)
    (next : ∀ {n : Nat} {i : Fin (n + 1)} (c : Cyc n (i + 1)), motive n i (Cyc.next c))
    (prev : ∀ {n : Nat} {i : Fin (n + 1)} (c : Cyc n (i - 1)), motive n i (Cyc.prev c)) :
    motive n i₂ t :=
  (congrArg (motive n i₂) (Cyc.ctor_dtor t)).mp (Cyc.casesOnAux (Cyc.dtor t) next prev)

example {n : Nat} {i : Fin (n + 1)} (t : Cyc n i) : True := by
  cases t with
  | next c => trivial
  | prev c => trivial

end

end IdxCyc
