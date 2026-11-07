import Colean.Model.Intype
import Colean.PolyIso

/-!
# The model: a fixpoint is polynomial in its parameter

If a layer is polynomial in the parameter `X` and in the recursive variable `Y`,
`Lay P B X Y = Σ s, (P s → X) × (B s → Y)`, then its least and greatest fixpoints in `Y` are
polynomial in `X`: a value is a *tree of shapes* and the contents of its slots, a slot being a
finite path to a node with a position `P s` there (`Path`). Both fixpoints go through one proof:
`data` and `codata` both have a destructor and a bisimulation principle, and differ only in how
`erase` (a value to its tree of shapes) and `fill` (a tree of shapes with contents to a value)
are obtained (`coFill` by corecursion, `inFill` by a fold and well-founded recursion).

This is the construction of `MvPFunctor.wp` and `MvPFunctor.M.Path`, on any type satisfying the
hypotheses, so that it applies to the types of the commands through their contracts.
-/

universe s p b x x' y y' w t t' st

namespace Codata

variable {S : Type s}

/-- Transport along an equality of shapes. -/
abbrev castS {D : S → Sort y} {s₁ s₂ : S} (e : s₁ = s₂) (d : D s₁) : D s₂ := e ▸ d

theorem castS_castS {D : S → Sort y} {s₁ s₂ s₃ : S} (e : s₁ = s₂) (e' : s₂ = s₃) (d : D s₁) :
    castS (D := D) e' (castS e d) = castS (e.trans e') d := by
  subst e; subst e'; rfl

theorem castS_self {D : S → Sort y} {s₁ : S} (e : s₁ = s₁) (d : D s₁) : castS e d = d := rfl

variable (P : S → Type p) (B : S → Type b)

/-- A layer, polynomial in the parameter `X` and in the recursive variable `Y`. -/
abbrev Lay (X : Type x) (Y : Type y) : Type (max s p b x y) := Σ s : S, (P s → X) × (B s → Y)

variable {P B}

/-- The action on the recursive variable. -/
def Lay.map {X : Type x} {Y : Type y} {Y' : Type y'} (f : Y → Y') (z : Lay P B X Y) :
    Lay P B X Y' :=
  ⟨z.1, z.2.1, fun b => f (z.2.2 b)⟩

variable (B) in
/-- A tree of shapes: a type with a destructor and the bisimulation principle. -/
structure ShapeTree (W : Type w) where
  d : W → Σ s : S, (B s → W)
  bisim (R : W → W → Prop)
    (H : ∀ a c, R a c → ∃ e : (d a).1 = (d c).1, ∀ i, R ((d a).2 i) ((d c).2 (castS e i)))
    (a c : W) : R a c → a = c

variable (P) in
/-- A slot of a tree of shapes: a finite path to a node, and a parameter position there. -/
inductive Path {W : Type w} (𝕎 : ShapeTree B W) : W → Type (max p b w)
  | here {a : W} (q : P (𝕎.d a).1) : Path 𝕎 a
  | there {a : W} (i : B (𝕎.d a).1) (r : Path 𝕎 ((𝕎.d a).2 i)) : Path 𝕎 a

variable (P) in
/-- A fixpoint of the layer at `X`, with its tree of shapes: a destructor and the bisimulation
principle, `erase` to the tree of shapes, and `fill` back. -/
structure PolyFix {W : Type w} (𝕎 : ShapeTree B W) (X : Type x) (T : Type t) where
  d : T → Lay P B X T
  bisim (R : T → T → Prop)
    (H : ∀ a c, R a c → ∃ e : (d a).1 = (d c).1,
      (∀ q, (d a).2.1 q = (d c).2.1 (castS e q)) ∧ ∀ i, R ((d a).2.2 i) ((d c).2.2 (castS e i)))
    (a c : T) : R a c → a = c
  erase : T → W
  d_erase (a : T) : 𝕎.d (erase a) = ⟨(d a).1, fun i => erase ((d a).2.2 i)⟩
  fill (a : W) : (Path P 𝕎 a → X) → T
  d_fill (a : W) (c : Path P 𝕎 a → X) :
    d (fill a c) = ⟨(𝕎.d a).1, fun q => c (.here q), fun i => fill _ fun r => c (.there i r)⟩

namespace PolyFix

variable {W : Type w} {𝕎 : ShapeTree B W} {X : Type x} {T : Type t} (M : PolyFix P 𝕎 X T)

theorem erase_fst {a : T} {c : W} (h : M.erase a = c) : (M.d a).1 = (𝕎.d c).1 := by
  subst h
  rw [M.d_erase]

theorem erase_child {a : T} {c : W} (h : M.erase a = c) (i : B (𝕎.d c).1) :
    M.erase ((M.d a).2.2 (castS (M.erase_fst h).symm i)) = (𝕎.d c).2 i := by
  subst h
  have key : ∀ z : Σ s : S, (B s → W),
      (e : z = ⟨(M.d a).1, fun i => M.erase ((M.d a).2.2 i)⟩) → ∀ i : B z.1,
      M.erase ((M.d a).2.2 (castS (D := B) (congrArg (·.1) e) i)) = z.2 i := by
    rintro _ rfl i
    rfl
  exact key _ (M.d_erase a) i

/-- The content of a slot, for a value whose tree of shapes is the slot's. -/
def val : {c : W} → Path P 𝕎 c → (a : T) → M.erase a = c → X
  | _, .here q, a, h => (M.d a).2.1 (castS (M.erase_fst h).symm q)
  | _, .there i r, a, h => val r ((M.d a).2.2 (castS (M.erase_fst h).symm i)) (M.erase_child h i)

theorem fill_fst (c : W) (f : Path P 𝕎 c → X) : (M.d (M.fill c f)).1 = (𝕎.d c).1 :=
  congrArg Sigma.fst (M.d_fill c f)

theorem fill_val (c : W) (f : Path P 𝕎 c → X) (q : P (𝕎.d c).1) :
    (M.d (M.fill c f)).2.1 (castS (M.fill_fst c f).symm q) = f (.here q) := by
  have key : ∀ z : Lay P B X T,
      (e : z = ⟨(𝕎.d c).1, fun q => f (.here q), fun i => M.fill _ fun r => f (.there i r)⟩) →
      ∀ q : P (𝕎.d c).1, z.2.1 (castS (congrArg Sigma.fst e).symm q) = f (.here q) := by
    rintro _ rfl q
    rfl
  exact key _ (M.d_fill c f) q

theorem fill_kid (c : W) (f : Path P 𝕎 c → X) (i : B (𝕎.d c).1) :
    (M.d (M.fill c f)).2.2 (castS (M.fill_fst c f).symm i) =
      M.fill _ fun r => f (.there i r) := by
  have key : ∀ z : Lay P B X T,
      (e : z = ⟨(𝕎.d c).1, fun q => f (.here q), fun i => M.fill _ fun r => f (.there i r)⟩) →
      ∀ i : B (𝕎.d c).1, z.2.2 (castS (congrArg Sigma.fst e).symm i) =
        M.fill _ fun r => f (.there i r) := by
    rintro _ rfl i
    rfl
  exact key _ (M.d_fill c f) i

/-- `erase` undoes `fill`. -/
theorem erase_fill (c : W) (f : Path P 𝕎 c → X) : M.erase (M.fill c f) = c := by
  refine 𝕎.bisim (fun a c => ∃ f, a = M.erase (M.fill c f)) ?_ _ _ ⟨f, rfl⟩
  rintro _ c ⟨f, rfl⟩
  have e₀ := M.erase_fst (a := M.fill c f) rfl
  refine ⟨e₀.symm.trans (M.fill_fst c f), fun i => ?_⟩
  refine ⟨fun r => f (.there (castS (e₀.symm.trans (M.fill_fst c f)) i) r), ?_⟩
  rw [← M.erase_child (a := M.fill c f) rfl i, ← M.fill_kid]
  exact congrArg (fun i' => M.erase ((M.d (M.fill c f)).2.2 i'))
    (by rw [castS_castS])

/-- The contents of a filled tree are the given ones. -/
theorem val_fill {c : W} (r : Path P 𝕎 c) :
    ∀ (a : T) (h : M.erase a = c) (f : Path P 𝕎 c → X), a = M.fill c f → M.val r a h = f r := by
  induction r with
  | here q =>
    rintro _ h f rfl
    exact M.fill_val _ f q
  | there i r ih =>
    rintro _ h f rfl
    exact ih _ _ (fun r => f (.there i r)) (M.fill_kid _ f i)

/-- `fill` undoes `erase`. -/
theorem fill_val_eq {c : W} (a : T) (h : M.erase a = c) : M.fill c (fun r => M.val r a h) = a := by
  refine M.bisim (fun x y => ∃ (c : W) (h : M.erase y = c), x = M.fill c fun r => M.val r y h)
    ?_ _ _ ⟨c, h, rfl⟩
  rintro _ y ⟨c, h, rfl⟩
  have e₁ := M.fill_fst c fun r => M.val r y h
  have e₂ := M.erase_fst h
  refine ⟨e₁.trans e₂.symm, fun q => ?_, fun i => ?_⟩
  · have := M.fill_val c (fun r => M.val r y h) (castS e₁ q)
    rw [castS_castS] at this
    refine this.trans ?_
    show (M.d y).2.1 _ = _
    rw [castS_castS]
  · have := M.fill_kid c (fun r => M.val r y h) (castS e₁ i)
    rw [castS_castS] at this
    have hy : (M.d y).2.2 (castS (e₁.trans e₂.symm) i) =
        (M.d y).2.2 (castS e₂.symm (castS e₁ i)) := by rw [castS_castS]
    rw [hy]
    exact ⟨_, M.erase_child h (castS e₁ i), this⟩

/-- A value is a tree of shapes with the contents of its slots. -/
def equiv : T ≃ Poly W (Path P 𝕎) X where
  toFun a := ⟨M.erase a, fun r => M.val r a rfl⟩
  invFun z := M.fill z.1 z.2
  left_inv a := M.fill_val_eq a rfl
  right_inv := by
    rintro ⟨c, f⟩
    have key : ∀ (c' : W) (h : M.erase (M.fill c f) = c'),
        (⟨M.erase (M.fill c f), fun r => M.val r (M.fill c f) rfl⟩ : Poly W (Path P 𝕎) X) =
          ⟨c', fun r => M.val r (M.fill c f) h⟩ := by
      rintro _ rfl
      rfl
    exact (key c (M.erase_fill c f)).trans
      (congrArg (Sigma.mk c) (funext fun r => M.val_fill r _ _ f rfl))

/-- The action on the parameter: the same tree of shapes, the contents mapped. -/
def map {X' : Type x'} {T' : Type t'} (M' : PolyFix P 𝕎 X' T') (f : X → X') (a : T) : T' :=
  M'.equiv.symm (Poly.map f (M.equiv a))

theorem equiv_map {X' : Type x'} {T' : Type t'} (M' : PolyFix P 𝕎 X' T') (f : X → X') (a : T) :
    M'.equiv (M.map M' f a) = Poly.map f (M.equiv a) :=
  M'.equiv.apply_symm_apply _

theorem map_eq {X' : Type x'} {T' : Type t'} (M' : PolyFix P 𝕎 X' T') (f : X → X') {a : T} {c : W}
    (h : M.erase a = c) : M.map M' f a = M'.fill c fun r => f (M.val r a h) := by
  subst h
  rfl

/-- The action on the parameter is the structural one: it maps the contents of the layer and goes
on in the children. So the map of `PolyMap` is determined by the type, not by the presentation. -/
theorem d_map {X' : Type x'} {T' : Type t'} (M' : PolyFix P 𝕎 X' T') (f : X → X') (a : T) :
    M'.d (M.map M' f a) =
      ⟨(M.d a).1, fun q => f ((M.d a).2.1 q), fun i => M.map M' f ((M.d a).2.2 i)⟩ := by
  have key : ∀ (c : W) (h : M.erase a = c), M'.d (M'.fill c fun r => f (M.val r a h)) =
      ⟨(M.d a).1, fun q => f ((M.d a).2.1 q), fun i => M.map M' f ((M.d a).2.2 i)⟩ := by
    intro c h
    rw [M'.d_fill]
    have e := M.erase_fst h
    have ext : ∀ {s₁ s₂ : S} (e : s₂ = s₁) {v₁ : P s₁ → X'} {k₁ : B s₁ → T'} {v₂ : P s₂ → X'}
        {k₂ : B s₂ → T'}, (∀ q, v₁ q = v₂ (castS e.symm q)) →
        (∀ i, k₁ i = k₂ (castS e.symm i)) →
        (⟨s₁, v₁, k₁⟩ : Lay P B X' T') = ⟨s₂, v₂, k₂⟩ := by
      intro s₁ s₂ e v₁ k₁ v₂ k₂ hv hk
      subst e
      obtain rfl : v₁ = v₂ := funext hv
      obtain rfl : k₁ = k₂ := funext hk
      rfl
    exact ext e (fun _ => rfl)
      (fun i => (M.map_eq M' f (M.erase_child h i)).symm)
  exact key _ rfl

end PolyFix

/-! ### Trees of shapes -/

variable (B) in
/-- The signature of the trees of shapes: one index, no parameter. -/
abbrev shapeSig : Signature.{0, s, b} where
  I := Unit
  Shape := fun _ => S
  B := fun _ s => B s
  idx := fun _ => ()

theorem obj_rel_of {R : ∀ j : Unit, (shapeSig B).Cotype j → (shapeSig B).Cotype j → Prop}
    (z z' : (shapeSig B).Obj (shapeSig B).Cotype ()) (e : z.shape = z'.shape)
    (h : ∀ i, R () (z.child i) (z'.child (castS (D := B) e i))) :
    Signature.Obj.Rel R z z' := by
  obtain ⟨s, c⟩ := z
  obtain ⟨s', c'⟩ := z'
  cases (e : s = s')
  exact ⟨s, c, c', rfl, rfl, h⟩

variable (B) in
/-- The coinductive trees of shapes. -/
noncomputable def coTree : ShapeTree B ((shapeSig B).Cotype ()) where
  d a := ⟨(Signature.dtorC a).shape, (Signature.dtorC a).child⟩
  bisim R H a c h := by
    refine Signature.bisimC (σ := shapeSig B) (fun _ => R) (fun j x y hxy => ?_) h
    obtain ⟨e, hk⟩ := H x y hxy
    exact obj_rel_of (R := fun _ => R) _ _ e hk

variable (B) in
/-- The inductive trees of shapes. -/
noncomputable def inTree : ShapeTree B ((shapeSig B).Intype ()) where
  d a := ⟨(Signature.dtorI a).shape, (Signature.dtorI a).child⟩
  bisim R H a c h := by
    have key : ∀ a : (shapeSig B).Intype (), ∀ c, R a c → a = c := by
      intro a
      refine Signature.recI (σ := shapeSig B) (motive := fun _ a => ∀ c, R a c → a = c) ?_ a
      rintro ⟨⟩ z ih c hc
      obtain ⟨e, hk⟩ := H _ c hc
      have hz := Signature.dtorI_ctorI z
      rw [← Signature.ctorI_dtorI c]
      generalize Signature.dtorI (Signature.ctorI z) = z' at e hk hz
      subst hz
      generalize Signature.dtorI c = zc at e hk
      obtain ⟨s, k⟩ := z'
      obtain ⟨s', k'⟩ := zc
      cases (e : s = s')
      exact congrArg (fun k => Signature.ctorI (Signature.Obj.mk s k))
        (funext fun i => ih i _ (hk i))
    exact key a c h

theorem coTree_d_of {a : (shapeSig B).Cotype ()} {z : (shapeSig B).Obj (shapeSig B).Cotype ()}
    (h : Signature.dtorC a = z) : (coTree B).d a = ⟨z.shape, z.child⟩ := by
  subst h
  rfl

theorem inTree_d_of {a : (shapeSig B).Intype ()} {z : (shapeSig B).Obj (shapeSig B).Intype ()}
    (h : Signature.dtorI a = z) : (inTree B).d a = ⟨z.shape, z.child⟩ := by
  subst h
  rfl

/-! ### The two instances -/

section Co

variable {X : Type x} {T : Type t}

/-- A coinductive fixpoint of the layer. -/
noncomputable def coFix (d : T → Lay P B X T)
    (corec : ∀ {St : Type (max s b p x)}, (St → Lay P B X St) → St → T)
    (d_corec : ∀ {St : Type (max s b p x)} (c : St → Lay P B X St) (a : St),
      d (corec c a) = Lay.map (corec c) (c a))
    (bisim : ∀ (R : T → T → Prop),
      (∀ a c, R a c → ∃ e : (d a).1 = (d c).1, (∀ q, (d a).2.1 q = (d c).2.1 (castS e q)) ∧
        ∀ i, R ((d a).2.2 i) ((d c).2.2 (castS e i))) → ∀ a c, R a c → a = c) :
    PolyFix P (coTree B) X T where
  d := d
  bisim := bisim
  erase := Signature.corecC (σ := shapeSig B) (S := fun _ => T)
    (fun _ a => ⟨(d a).1, (d a).2.2⟩)
  d_erase a := coTree_d_of (Signature.dtorC_corecC (σ := shapeSig B) (S := fun _ => T) _ a)
  fill a c := corec (St := Σ a, Path P (coTree B) a → X)
    (fun z => ⟨((coTree B).d z.1).1, fun q => z.2 (.here q), fun i => ⟨_, fun r => z.2 (.there i r)⟩⟩)
    ⟨a, c⟩
  d_fill a c := d_corec _ _

/-- The bisimulation principle of a layer destructor, from a contract. -/
theorem co_bisim {F : Type t → Type t} (K : Contract (fun _ : Unit => T) (fun Y _ => F (Y ())))
    (d : T → Lay P B X T) (ofL : ∀ {Y : Type t}, Lay P B X Y → F Y)
    (ofL_d : ∀ a, ofL (d a) = K.dtor (i := ()) a)
    (ofL_map : ∀ {Y Y' : Type t} (f : Y → Y') (z : Lay P B X Y),
      ofL (Lay.map f z) = K.map (X := fun _ => Y) (Y := fun _ => Y') (fun _ => f) (i := ()) (ofL z))
    (R : T → T → Prop)
    (H : ∀ a c, R a c → ∃ e : (d a).1 = (d c).1, (∀ q, (d a).2.1 q = (d c).2.1 (castS e q)) ∧
      ∀ i, R ((d a).2.2 i) ((d c).2.2 (castS e i)))
    (a c : T) (h : R a c) : a = c := by
  refine K.bisim (fun _ => R) (fun _ x y hxy => ?_) (i := ()) h
  obtain ⟨e, hv, hk⟩ := H x y hxy
  rw [← ofL_d x, ← ofL_d y]
  generalize d x = zx at e hv hk
  generalize d y = zy at e hv hk
  obtain ⟨sx, vx, kx⟩ := zx
  obtain ⟨sy, vy, ky⟩ := zy
  cases (e : sx = sy)
  obtain rfl : vx = vy := funext hv
  refine ⟨ofL (Y := {p : T × T // R p.1 p.2}) ⟨sx, vx, fun i => ⟨(kx i, ky i), hk i⟩⟩, ?_, ?_⟩
  · exact (ofL_map (fun p : {p : T × T // R p.1 p.2} => p.1.1) _).symm
  · exact (ofL_map (fun p : {p : T × T // R p.1 p.2} => p.1.2) _).symm

end Co

section In

variable {X : Type x} {T : Type t}

/-- The bisimulation principle of an inductive fixpoint. -/
theorem in_bisim (ctor : Lay P B X T → T) (d : T → Lay P B X T)
    (d_ctor : ∀ z, d (ctor z) = z) (ctor_d : ∀ a, ctor (d a) = a)
    (ind : ∀ motive : T → Prop, (∀ z, (∀ i, motive (z.2.2 i)) → motive (ctor z)) → ∀ a, motive a)
    (R : T → T → Prop)
    (H : ∀ a c, R a c → ∃ e : (d a).1 = (d c).1, (∀ q, (d a).2.1 q = (d c).2.1 (castS e q)) ∧
      ∀ i, R ((d a).2.2 i) ((d c).2.2 (castS e i)))
    (a c : T) (h : R a c) : a = c := by
  have key : ∀ a c, R a c → a = c := by
    refine fun a => ind (fun a => ∀ c, R a c → a = c) ?_ a
    intro z ih c hc
    obtain ⟨e, hv, hk⟩ := H _ c hc
    have hz := d_ctor z
    rw [← ctor_d c]
    generalize d (ctor z) = z' at e hv hk hz
    subst hz
    generalize d c = zc at e hv hk
    obtain ⟨s, v, k⟩ := z'
    obtain ⟨s', v', k'⟩ := zc
    cases (e : s = s')
    obtain rfl : v = v' := funext hv
    exact congrArg (fun k => ctor ⟨s, v, k⟩) (funext fun i => ih i _ (hk i))
  exact key a c h

/-- An inductive fixpoint of the layer. -/
noncomputable def inFix (ctor : Lay P B X T → T) (d : T → Lay P B X T)
    (d_ctor : ∀ z, d (ctor z) = z) (ctor_d : ∀ a, ctor (d a) = a)
    (fold : ∀ {St : Type (max s b)}, (Lay P B X St → St) → T → St)
    (fold_ctor : ∀ {St : Type (max s b)} (a : Lay P B X St → St) (z : Lay P B X T),
      fold a (ctor z) = a (Lay.map (fold a) z))
    (ind : ∀ motive : T → Prop, (∀ z, (∀ i, motive (z.2.2 i)) → motive (ctor z)) → ∀ a, motive a) :
    PolyFix P (inTree B) X T where
  d := d
  bisim := in_bisim ctor d d_ctor ctor_d ind
  erase := fold fun z => Signature.ctorI (σ := shapeSig B) ⟨z.1, z.2.2⟩
  d_erase a := by
    have h : fold (fun z => Signature.ctorI (σ := shapeSig B) ⟨z.1, z.2.2⟩) a =
        Signature.ctorI (σ := shapeSig B) ⟨(d a).1, fun i => fold
          (fun z => Signature.ctorI (σ := shapeSig B) ⟨z.1, z.2.2⟩) ((d a).2.2 i)⟩ := by
      conv => lhs; rw [← ctor_d a]
      exact fold_ctor _ _
    exact inTree_d_of (h ▸ Signature.dtorI_ctorI (σ := shapeSig B) _)
  fill a c := (Signature.child_wf (σ := shapeSig B)).fix
    (C := fun q => (Path P (inTree B) q.2 → X) → T)
    (fun q ih c => ctor ⟨((inTree B).d q.2).1, fun r => c (.here r),
      fun i => ih ⟨(), ((inTree B).d q.2).2 i⟩ ⟨i, rfl⟩ fun r => c (.there i r)⟩)
    ⟨(), a⟩ c
  d_fill a c := by
    rw [WellFounded.fix_eq]
    exact d_ctor _

/-- Induction on a layer, from a contract. -/
theorem in_ind {F : Type t → Type t} (K : Data.Contract (fun _ : Unit => T) (fun Y _ => F (Y ())))
    (toL : ∀ {Y : Type t}, F Y → Lay P B X Y) (ofL : ∀ {Y : Type t}, Lay P B X Y → F Y)
    (ofL_toL : ∀ {Y : Type t} (a : F Y), ofL (toL a) = a)
    (ofL_map : ∀ {Y Y' : Type t} (f : Y → Y') (z : Lay P B X Y),
      ofL (Lay.map f z) = K.map (X := fun _ => Y) (Y := fun _ => Y') (fun _ => f) (i := ()) (ofL z))
    (motive : T → Prop)
    (H : ∀ z : Lay P B X T, (∀ i, motive (z.2.2 i)) → motive (K.ctor (i := ()) (ofL z)))
    (a : T) : motive a := by
  refine K.induction (fun _ => motive) (fun _ y ⟨z, hz⟩ => ?_) (i := ())  a
  have h := H (Lay.map Subtype.val (toL (Y := {x : T // motive x}) z)) (fun i => (_ : Subtype motive).2)
  rw [ofL_map, ofL_toL] at h
  rw [← hz]
  exact h

end In

end Codata
