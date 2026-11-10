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
hypotheses, so that it applies to the types of the commands through their contracts. The action
on the parameter is the structural one (`d_map`); through a constructor it is computed by
`map_eq_of_d`, and membership, the contents of the slots, is one layer deep (`exists_val_iff`):
the `simp` lemmas of the instances of declared types (`Gen/Derive.lean`).

The second part is the same for a family: a layer at the index `i` of a signature,
`ILay σ P X Y i = Σ s : σ.Shape i, (P i s → X) × ((b : σ.B i s) → Y (σ.idx b))`, has fixpoints
polynomial in `X` at every index (`IPolyFix.equiv`), with the trees of shapes at `i` and their
slots (`IPath`). It is derived from the first part on the total spaces `Σ i, T i`, where a layer
is a plain one whose shapes carry their index; the plain case is not an instance of it.
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

/-- A value is determined by its layer. -/
theorem d_injective : Function.Injective M.d := by
  intro a c h
  refine M.bisim (fun a c => M.d a = M.d c) (fun a c h => ?_) a c h
  have key : ∀ z z' : Lay P B X T, z = z' → ∃ e : z.1 = z'.1,
      (∀ q, z.2.1 q = z'.2.1 (castS e q)) ∧ ∀ i, z.2.2 i = z'.2.2 (castS e i) := by
    rintro _ _ rfl
    exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨e, hv, hk⟩ := key _ _ h
  exact ⟨e, hv, fun i => congrArg M.d (hk i)⟩

/-- The map of a value, through a right inverse `c` of the destructor of the other side: the
value of its layer with the contents and the children mapped. With `c` a constructor, this
computes the map on constructors. -/
theorem map_eq_of_d {X' : Type x'} {T' : Type t'} (M' : PolyFix P 𝕎 X' T') (f : X → X')
    (c : Lay P B X' T' → T') (hc : ∀ z, M'.d (c z) = z) (a : T) :
    M.map M' f a =
      c ⟨(M.d a).1, fun q => f ((M.d a).2.1 q), fun i => M.map M' f ((M.d a).2.2 i)⟩ :=
  M'.d_injective ((M.d_map M' f a).trans (hc _).symm)

/-- The contents of the slots of equal values are the same, whatever the proof of their tree of
shapes. -/
theorem exists_val_congr {a a' : T} (ha : a = a') {c : W} (h : M.erase a = c) (x : X) :
    (∃ r : Path P 𝕎 c, M.val r a h = x) ↔ ∃ r : Path P 𝕎 (M.erase a'), M.val r a' rfl = x := by
  subst ha h
  rfl

/-- The contents of the slots of a value are those of its layer and those of the slots of its
children, at any proof of its tree of shapes. -/
theorem exists_val_iff' {a : T} {c : W} (hc : M.erase a = c) (x : X) :
    (∃ r : Path P 𝕎 c, M.val r a hc = x) ↔ (∃ q, (M.d a).2.1 q = x) ∨
      ∃ i, ∃ r : Path P 𝕎 (M.erase ((M.d a).2.2 i)), M.val r ((M.d a).2.2 i) rfl = x := by
  have e := M.erase_fst hc
  constructor
  · rintro ⟨r, rfl⟩
    cases r with
    | here q => exact .inl ⟨_, rfl⟩
    | there i r => exact .inr ⟨_, (M.exists_val_congr rfl _ _).1 ⟨r, rfl⟩⟩
  · rintro (⟨q, rfl⟩ | ⟨i, r, rfl⟩)
    · refine ⟨.here (castS e q), ?_⟩
      show (M.d a).2.1 (castS e.symm (castS e q)) = _
      rw [castS_castS]
    · obtain ⟨r₁, h₁⟩ := (M.exists_val_congr (a := (M.d a).2.2 (castS e.symm (castS e i)))
        (by rw [castS_castS]) (M.erase_child hc (castS e i)) _).2 ⟨r, rfl⟩
      exact ⟨.there (castS e i) r₁, h₁⟩

/-- The contents of the slots of a value are those of its layer and those of the slots of its
children: membership in one step, for the least and the greatest fixpoint alike, since a slot is
a finite path. -/
theorem exists_val_iff {a : T} {s : S} {v : P s → X} {k : B s → T} (h : M.d a = ⟨s, v, k⟩)
    (x : X) :
    (∃ r, (M.equiv a).2 r = x) ↔ (∃ q, v q = x) ∨ ∃ i, ∃ r, (M.equiv (k i)).2 r = x := by
  have := M.exists_val_iff' (a := a) rfl x
  rw [h] at this
  exact this

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

/-! ## Indexed signatures

A layer at the index `i` of a signature `σ`, polynomial in the parameter `X` and in the family
`Y`, `ILay σ P X Y i = Σ s : σ.Shape i, (P i s → X) × ((b : σ.B i s) → Y (σ.idx b))`: its least
and greatest fixpoints at `i` are polynomial in `X`, with the trees of shapes at `i` (`σ.Intype i`,
`σ.Cotype i`) and their slots (`IPath`). This is the plain case on the total spaces: a layer of
the family is a plain layer whose shapes are the labels `Σ i, σ.Shape i` (`ILay.total`), the trees
of shapes of all indices are plain trees of shapes (`IShapeTree.total`), and so is the fixpoint
(`IPolyFix.total`); the equivalence at `i` is the fibre of the plain one (`IPolyFix.equiv`).

The fixpoint may be a family over another index type `I'`, the one of its contract, read along a
map `ι : σ.I → I'`: the types of a mutual block live over the block's index, whose type mentions
the parameters, while the trees of shapes may not. `ico_bisim` and `iin_ind` take the principles
of the contract along `ι`, and `Along`, `Over` turn the states of `corec` and `fold` on `σ.I` into
states on `I'`.
-/

universe j j' v

namespace Codata

section Indexed

variable {σ : Signature.{j, s, b}}

/-- The positions of the parameter, on the labels. -/
abbrev lblP (σ : Signature.{j, s, b}) (P : (i : σ.I) → σ.Shape i → Type p) (l : σ.Lbl) :
    Type p :=
  P l.1 l.2

/-- The positions of the children, on the labels. -/
abbrev lblB (σ : Signature.{j, s, b}) (l : σ.Lbl) : Type b := σ.B l.1 l.2

variable (σ) (P : (i : σ.I) → σ.Shape i → Type p) in
/-- A layer at the index `i`, polynomial in the parameter `X` and in the family `Y`. -/
abbrev ILay (X : Type x) (Y : σ.I → Type y) (i : σ.I) : Type (max s p b x y) :=
  Σ s : σ.Shape i, (P i s → X) × ((b : σ.B i s) → Y (σ.idx b))

variable {P : (i : σ.I) → σ.Shape i → Type p}

/-- The action on the recursive family. -/
def ILay.map {X : Type x} {Y : σ.I → Type y} {Y' : σ.I → Type y'} (f : ∀ j, Y j → Y' j)
    {i : σ.I} (z : ILay σ P X Y i) : ILay σ P X Y' i :=
  ⟨z.1, z.2.1, fun b => f _ (z.2.2 b)⟩

/-- Two layers with the same shape and contents, and related children. -/
def ILay.Rel {X : Type x} {Y : σ.I → Type y} {Y' : σ.I → Type y'} (R : ∀ j, Y j → Y' j → Prop)
    {i : σ.I} (z : ILay σ P X Y i) (z' : ILay σ P X Y' i) : Prop :=
  ∃ (s : σ.Shape i) (v : P i s → X) (k : (b : σ.B i s) → Y (σ.idx b))
    (k' : (b : σ.B i s) → Y' (σ.idx b)), z = ⟨s, v, k⟩ ∧ z' = ⟨s, v, k'⟩ ∧ ∀ b, R _ (k b) (k' b)

/-- A layer as a plain layer of the total space: its shape with its index. -/
def ILay.total {X : Type x} {Y : σ.I → Type y} {i : σ.I} (z : ILay σ P X Y i) :
    Lay (lblP σ P) (lblB σ) X (Σ j, Y j) :=
  ⟨⟨i, z.1⟩, z.2.1, fun b => ⟨_, z.2.2 b⟩⟩

theorem ILay.total_inj {X : Type x} {Y : σ.I → Type y} {i : σ.I} {z z' : ILay σ P X Y i}
    (h : z.total = z'.total) : z = z' := by
  obtain ⟨s, v, k⟩ := z
  obtain ⟨s', v', k'⟩ := z'
  obtain rfl : s = s' := eq_of_heq (Sigma.mk.inj (Sigma.mk.inj h).1).2
  have h' := Prod.mk.inj (eq_of_heq (Sigma.mk.inj h).2)
  obtain rfl : v = v' := h'.1
  obtain rfl : k = k' := funext fun b => eq_of_heq (Sigma.mk.inj (congrFun h'.2 b)).2
  rfl

/-! ### Trees of shapes and slots -/

variable (σ) in
/-- An indexed tree of shapes: a family with a destructor and the bisimulation principle. -/
structure IShapeTree (W : σ.I → Type w) where
  d {i : σ.I} : W i → σ.Obj W i
  bisim (R : ∀ i, W i → W i → Prop) (H : ∀ i x y, R i x y → Signature.Obj.Rel R (d x) (d y))
    {i : σ.I} {x y : W i} : R i x y → x = y

/-- The trees of shapes of all indices, as plain trees of shapes over the labels. -/
def IShapeTree.total {W : σ.I → Type w} (𝕎 : IShapeTree σ W) : ShapeTree (lblB σ) (Σ i, W i) where
  d a := ⟨⟨a.1, (𝕎.d a.2).shape⟩, fun b => ⟨_, (𝕎.d a.2).child b⟩⟩
  bisim R H := by
    rintro ⟨i, x⟩ ⟨i', y⟩ h
    obtain rfl : i = i' := congrArg Sigma.fst (H _ _ h).1
    refine congrArg (Sigma.mk i) (𝕎.bisim (fun i x y => R ⟨i, x⟩ ⟨i, y⟩) (fun i x y hxy => ?_) h)
    obtain ⟨e, hk⟩ := H _ _ hxy
    revert e hk
    obtain ⟨sx, kx⟩ := 𝕎.d x
    obtain ⟨sy, ky⟩ := 𝕎.d y
    intro e hk
    obtain rfl : sx = sy := eq_of_heq (Sigma.mk.inj e).2
    exact ⟨sx, kx, ky, rfl, rfl, hk⟩

variable (P) in
/-- The slots of a tree of shapes at the index `i`: the paths from it in the total tree. -/
abbrev IPath {W : σ.I → Type w} (𝕎 : IShapeTree σ W) (i : σ.I) (a : W i) :
    Type (max p b j w) :=
  Path (lblP σ P) 𝕎.total ⟨i, a⟩

/-! ### The fixpoint -/

variable (P) in
/-- A fixpoint of the layer at `X`, a family over `σ.I`, with its trees of shapes: a destructor
and the bisimulation principle, `erase` to the tree of shapes, and `fill` back. -/
structure IPolyFix {W : σ.I → Type w} (𝕎 : IShapeTree σ W) (X : Type x) (T : σ.I → Type t) where
  d {i : σ.I} : T i → ILay σ P X T i
  bisim (R : ∀ i, T i → T i → Prop) (H : ∀ i a c, R i a c → ILay.Rel R (d a) (d c)) {i : σ.I}
    (a c : T i) : R i a c → a = c
  erase {i : σ.I} : T i → W i
  d_erase {i : σ.I} (a : T i) : 𝕎.d (erase a) = ⟨(d a).1, fun b => erase ((d a).2.2 b)⟩
  fill {i : σ.I} (c : W i) : (IPath P 𝕎 i c → X) → T i
  d_fill {i : σ.I} (c : W i) (f : IPath P 𝕎 i c → X) :
    d (fill c f) = ⟨(𝕎.d c).shape, fun q => f (.here q), fun b => fill _ fun r => f (.there b r)⟩

namespace IPolyFix

variable {W : σ.I → Type w} {𝕎 : IShapeTree σ W} {X : Type x} {T : σ.I → Type t}
  (M : IPolyFix P 𝕎 X T)

/-- The fixpoint on the total space, a plain one. -/
def total : PolyFix (lblP σ P) 𝕎.total X (Σ i, T i) where
  d a := (M.d a.2).total
  bisim R H := by
    rintro ⟨i, x⟩ ⟨i', y⟩ h
    obtain rfl : i = i' := congrArg Sigma.fst (H _ _ h).1
    refine congrArg (Sigma.mk i) (M.bisim (fun i x y => R ⟨i, x⟩ ⟨i, y⟩) (fun i x y hxy => ?_) x y h)
    obtain ⟨e, hv, hk⟩ := H _ _ hxy
    revert e hv hk
    obtain ⟨sx, vx, kx⟩ := M.d x
    obtain ⟨sy, vy, ky⟩ := M.d y
    intro e hv hk
    obtain rfl : sx = sy := eq_of_heq (Sigma.mk.inj e).2
    obtain rfl : vx = vy := funext hv
    exact ⟨sx, vx, kx, ky, rfl, rfl, hk⟩
  erase a := ⟨a.1, M.erase a.2⟩
  d_erase a := by
    show (⟨⟨a.1, (𝕎.d (M.erase a.2)).shape⟩, fun b => ⟨_, (𝕎.d (M.erase a.2)).child b⟩⟩ :
      Σ l : σ.Lbl, (lblB σ l → Σ i, W i)) = _
    rw [M.d_erase]
    rfl
  fill a f := ⟨a.1, M.fill a.2 f⟩
  d_fill a f := by
    show (M.d (M.fill a.2 f)).total = _
    rw [M.d_fill]
    rfl

/-- A value at `i` is a tree of shapes at `i` with the contents of its slots. -/
def equiv (i : σ.I) : T i ≃ Poly (W i) (IPath P 𝕎 i) X where
  toFun a := ⟨M.erase a, fun r => M.total.val r ⟨i, a⟩ rfl⟩
  invFun z := M.fill z.1 z.2
  left_inv a := eq_of_heq (Sigma.mk.inj (M.total.fill_val_eq ⟨i, a⟩ rfl)).2
  right_inv := by
    rintro ⟨c, f⟩
    have h : M.erase (M.fill c f) = c := eq_of_heq (Sigma.mk.inj (M.total.erase_fill ⟨i, c⟩ f)).2
    have key : ∀ (c' : W i) (h' : M.total.erase ⟨i, M.fill c f⟩ = ⟨i, c'⟩),
        M.erase (M.fill c f) = c' →
        (⟨M.erase (M.fill c f), fun r => M.total.val r ⟨i, M.fill c f⟩ rfl⟩ :
          Poly (W i) (IPath P 𝕎 i) X) = ⟨c', fun r => M.total.val r ⟨i, M.fill c f⟩ h'⟩ := by
      rintro _ _ rfl
      rfl
    exact (key c (congrArg (Sigma.mk i) h) h).trans
      (congrArg (Sigma.mk c) (funext fun r => M.total.val_fill r _ _ f rfl))

/-- The action on the parameter: the same tree of shapes, the contents mapped. -/
def map {X' : Type x'} {T' : σ.I → Type t'} (M' : IPolyFix P 𝕎 X' T') (f : X → X') {i : σ.I}
    (a : T i) : T' i :=
  (M'.equiv i).symm (Poly.map f (M.equiv i a))

theorem equiv_map {X' : Type x'} {T' : σ.I → Type t'} (M' : IPolyFix P 𝕎 X' T') (f : X → X')
    {i : σ.I} (a : T i) : M'.equiv i (M.map M' f a) = Poly.map f (M.equiv i a) :=
  (M'.equiv i).apply_symm_apply _

theorem total_map {X' : Type x'} {T' : σ.I → Type t'} (M' : IPolyFix P 𝕎 X' T') (f : X → X')
    {i : σ.I} (a : T i) : M.total.map M'.total f ⟨i, a⟩ = ⟨i, M.map M' f a⟩ :=
  rfl

/-- The action on the parameter is the structural one: it maps the contents of the layer and goes
on in the children. -/
theorem d_map {X' : Type x'} {T' : σ.I → Type t'} (M' : IPolyFix P 𝕎 X' T') (f : X → X')
    {i : σ.I} (a : T i) :
    M'.d (M.map M' f a) =
      ⟨(M.d a).1, fun q => f ((M.d a).2.1 q), fun b => M.map M' f ((M.d a).2.2 b)⟩ :=
  ILay.total_inj (M.total.d_map M'.total f ⟨i, a⟩)

/-- A value is determined by its layer. -/
theorem d_injective {i : σ.I} : Function.Injective (M.d (i := i)) := by
  intro a c h
  refine M.bisim (fun _ a c => M.d a = M.d c) (fun _ a c h => ?_) a c h
  rcases hd : M.d a with ⟨s, v, k⟩
  exact ⟨s, v, k, k, rfl, h ▸ hd, fun _ => rfl⟩

/-- The map of a value, through a right inverse `c` of the destructor of the other side. -/
theorem map_eq_of_d {X' : Type x'} {T' : σ.I → Type t'} (M' : IPolyFix P 𝕎 X' T') (f : X → X')
    (c : ∀ {i}, ILay σ P X' T' i → T' i) (hc : ∀ {i} (z : ILay σ P X' T' i), M'.d (c z) = z)
    {i : σ.I} (a : T i) :
    M.map M' f a =
      c ⟨(M.d a).1, fun q => f ((M.d a).2.1 q), fun b => M.map M' f ((M.d a).2.2 b)⟩ :=
  M'.d_injective ((M.d_map M' f a).trans (hc _).symm)

/-- The contents of the slots of a value at `i` are those of its layer and those of the slots
of its children. -/
theorem exists_val_iff {i : σ.I} {a : T i} {s : σ.Shape i} {v : P i s → X}
    {k : (b : σ.B i s) → T (σ.idx b)} (h : M.d a = ⟨s, v, k⟩) (x : X) :
    (∃ r, (M.equiv i a).2 r = x) ↔ (∃ q, v q = x) ∨ ∃ b, ∃ r, (M.equiv _ (k b)).2 r = x :=
  M.total.exists_val_iff (a := ⟨i, a⟩) (s := ⟨i, s⟩) (k := fun b => ⟨_, k b⟩)
    (show (M.d a).total = _ by rw [h]; rfl) x

end IPolyFix

/-! ### Trees of shapes -/

variable (σ) in
/-- The coinductive trees of shapes. -/
noncomputable def coITree : IShapeTree σ σ.Cotype where
  d := Signature.dtorC
  bisim := Signature.bisimC

variable (σ) in
/-- The inductive trees of shapes. -/
noncomputable def inITree : IShapeTree σ σ.Intype where
  d := Signature.dtorI
  bisim R H {i} x y h := by
    have key : ∀ i (x : σ.Intype i) y, R i x y → x = y := by
      intro i x
      refine Signature.recI (motive := fun i x => ∀ y, R i x y → x = y) ?_ x
      intro i z ih y hy
      obtain ⟨s, c, c', hz, hy', hc⟩ := H i _ y hy
      rw [Signature.dtorI_ctorI] at hz
      subst hz
      rw [← Signature.ctorI_dtorI y, hy']
      exact congrArg (fun c => Signature.ctorI ⟨s, c⟩) (funext fun b => ih b _ (hc b))
    exact key i x y h

/-! ### The two instances -/

section Co

variable {X : Type x} {T : σ.I → Type t}

/-- A coinductive fixpoint of the layer. -/
noncomputable def icoFix (d : ∀ {i}, T i → ILay σ P X T i)
    (corec : ∀ {St : σ.I → Type (max j s b p x)}, (∀ i, St i → ILay σ P X St i) →
      ∀ {i}, St i → T i)
    (d_corec : ∀ {St : σ.I → Type (max j s b p x)} (c : ∀ i, St i → ILay σ P X St i) {i}
      (a : St i), d (corec c a) = ILay.map (fun _ => corec c) (c i a))
    (bisim : ∀ (R : ∀ i, T i → T i → Prop), (∀ i a c, R i a c → ILay.Rel R (d a) (d c)) →
      ∀ {i} (a c : T i), R i a c → a = c) :
    IPolyFix P (coITree σ) X T where
  d := d
  bisim := bisim
  erase := Signature.corecC (σ := σ) (S := T) fun _ a => ⟨(d a).1, (d a).2.2⟩
  d_erase a := Signature.dtorC_corecC _ a
  fill c f := corec (St := fun i => Σ c : σ.Cotype i, IPath P (coITree σ) i c → X)
    (fun _ z => ⟨(Signature.dtorC z.1).shape, fun q => z.2 (.here q),
      fun b => ⟨_, fun r => z.2 (.there b r)⟩⟩) ⟨c, f⟩
  d_fill _ _ := d_corec _ _

variable {I' : Type j'}

/-- The states of a coalgebra on `σ.I` as states on `I'`, along `ι`: at `i'`, a state at some `i`
over `i'`. -/
def Along (ι : σ.I → I') (St : σ.I → Type v) (i' : I') : Type (max j v) :=
  {a : Σ i, St i // ι a.1 = i'}

/-- A state at `i` as a state at `ι i`. -/
def Along.mk (ι : σ.I → I') {St : σ.I → Type v} {i : σ.I} (a : St i) : Along ι St (ι i) :=
  ⟨⟨i, a⟩, rfl⟩

/-- The coalgebra on `I'` of a coalgebra `c` on `σ.I`, through `ofL` from layers to `G`. -/
def Along.coalg (ι : σ.I → I') {St : σ.I → Type v} {G : I' → Type y}
    (ofL : ∀ {i}, ILay σ P X (fun j => Along ι St (ι j)) i → G (ι i))
    (c : ∀ i, St i → ILay σ P X St i) (i' : I') (a : Along ι St i') : G i' :=
  a.2 ▸ ofL (ILay.map (fun _ a => Along.mk ι a) (c a.1.1 a.1.2))

theorem Along.coalg_mk (ι : σ.I → I') {St : σ.I → Type v} {G : I' → Type y}
    (ofL : ∀ {i}, ILay σ P X (fun j => Along ι St (ι j)) i → G (ι i))
    (c : ∀ i, St i → ILay σ P X St i) {i : σ.I} (a : St i) :
    Along.coalg ι ofL c (ι i) (Along.mk ι a) = ofL (ILay.map (fun _ a => Along.mk ι a) (c i a)) :=
  rfl

/-- The bisimulation principle of a layer destructor, from a contract along `ι`. -/
theorem ico_bisim {T' : I' → Type t} {F : (I' → Type t) → I' → Type t} (K : Contract T' F)
    (ι : σ.I → I') (d : ∀ {i}, T' (ι i) → ILay σ P X (fun j => T' (ι j)) i)
    (ofL : ∀ {Y : I' → Type t} {i}, ILay σ P X (fun j => Y (ι j)) i → F Y (ι i))
    (ofL_d : ∀ {i} (a : T' (ι i)), ofL (d a) = K.dtor a)
    (ofL_map : ∀ {Y Y' : I' → Type t} (f : ∀ j, Y j → Y' j) {i}
      (z : ILay σ P X (fun j => Y (ι j)) i), ofL (ILay.map (fun j => f (ι j)) z) = K.map f (ofL z))
    (R : ∀ i, T' (ι i) → T' (ι i) → Prop) (H : ∀ i a c, R i a c → ILay.Rel R (d a) (d c))
    {i : σ.I} (a c : T' (ι i)) (h : R i a c) : a = c := by
  let R' (i' : I') (x y : T' i') : Prop := ∃ (i : σ.I) (e : i' = ι i), R i (e ▸ x) (e ▸ y)
  refine K.bisim R' (fun i' x y hxy => ?_) (i := ι i) ⟨i, rfl, h⟩
  obtain ⟨i, rfl, r⟩ := hxy
  obtain ⟨s, v, k, k', hx, hy, hk⟩ := H i x y r
  let Pr (i' : I') : Type t := {p : T' i' × T' i' // R' i' p.1 p.2}
  refine ⟨ofL (Y := Pr) ⟨s, v, fun b => ⟨(k b, k' b), _, rfl, hk b⟩⟩, ?_, ?_⟩
  · refine (ofL_map (fun i' (p : Pr i') => p.1.1) _).symm.trans ?_
    rw [← ofL_d, hx]
    rfl
  · refine (ofL_map (fun i' (p : Pr i') => p.1.2) _).symm.trans ?_
    rw [← ofL_d, hy]
    rfl

end Co

section In

variable {X : Type x} {T : σ.I → Type t}

/-- The bisimulation principle of an inductive fixpoint. -/
theorem iin_bisim (ctor : ∀ {i}, ILay σ P X T i → T i) (d : ∀ {i}, T i → ILay σ P X T i)
    (d_ctor : ∀ {i} (z : ILay σ P X T i), d (ctor z) = z) (ctor_d : ∀ {i} (a : T i), ctor (d a) = a)
    (ind : ∀ motive : ∀ i, T i → Prop,
      (∀ i (z : ILay σ P X T i), (∀ b, motive _ (z.2.2 b)) → motive i (ctor z)) →
      ∀ {i} (a : T i), motive i a)
    (R : ∀ i, T i → T i → Prop) (H : ∀ i a c, R i a c → ILay.Rel R (d a) (d c))
    {i : σ.I} (a c : T i) (h : R i a c) : a = c := by
  refine ind (fun i a => ∀ c, R i a c → a = c) (fun i z ih c hc => ?_) a c h
  obtain ⟨s, v, k, k', hz, hc', hk⟩ := H i _ c hc
  rw [d_ctor] at hz
  subst hz
  rw [← ctor_d c, hc']
  exact congrArg (fun k => ctor ⟨s, v, k⟩) (funext fun b => ih b _ (hk b))

/-- An inductive fixpoint of the layer. -/
noncomputable def iinFix (ctor : ∀ {i}, ILay σ P X T i → T i) (d : ∀ {i}, T i → ILay σ P X T i)
    (d_ctor : ∀ {i} (z : ILay σ P X T i), d (ctor z) = z) (ctor_d : ∀ {i} (a : T i), ctor (d a) = a)
    (fold : ∀ {St : σ.I → Type (max j s b)}, (∀ i, ILay σ P X St i → St i) → ∀ {i}, T i → St i)
    (fold_ctor : ∀ {St : σ.I → Type (max j s b)} (a : ∀ i, ILay σ P X St i → St i) {i}
      (z : ILay σ P X T i), fold a (ctor z) = a i (ILay.map (fun _ => fold a) z))
    (ind : ∀ motive : ∀ i, T i → Prop,
      (∀ i (z : ILay σ P X T i), (∀ b, motive _ (z.2.2 b)) → motive i (ctor z)) →
      ∀ {i} (a : T i), motive i a) :
    IPolyFix P (inITree σ) X T where
  d := d
  bisim := iin_bisim ctor d d_ctor ctor_d ind
  erase := fold fun _ z => Signature.ctorI (σ := σ) ⟨z.1, z.2.2⟩
  d_erase a := by
    have h : fold (fun _ z => Signature.ctorI (σ := σ) ⟨z.1, z.2.2⟩) a =
        Signature.ctorI (σ := σ) ⟨(d a).1, fun b => fold
          (fun _ z => Signature.ctorI (σ := σ) ⟨z.1, z.2.2⟩) ((d a).2.2 b)⟩ := by
      conv => lhs; rw [← ctor_d a]
      exact fold_ctor _ _
    exact h ▸ Signature.dtorI_ctorI (σ := σ) _
  fill c f := (Signature.child_wf (σ := σ)).fix
    (C := fun q => (IPath P (inITree σ) q.1 q.2 → X) → T q.1)
    (fun q ih f => ctor ⟨(Signature.dtorI q.2).shape, fun r => f (.here r),
      fun b => ih ⟨_, (Signature.dtorI q.2).child b⟩ ⟨b, rfl⟩ fun r => f (.there b r)⟩)
    ⟨_, c⟩ f
  d_fill c f := by
    rw [WellFounded.fix_eq]
    exact d_ctor _

variable {I' : Type j'}

/-- The states of an algebra on `σ.I` as states on `I'`, along `ι`: at `i'`, a state at every `i`
over `i'`. -/
def Over (ι : σ.I → I') (St : σ.I → Type v) (i' : I') : Type (max j v) :=
  ∀ i, i' = ι i → St i

/-- The algebra on `I'` of an algebra `a` on `σ.I`, through `toL` from `G` to layers. -/
def Over.alg (ι : σ.I → I') {St : σ.I → Type v} {G : I' → Type y}
    (toL : ∀ {i}, G (ι i) → ILay σ P X (fun j => Over ι St (ι j)) i)
    (a : ∀ i, ILay σ P X St i → St i) (i' : I') (z : G i') : Over ι St i' :=
  fun i e => a i (ILay.map (fun j g => g j rfl) (toL (e ▸ z)))

theorem Over.alg_apply (ι : σ.I → I') {St : σ.I → Type v} {G : I' → Type y}
    (toL : ∀ {i}, G (ι i) → ILay σ P X (fun j => Over ι St (ι j)) i)
    (a : ∀ i, ILay σ P X St i → St i) {i : σ.I} (z : G (ι i)) :
    Over.alg ι toL a (ι i) z i rfl = a i (ILay.map (fun j g => g j rfl) (toL z)) :=
  rfl

/-- Induction on a layer, from a contract along `ι`. -/
theorem iin_ind {T' : I' → Type t} {F : (I' → Type t) → I' → Type t} (K : Data.Contract T' F)
    (ι : σ.I → I')
    (toL : ∀ {Y : I' → Type t} {i}, F Y (ι i) → ILay σ P X (fun j => Y (ι j)) i)
    (ofL : ∀ {Y : I' → Type t} {i}, ILay σ P X (fun j => Y (ι j)) i → F Y (ι i))
    (ofL_toL : ∀ {Y : I' → Type t} {i} (a : F Y (ι i)), ofL (toL a) = a)
    (ofL_map : ∀ {Y Y' : I' → Type t} (f : ∀ j, Y j → Y' j) {i}
      (z : ILay σ P X (fun j => Y (ι j)) i), ofL (ILay.map (fun j => f (ι j)) z) = K.map f (ofL z))
    (motive : ∀ i, T' (ι i) → Prop)
    (H : ∀ i (z : ILay σ P X (fun j => T' (ι j)) i), (∀ b, motive _ (z.2.2 b)) →
      motive i (K.ctor (ofL z)))
    {i : σ.I} (a : T' (ι i)) : motive i a := by
  let motive' (i' : I') (x : T' i') : Prop := ∀ i (e : i' = ι i), motive i (e ▸ x)
  refine K.induction motive' (fun i' y hy => ?_) a i rfl
  obtain ⟨z, rfl⟩ := hy
  rintro i rfl
  let val (j' : I') (x : {x : T' j' // motive' j' x}) : T' j' := x.1
  have h := H i (ILay.map (fun j => val (ι j)) (toL z)) (fun b => ((toL z).2.2 b).2 _ rfl)
  rw [ofL_map val, ofL_toL] at h
  exact h

end In

end Indexed

end Codata
