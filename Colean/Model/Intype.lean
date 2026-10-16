import Colean.Model.Cotype

/-!
# The model, inductive part: the least fixpoint on `Raw`

The inductive dual of `Codata.lean`, for the same signatures: `IsFin` is the *least* fixpoint of
the operator of `IsWf` (`inductive_fixpoint` instead of `coinductive_fixpoint`), and
`Signature.Intype σ : I → Type` the subtype it cuts out. The one-layer constructor and
destructor come from the shared `IsFix` section of `Codata.lean`.

The recursor is where the encoding costs something. `IsFin` is a proposition, so its induction
principle `IsFin.induct` eliminates into `Prop` only; the recursor into a `Sort` is defined by
well-founded recursion on the relation "is an immediate child of", whose well-foundedness *is* a
proposition and is proved by `IsFin.induct`. Consequently `recI` is built from `WellFounded.fix`,
does not reduce definitionally, and its computation rule `recI_ctorI` is propositional. One
dependent recursor `recI` on the container gives everything else: the fold `foldI` into any
family, in any universe, and induction.

The transport theorems `fold_ctor_of`, `rec_of`, `rec_of_ctor`, `induction_of` are what the
command instantiates for its functor `F`, through the isomorphism `toC`/`ofC`; as in the
coinductive case they take the concrete pieces as hypotheses so that `fold` accepts families in
any universe. The contract itself and what follows from it are in `Framework.lean`.

*Spec.* Input: a signature `σ`. Output: the family `Intype σ` with the pieces of the inductive
contract on `σ.Obj` (constructor, fold, induction) and the dependent recursor, and the transport
theorems to a functor `F` isomorphic to `σ.Obj`.
-/

universe w u u₀ v u₁ u₂ u₃

namespace Codata.Signature

variable {σ : Signature.{w, u, u₀, v}} {S : σ.I → Type u₃}

/-! ### The predicate and the type -/

/-- Well-founded trees at index `i`: the least fixpoint of the operator of `IsWf`. -/
def IsFin (i : σ.I) (t : Raw σ.Idx σ.Lbl) : Prop :=
  ∃ z : σ.Obj (fun _ => Raw σ.Idx σ.Lbl) i, t = encode i z ∧ ∀ b, IsFin (σ.idx b) (z.child b)
inductive_fixpoint

theorem IsFin.isFix : σ.IsFix IsFin := fun i t => Iff.of_eq (IsFin.eq_def i t)

/-- The inductive family of a signature. -/
def Intype (σ : Signature.{w, u, u₀, v}) (i : σ.I) : Type (max w u u₀ v) :=
  {t : Raw σ.Idx σ.Lbl // IsFin i t}

/-- The least fixpoint is below the greatest: every well-founded tree is well-formed. -/
theorem IsWf.of_isFin {i : σ.I} {t : Raw σ.Idx σ.Lbl} (h : IsFin i t) : IsWf i t :=
  IsFin.induct IsWf (fun i t h => (IsWf.isFix i t).2 h) i t h

/-- The inclusion of the inductive family into the coinductive one. -/
def Intype.toCotype {i : σ.I} (t : σ.Intype i) : σ.Cotype i := ⟨t.1, IsWf.of_isFin t.2⟩

/-- The constructor on the container. -/
noncomputable def ctorI {i : σ.I} (z : σ.Obj σ.Intype i) : σ.Intype i := IsFin.isFix.ctor z

/-- The destructor on the container. -/
def dtorI {i : σ.I} (t : σ.Intype i) : σ.Obj σ.Intype i := IsFin.isFix.dtor t

theorem dtorI_ctorI {i : σ.I} (z : σ.Obj σ.Intype i) : dtorI (ctorI z) = z :=
  IsFin.isFix.dtor_ctor z

theorem ctorI_dtorI {i : σ.I} (t : σ.Intype i) : ctorI (dtorI t) = t :=
  IsFin.isFix.ctor_dtor t

/-! ### The recursor -/

/-- `s` is an immediate child of `t`, on the total space of the family. -/
def Child (s t : Σ i, σ.Intype i) : Prop := ∃ b, s = ⟨_, (dtorI t.2).child b⟩

/-- Well-founded, by the induction principle of the least fixpoint. -/
theorem child_wf : WellFounded (Child (σ := σ)) := by
  refine ⟨fun ⟨i, t, ht⟩ => ?_⟩
  refine (IsFin.induct (fun i t => IsFin i t ∧ ∀ h : IsFin i t, Acc Child ⟨i, ⟨t, h⟩⟩) ?_
    i t ht).2 ht
  rintro i _ ⟨z, rfl, hz⟩
  refine ⟨(IsFin.isFix i _).2 ⟨z, rfl, fun b => (hz b).1⟩,
    fun h => Acc.intro _ fun s ⟨b, hs⟩ => ?_⟩
  subst hs
  have key : ∀ z₀ : σ.Obj σ.Intype i, z₀ = ⟨z.shape, fun b => ⟨z.child b, (hz b).1⟩⟩ →
      ∀ b, Acc Child ⟨_, z₀.child b⟩ := by
    rintro _ rfl b
    exact (hz b).2 _
  exact key _ (dtorI_ctorI _) b

/-- The recursor on the container, by well-founded recursion on `Child`: dependent, into any
sort. -/
noncomputable def recI {motive : ∀ i, σ.Intype i → Sort u₁}
    (H : ∀ i (z : σ.Obj σ.Intype i), (∀ b, motive _ (z.child b)) → motive i (ctorI z))
    {i : σ.I} (t : σ.Intype i) : motive i t :=
  child_wf.fix (C := fun p => motive p.1 p.2)
    (fun p ih => (congrArg (motive p.1) (ctorI_dtorI p.2)).mp
      (H p.1 (dtorI p.2) fun b => ih ⟨_, (dtorI p.2).child b⟩ ⟨b, rfl⟩))
    ⟨i, t⟩

theorem recI_ctorI {motive : ∀ i, σ.Intype i → Sort u₁}
    (H : ∀ i (z : σ.Obj σ.Intype i), (∀ b, motive _ (z.child b)) → motive i (ctorI z))
    {i : σ.I} (z : σ.Obj σ.Intype i) :
    recI H (ctorI z) = H i z fun b => recI H (z.child b) := by
  show child_wf.fix _ ⟨i, ctorI z⟩ = _
  rw [WellFounded.fix_eq]
  exact cast_ctor_dtor (motive := motive i) ctorI dtorI ctorI_dtorI dtorI_ctorI
    (fun z => H i z fun b => recI H (z.child b)) z

/-- The fold into any family, in any universe. -/
noncomputable def foldI (a : ∀ i, σ.Obj S i → S i) {i : σ.I} (t : σ.Intype i) : S i :=
  recI (motive := fun i _ => S i) (fun i z ih => a i ⟨z.shape, ih⟩) t

theorem foldI_ctorI (a : ∀ i, σ.Obj S i → S i) {i : σ.I} (z : σ.Obj σ.Intype i) :
    foldI a (ctorI z) = a i (Obj.map (fun _ t => foldI a t) z) :=
  recI_ctorI (motive := fun i _ => S i) (fun i z ih => a i ⟨z.shape, ih⟩) z

/-! ### Transport along an isomorphism `F X i ≃ σ.Obj X i` -/

theorem fold_ctor_of {FS : σ.I → Type u₁} {FT : σ.I → Type u₂}
    (toC : ∀ {i}, FT i → σ.Obj σ.Intype i) (ofCT : ∀ {i}, σ.Obj σ.Intype i → FT i)
    (ofCS : ∀ {i}, σ.Obj S i → FS i)
    (map : (∀ j, σ.Intype j → S j) → ∀ {i}, FT i → FS i)
    (ofC_toC : ∀ {i} (y : FT i), ofCT (toC y) = y)
    (ofC_map : ∀ (f : ∀ j, σ.Intype j → S j) {i} (z : σ.Obj σ.Intype i),
      ofCS (Obj.map f z) = map f (ofCT z))
    (a : ∀ i, FS i → S i) {i : σ.I} (y : FT i) :
    foldI (fun j z => a j (ofCS z)) (ctorI (toC y)) =
      a i (map (fun _ t => foldI (fun j z => a j (ofCS z)) t) y) := by
  rw [foldI_ctorI, ofC_map, ofC_toC]

/-- The dependent recursor for `F`, with the induction hypotheses at the positions of `toC`. -/
noncomputable def rec_of {FT : σ.I → Type u₂} (toC : ∀ {i}, FT i → σ.Obj σ.Intype i)
    (ofC : ∀ {i}, σ.Obj σ.Intype i → FT i)
    (toC_ofC : ∀ {i} (z : σ.Obj σ.Intype i), toC (ofC z) = z)
    {motive : ∀ i, σ.Intype i → Sort u₁}
    (H : ∀ i (y : FT i), (∀ b, motive _ ((toC y).child b)) → motive i (ctorI (toC y)))
    {i : σ.I} (t : σ.Intype i) : motive i t :=
  recI (motive := motive)
    (fun i z => (toC_ofC z).rec
      (motive := fun z' _ => (∀ b, motive _ (z'.child b)) → motive i (ctorI z')) (H i (ofC z)))
    t

theorem rec_of_ctor {FT : σ.I → Type u₂} (toC : ∀ {i}, FT i → σ.Obj σ.Intype i)
    (ofC : ∀ {i}, σ.Obj σ.Intype i → FT i)
    (toC_ofC : ∀ {i} (z : σ.Obj σ.Intype i), toC (ofC z) = z)
    (ofC_toC : ∀ {i} (y : FT i), ofC (toC y) = y)
    {motive : ∀ i, σ.Intype i → Sort u₁}
    (H : ∀ i (y : FT i), (∀ b, motive _ ((toC y).child b)) → motive i (ctorI (toC y)))
    {i : σ.I} (y : FT i) :
    rec_of toC ofC toC_ofC H (ctorI (toC y)) =
      H i y fun b => rec_of toC ofC toC_ofC H ((toC y).child b) := by
  have key : ∀ (y' : FT i) (h : toC y' = toC y) (ih : ∀ b, motive _ ((toC y).child b)),
      y' = y → h.rec (motive := fun z' _ => (∀ b, motive _ (z'.child b)) → motive i (ctorI z'))
        (H i y') ih = H i y ih := by
    intro y' h ih hy
    subst hy
    rfl
  rw [rec_of, recI_ctorI]
  exact key _ (toC_ofC (toC y)) _ (ofC_toC y)

/-- Induction for `F`, with the canonical lifting `Data.All`. All families here live in the
universe of `σ.Intype`, so the functor can be a bound variable. -/
theorem induction_of {F : (σ.I → Type (max w u u₀ v)) → σ.I → Type (max w u u₀ v)}
    (map : ∀ {X Y : σ.I → Type (max w u u₀ v)}, (∀ j, X j → Y j) → ∀ {i}, F X i → F Y i)
    (toC : ∀ {i}, F σ.Intype i → σ.Obj σ.Intype i)
    (ofC : ∀ {X : σ.I → Type (max w u u₀ v)} {i}, σ.Obj X i → F X i)
    (toC_ofC : ∀ {i} (z : σ.Obj σ.Intype i), toC (ofC z) = z)
    (ofC_toC : ∀ {i} (y : F σ.Intype i), ofC (toC y) = y)
    (ofC_map : ∀ {X Y : σ.I → Type (max w u u₀ v)} (f : ∀ j, X j → Y j) {i} (z : σ.Obj X i),
      ofC (Obj.map f z) = map f (ofC z))
    (motive : ∀ i, σ.Intype i → Prop)
    (H : ∀ i (y : F σ.Intype i), Data.All map motive y → motive i (ctorI (toC y)))
    {i : σ.I} (t : σ.Intype i) : motive i t :=
  rec_of toC ofC toC_ofC (motive := motive)
    (fun i y ih => H i y ⟨ofC ⟨(toC y).shape, fun b => ⟨(toC y).child b, ih b⟩⟩,
      (ofC_map _ _).symm.trans (ofC_toC y)⟩) t

end Codata.Signature
