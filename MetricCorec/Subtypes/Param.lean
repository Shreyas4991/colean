import MetricCorec.Subtypes.Container
import MetricCorec.Subtypes.Data

/-!
# A (co)inductive type is a container in its parameter

A declaration with a parameter `X : J → Type` (a family; a type parameter is the case
`J = Unit`) occurring only at *positions* (as the type of a field, under a function type, or
inside a container) has shapes of the form `Σ s₀, (p : P s₀) → X (pidx p)`: the erased shapes
`Shape₀` with the parameter positions `P` and their indices `pidx`. A `PSignature` is a
signature with such parameter positions; `PSignature.sig` is the ordinary signature at a
parameter `X`, for shapes presented through an equivalence `e : S i ≃ Σ s₀, (p : P s₀) → X
(pidx p)` (the command generates `S` as the constructors' data and `e` by cases), and
`PSignature.sig₀` the signature of the erased trees, whose shapes are `Shape₀` itself.

The family `X ↦ Intype (ψ.sig (S X) (e X)) i` is then an indexed container
(`PSignature.icontainer`, and `PSignature.container` for a type parameter), with the erased
trees as shapes and, as positions, the paths to a node together with a parameter position of
its erased shape, at that position's index; likewise for `Cotype` (`cocontainer`,
`icocontainer`). Everything is
pathwise on `Raw`: `erase` relabels a tree, `reattach` puts values back, and the two laws are
extensionality on paths. A position carries the proof that its path leads to a node, so that
transporting positions along an equality of trees changes only a proof (`Pos.cast`), and the
facts about `reattach` and `valAt` are stated under hypotheses on `sh.get pa`, which keeps all
rewriting outside dependent matches. This is Mathlib's `MvPFunctor.wp`, the W-type of a
polynomial functor as a polynomial functor, here for the encoding, and `mp` for the coinductive
types.
-/

universe w u u₀ v p u' j

namespace Codata

/-- A signature with parameter positions: erased shapes, the positions of the parameter with
their indices in the parameter's family, and the recursive positions on them. -/
structure PSignature where
  I : Type w
  J : Type j
  Shape₀ : I → Type u₀
  P : ∀ {i : I}, Shape₀ i → Type p
  pidx : ∀ {i : I} {s₀ : Shape₀ i}, P s₀ → J
  B : (i : I) → Shape₀ i → Type v
  idx : ∀ {i : I} {s : Shape₀ i}, B i s → I

namespace PSignature

variable (ψ : PSignature.{w, u₀, v, p, j})

/-- The signature of the erased trees. -/
abbrev sig₀ : Signature.{w, u₀, u₀, v} :=
  { I := ψ.I, Shape := ψ.Shape₀, Shape₀ := ψ.Shape₀, sh₀ := id, B := ψ.B, idx := ψ.idx }

/-- The signature at a parameter `X`, with shapes `S` presented as layers over the erased
shapes. -/
abbrev sig {X : ψ.J → Type u'} (S : ψ.I → Type u)
    (e : ∀ {i : ψ.I}, S i ≃ Σ s₀ : ψ.Shape₀ i, (p : ψ.P s₀) → X (ψ.pidx p)) :
    Signature.{w, u, u₀, v} :=
  { I := ψ.I, Shape := S, Shape₀ := ψ.Shape₀, sh₀ := fun s => (e s).1, B := ψ.B, idx := ψ.idx }

/-- The raw erased trees. -/
abbrev Raw₀ : Type (max w u₀ v) := Raw ψ.sig₀.Idx ψ.sig₀.Lbl

/-- The raw trees of the signature at `X`. -/
abbrev RawS {X : ψ.J → Type u'} (S : ψ.I → Type u)
    (e : ∀ {i : ψ.I}, S i ≃ Σ s₀ : ψ.Shape₀ i, (p : ψ.P s₀) → X (ψ.pidx p)) :
    Type (max w u u₀ v) :=
  Raw (ψ.sig S e).Idx (ψ.sig S e).Lbl

/-- The positions of an erased tree: a path to a node and a parameter position of its shape. -/
def Pos (sh : ψ.Raw₀) : Type (max w u₀ v p) :=
  Σ (pa : List ψ.sig₀.Idx) (l : ψ.sig₀.Lbl), PLift (sh.get pa = some l) × ψ.P l.2

variable {ψ}

/-- The index of a position in the parameter's family. -/
def Pos.idx {sh : ψ.Raw₀} (x : ψ.Pos sh) : ψ.J := ψ.pidx x.2.2.2

/-- Transport a position along an equality of trees: only its proof changes. -/
def Pos.cast {sh sh' : ψ.Raw₀} (h : sh = sh') (x : ψ.Pos sh) : ψ.Pos sh' :=
  ⟨x.1, x.2.1, ⟨h ▸ x.2.2.1.1⟩, x.2.2.2⟩

theorem cast_pos {sh sh' : ψ.Raw₀} (h : sh = sh') (x : ψ.Pos sh) :
    cast (congrArg ψ.Pos h) x = Pos.cast h x := by
  subst h
  rfl

/-- A position of a child, as a position of the tree. -/
def Pos.cons {sh : ψ.Raw₀} (j : ψ.sig₀.Idx) (x : ψ.Pos (sh.child j)) : ψ.Pos sh :=
  ⟨j :: x.1, x.2.1, ⟨x.2.2.1.1⟩, x.2.2.2⟩

/-- Transport a recursive position along an equality of erased shapes. -/
def castP {i : ψ.I} {s₀ s₀' : ψ.Shape₀ i} (h : s₀ = s₀') (b : ψ.B i s₀) : ψ.B i s₀' := h ▸ b

theorem castP_castP {i : ψ.I} {s₀ s₀' : ψ.Shape₀ i} (h : s₀ = s₀') (h' : s₀' = s₀)
    (b : ψ.B i s₀) : castP h' (castP h b) = b := by
  subst h
  rfl

section

variable {X : ψ.J → Type u'} {S : ψ.I → Type u}
  (e : ∀ {i : ψ.I}, S i ≃ Σ s₀ : ψ.Shape₀ i, (p : ψ.P s₀) → X (ψ.pidx p))

/-- The erased shape of a reattached shape is the original one. -/
theorem sh₀_symm {i : ψ.I} (s₀ : ψ.Shape₀ i) (f : (p : ψ.P s₀) → X (ψ.pidx p)) :
    (e (e.symm ⟨s₀, f⟩)).1 = s₀ :=
  congrArg Sigma.fst (e.apply_symm_apply _)

/-- `castB` along an equality of labels with the same index is `castP`. -/
theorem castB_mk {i : ψ.I} {s₀ s₀' : ψ.Shape₀ i} (h : s₀ = s₀') (b : ψ.B i s₀) :
    Signature.castB (σ := ψ.sig S e) (congrArg (Sigma.mk i) h) b = castP h b := by
  subst h
  rfl

/-- The index of a transported position, stated between the two signatures. -/
theorem idx_castP {i : ψ.I} {s₀ s₀' : ψ.Shape₀ i} (h : s₀ = s₀') (b : ψ.B i s₀) :
    ψ.sig₀.idx (castP h b) = (ψ.sig S e).idx b := by
  subst h
  rfl

/-! ### Erasure -/

/-- Erase the parameter's values from a label. -/
def eraseL (l : (ψ.sig S e).Lbl) : ψ.sig₀.Lbl := ⟨l.1, (e l.2).1⟩

/-- Erase the parameter's values from a tree. -/
def erase (t : ψ.RawS S e) : ψ.Raw₀ := Raw.mapL (eraseL e) t

@[simp] theorem get_erase (t : ψ.RawS S e) (pa : List ψ.sig₀.Idx) :
    (erase e t).get pa = (t.get pa).map (eraseL e) := rfl

/-- A child of a layer at a label with the same index and an equal erased shape. -/
theorem child_encode_castP {i : ψ.I} (z : (ψ.sig S e).Obj (fun _ => ψ.RawS S e) i)
    {s₀ : ψ.Shape₀ i} (h : s₀ = (e z.shape).1) (b : ψ.B i s₀) :
    (Signature.encode i z).child ⟨⟨i, s₀⟩, b⟩ = z.child (castP h b) := by
  subst h
  exact Signature.child_encode_self (σ := ψ.sig S e) i z b

theorem child_encode_castP₀ {i : ψ.I} (z : ψ.sig₀.Obj (fun _ => ψ.Raw₀) i)
    {s₀ : ψ.Shape₀ i} (h : s₀ = z.shape) (b : ψ.B i s₀) :
    (Signature.encode i z).child ⟨⟨i, s₀⟩, b⟩ = z.child (castP h b) := by
  subst h
  exact Signature.child_encode_self (σ := ψ.sig₀) i z b

theorem erase_encode (i : ψ.I) (z : (ψ.sig S e).Obj (fun _ => ψ.RawS S e) i) :
    erase e (Signature.encode i z) =
      Signature.encode (σ := ψ.sig₀) i ⟨(e z.shape).1, fun b => erase e (z.child b)⟩ := by
  refine Raw.ext_root_child rfl fun ⟨l, b⟩ => ?_
  change (Raw.mapL (eraseL e) (Signature.encode i z)).child ⟨l, b⟩ = _
  rw [Raw.child_mapL]
  by_cases h : l = ⟨i, (e z.shape).1⟩
  · subst h
    exact (congrArg (Raw.mapL _) (Signature.child_encode_self (σ := ψ.sig S e) i z b)).trans
      (Signature.child_encode_self (σ := ψ.sig₀) i
        ⟨(e z.shape).1, fun b => erase e (z.child b)⟩ b).symm
  · rw [Signature.child_encode_of_ne (σ := ψ.sig S e) i z h b,
      Signature.child_encode_of_ne (σ := ψ.sig₀) i ⟨(e z.shape).1, fun b => erase e (z.child b)⟩
        h b]
    rfl

theorem isFin_erase {i : ψ.I} {t : ψ.RawS S e} (h : Signature.IsFin i t) :
    Signature.IsFin (σ := ψ.sig₀) i (erase e t) := by
  refine Signature.IsFin.induct (σ := ψ.sig S e)
    (fun i t => Signature.IsFin (σ := ψ.sig₀) i (erase e t)) ?_ i t h
  rintro i _ ⟨z, rfl, hz⟩
  rw [erase_encode]
  refine (Signature.IsFin.isFix (σ := ψ.sig₀) i _).2 ⟨_, rfl, fun b => ?_⟩
  exact hz b

theorem isWf_erase {i : ψ.I} {t : ψ.RawS S e} (h : Signature.IsWf i t) :
    Signature.IsWf (σ := ψ.sig₀) i (erase e t) := by
  refine Signature.IsWf.coinduct (σ := ψ.sig₀)
    (fun i t' => ∃ t : ψ.RawS S e, t' = erase e t ∧ Signature.IsWf (σ := ψ.sig S e) i t)
    ?_ i _ ⟨t, rfl, h⟩
  rintro i _ ⟨t, rfl, ht⟩
  obtain ⟨z, rfl, hz⟩ := (Signature.IsWf.isFix (σ := ψ.sig S e) i t).1 ht
  rw [erase_encode]
  exact ⟨_, rfl, fun b => ⟨_, rfl, hz b⟩⟩

/-- The value at a parameter position of the label at a path, from the label itself. -/
def valAtO (o : Option (ψ.sig S e).Lbl) (l : ψ.sig₀.Lbl) (h : o.map (eraseL e) = some l)
    (q : ψ.P l.2) : X (ψ.pidx q) :=
  match o, h with
  | some l₀, h =>
    match l, Option.some.inj h, q with
    | _, rfl, q => (e l₀.2).2 q
  | none, h => nomatch h

theorem valAtO_some (l₀ : (ψ.sig S e).Lbl) (h : (some l₀).map (eraseL e) = some (eraseL e l₀))
    (q : ψ.P (eraseL e l₀).2) : valAtO e (some l₀) (eraseL e l₀) h q = (e l₀.2).2 q := rfl

/-- The value of `t` at a position of its erased tree. -/
def valAt (t : ψ.RawS S e) (pa : List ψ.sig₀.Idx) (l : ψ.sig₀.Lbl)
    (h : (t.get pa).map (eraseL e) = some l) (q : ψ.P l.2) : X (ψ.pidx q) :=
  valAtO e (t.get pa) l h q

theorem valAt_some {t : ψ.RawS S e} {pa : List ψ.sig₀.Idx} {l₀ : (ψ.sig S e).Lbl}
    (ht : t.get pa = some l₀) (h : (t.get pa).map (eraseL e) = some (eraseL e l₀))
    (q : ψ.P (eraseL e l₀).2) : valAt e t pa (eraseL e l₀) h q = (e l₀.2).2 q := by
  unfold valAt
  revert h
  rw [ht]
  intro h
  exact valAtO_some e l₀ h q

/-! ### Reattachment -/

/-- Put values back at the positions of an erased tree. -/
def reattach (sh : ψ.Raw₀) (c : (x : ψ.Pos sh) → X x.idx) : ψ.RawS S e :=
  ⟨fun pa => match hs : sh.get pa with
    | some l => some ⟨l.1, e.symm ⟨l.2, fun q => c ⟨pa, l, ⟨hs⟩, q⟩⟩⟩
    | none => none⟩

theorem get_reattach_some {sh : ψ.Raw₀} (c : (x : ψ.Pos sh) → X x.idx) {pa : List ψ.sig₀.Idx}
    {l : ψ.sig₀.Lbl} (h : sh.get pa = some l) :
    (reattach e sh c).get pa = some ⟨l.1, e.symm ⟨l.2, fun q => c ⟨pa, l, ⟨h⟩, q⟩⟩⟩ := by
  unfold reattach
  dsimp only
  split
  · rename_i l' hs
    rw [h] at hs
    cases hs
    rfl
  · rename_i hs
    rw [h] at hs
    cases hs

theorem get_reattach_none {sh : ψ.Raw₀} (c : (x : ψ.Pos sh) → X x.idx) {pa : List ψ.sig₀.Idx}
    (h : sh.get pa = none) : (reattach e sh c).get pa = none := by
  unfold reattach
  dsimp only
  split
  · rename_i l' hs
    rw [h] at hs
    cases hs
  · rfl

theorem child_reattach {sh : ψ.Raw₀} (c : (x : ψ.Pos sh) → X x.idx) (j : ψ.sig₀.Idx) :
    (reattach e sh c).child j = reattach e (sh.child j) fun x => c (Pos.cons j x) := rfl

/-- Reattaching to equal trees. -/
theorem reattach_cast {sh sh' : ψ.Raw₀} (h : sh = sh') (c : (x : ψ.Pos sh) → X x.idx) :
    reattach e sh c = reattach e sh' fun x => c (Pos.cast h.symm x) := by
  subst h
  rfl

/-- The values of a layer at the positions of its child at `b`, as positions of the layer. -/
def childVals (i : ψ.I) (z : ψ.sig₀.Obj (fun _ => ψ.Raw₀) i)
    (c : (x : ψ.Pos (Signature.encode i z)) → X x.idx) (b : ψ.B i z.shape) :
    (x : ψ.Pos (z.child b)) → X x.idx :=
  fun x => c (Pos.cons ⟨⟨i, z.shape⟩, b⟩
    (Pos.cast (Signature.child_encode_self (σ := ψ.sig₀) i z b).symm x))

/-- The layer of a reattached layer: the values at the root, and the children reattached. -/
def reattachObj (i : ψ.I) (z : ψ.sig₀.Obj (fun _ => ψ.Raw₀) i)
    (c : (x : ψ.Pos (Signature.encode i z)) → X x.idx) :
    (ψ.sig S e).Obj (fun _ => ψ.RawS S e) i :=
  ⟨e.symm ⟨z.shape, fun q => c ⟨[], ⟨i, z.shape⟩, ⟨rfl⟩, q⟩⟩,
    fun b => reattach e (z.child (castP (sh₀_symm e _ _) b))
      (childVals i z c (castP (sh₀_symm e _ _) b))⟩

/-- A reattached layer is the layer with the values at the root and reattached children. -/
theorem reattach_encode (i : ψ.I) (z : ψ.sig₀.Obj (fun _ => ψ.Raw₀) i)
    (c : (x : ψ.Pos (Signature.encode i z)) → X x.idx) :
    reattach e (Signature.encode i z) c = Signature.encode i (reattachObj e i z c) := by
  refine Raw.ext_root_child rfl fun ⟨l, b⟩ => ?_
  rw [child_reattach]
  by_cases h : l = ⟨i, z.shape⟩
  · subst h
    refine (reattach_cast e (Signature.child_encode_self (σ := ψ.sig₀) i z b) _).trans
      (Eq.trans ?_ (child_encode_castP e (reattachObj e i z c) (sh₀_symm e _ _).symm b).symm)
    exact congrArg (fun b₀ : ψ.B i z.shape => reattach e (z.child b₀) (childVals i z c b₀))
      (castP_castP (sh₀_symm e _ _).symm (sh₀_symm e _ _) b).symm
  · have h' : l ≠ ⟨i, (ψ.sig S e).sh₀ (reattachObj e i z c).shape⟩ :=
      fun hl => h (hl.trans (congrArg (Sigma.mk i) (sh₀_symm e _ _)))
    rw [Signature.child_encode_of_ne (σ := ψ.sig S e) i _ h' b,
      reattach_cast e (Signature.child_encode_of_ne (σ := ψ.sig₀) i z h b)]
    exact Raw.ext fun pa => get_reattach_none e _ rfl

theorem isFin_reattach {i : ψ.I} {sh : ψ.Raw₀} (h : Signature.IsFin i sh)
    (c : (x : ψ.Pos sh) → X x.idx) : Signature.IsFin (σ := ψ.sig S e) i (reattach e sh c) := by
  refine Signature.IsFin.induct (σ := ψ.sig₀)
    (fun i sh => ∀ c : (x : ψ.Pos sh) → X x.idx,
      Signature.IsFin (σ := ψ.sig S e) i (reattach e sh c))
    ?_ i sh h c
  rintro i _ ⟨z, rfl, hz⟩ c
  rw [reattach_encode]
  refine (Signature.IsFin.isFix (σ := ψ.sig S e) i _).2 ⟨_, rfl, fun b => ?_⟩
  exact idx_castP e (sh₀_symm e _ _) b ▸
    hz (castP (sh₀_symm e _ _) b) (childVals i z c (castP (sh₀_symm e _ _) b))

theorem isWf_reattach {i : ψ.I} {sh : ψ.Raw₀} (h : Signature.IsWf i sh)
    (c : (x : ψ.Pos sh) → X x.idx) : Signature.IsWf (σ := ψ.sig S e) i (reattach e sh c) := by
  refine Signature.IsWf.coinduct (σ := ψ.sig S e)
    (fun i t => ∃ (sh : ψ.Raw₀) (c : (x : ψ.Pos sh) → X x.idx),
      t = reattach e sh c ∧ Signature.IsWf (σ := ψ.sig₀) i sh)
    ?_ i _ ⟨sh, c, rfl, h⟩
  rintro i _ ⟨sh, c, rfl, hsh⟩
  obtain ⟨z, rfl, hz⟩ := (Signature.IsWf.isFix (σ := ψ.sig₀) i sh).1 hsh
  rw [reattach_encode]
  exact ⟨_, rfl, fun b => ⟨z.child (castP (sh₀_symm e _ _) b),
    childVals i z c (castP (sh₀_symm e _ _) b), rfl,
    idx_castP e (sh₀_symm e _ _) b ▸ hz (castP (sh₀_symm e _ _) b)⟩⟩

/-! ### The layer of a tree, and the two laws -/

/-- The layer of a tree: its erased tree and the values at its positions. -/
def layer (t : ψ.RawS S e) : Σ sh : ψ.Raw₀, (x : ψ.Pos sh) → X x.idx :=
  ⟨erase e t, fun x => valAt e t x.1 x.2.1 x.2.2.1.1 x.2.2.2⟩

theorem reattach_layer (t : ψ.RawS S e) : reattach e (layer e t).1 (layer e t).2 = t := by
  refine Raw.ext fun pa => ?_
  rcases ht : t.get pa with _ | l₀
  · exact get_reattach_none e _ (by simp [layer, ht])
  · rw [get_reattach_some e _ (l := eraseL e l₀) (by simp [layer, ht])]
    simp only [layer, valAt_some e ht]
    change some ⟨l₀.1, e.symm (e l₀.2)⟩ = some l₀
    rw [Equiv.symm_apply_apply]

theorem layer_reattach (sh : ψ.Raw₀) (c : (x : ψ.Pos sh) → X x.idx) :
    layer e (reattach e sh c) = ⟨sh, c⟩ := by
  have h₁ : erase e (reattach e sh c) = sh := by
    refine Raw.ext fun pa => ?_
    rcases hsh : sh.get pa with _ | l
    · simp [get_reattach_none e c hsh]
    · simp [get_reattach_some e c hsh, eraseL]
  refine Sigma.ext h₁ (Function.hfunext (congrArg ψ.Pos h₁) fun x x' hx => ?_)
  obtain rfl : x' = Pos.cast h₁ x := by
    rw [← cast_pos h₁]
    exact (cast_eq_iff_heq.mpr hx).symm
  refine heq_of_eq ?_
  obtain ⟨pa, l, ⟨hp⟩, q⟩ := x
  rcases hsh : sh.get pa with _ | l'
  · exact absurd hp (by simp [layer, get_reattach_none e c hsh])
  · have hl : l = eraseL e ⟨l'.1, e.symm ⟨l'.2, fun q => c ⟨pa, l', ⟨hsh⟩, q⟩⟩⟩ := by
      have := hp
      dsimp only [layer] at this
      rw [get_erase, get_reattach_some e c hsh] at this
      exact (Option.some.inj this).symm
    subst hl
    clear hx
    show valAt e (reattach e sh c) pa _ hp q = c ⟨pa, _, ⟨_⟩, q⟩
    rw [valAt_some e (get_reattach_some e c hsh)]
    have key : ∀ (x : Σ s₀ : ψ.Shape₀ l'.1, (p : ψ.P s₀) → X (ψ.pidx p)),
        x = ⟨l'.2, fun q => c ⟨pa, l', ⟨hsh⟩, q⟩⟩ →
        ∀ (q : ψ.P x.1) (h : sh.get pa = some ⟨l'.1, x.1⟩), x.2 q = c ⟨pa, ⟨l'.1, x.1⟩, ⟨h⟩, q⟩ := by
      rintro x rfl q h
      rfl
    exact key _ (e.apply_symm_apply _) q
      (hsh.trans (congrArg some (Sigma.ext rfl (heq_of_eq (sh₀_symm e _ _).symm))))

end

/-! ### The container instances -/

section

variable (X : ψ.J → Type u') {S : ψ.I → Type u}
  (e : ∀ {i : ψ.I}, S i ≃ Σ s₀ : ψ.Shape₀ i, (p : ψ.P s₀) → X (ψ.pidx p))

/-- The inductive family at `i` is the erased trees with values at their positions. -/
def layerEquivI (i : ψ.I) :
    Signature.Intype (ψ.sig S e) i ≃
      Σ sh : Signature.Intype ψ.sig₀ i, (x : ψ.Pos sh.1) → X x.idx where
  toFun := fun t => ⟨⟨(layer e t.1).1, isFin_erase e t.2⟩, (layer e t.1).2⟩
  invFun := fun z => ⟨reattach e z.1.1 z.2, isFin_reattach e z.1.2 z.2⟩
  left_inv := fun t => Subtype.ext (reattach_layer e t.1)
  right_inv := fun z =>
    Sigma.ext (Subtype.ext (Sigma.mk.inj_iff.mp (layer_reattach e z.1.1 z.2)).1)
      (Sigma.mk.inj_iff.mp (layer_reattach e z.1.1 z.2)).2

/-- The coinductive family at `i` is the erased trees with values at their positions. -/
def layerEquivC (i : ψ.I) :
    Signature.Cotype (ψ.sig S e) i ≃
      Σ sh : Signature.Cotype ψ.sig₀ i, (x : ψ.Pos sh.1) → X x.idx where
  toFun := fun t => ⟨⟨(layer e t.1).1, isWf_erase e t.2⟩, (layer e t.1).2⟩
  invFun := fun z => ⟨reattach e z.1.1 z.2, isWf_reattach e z.1.2 z.2⟩
  left_inv := fun t => Subtype.ext (reattach_layer e t.1)
  right_inv := fun z =>
    Sigma.ext (Subtype.ext (Sigma.mk.inj_iff.mp (layer_reattach e z.1.1 z.2)).1)
      (Sigma.mk.inj_iff.mp (layer_reattach e z.1.1 z.2)).2

end

section

variable (S : (ψ.J → Type u') → ψ.I → Type u)
  (e : ∀ (X : ψ.J → Type u') {i : ψ.I},
    S X i ≃ Σ s₀ : ψ.Shape₀ i, (p : ψ.P s₀) → X (ψ.pidx p))

/-- The inductive family at `i`, as an indexed container in the parameter. -/
def icontainer (i : ψ.I) :
    IContainer (fun X : ψ.J → Type u' => Signature.Intype (ψ.sig (S X) (e X)) i)
      (Signature.Intype ψ.sig₀ i) (fun sh => ψ.Pos sh.1) (fun _ x => x.idx) where
  equiv {X} := layerEquivI X (e X) i

/-- The coinductive family at `i`, as an indexed container in the parameter. -/
def icocontainer (i : ψ.I) :
    IContainer (fun X : ψ.J → Type u' => Signature.Cotype (ψ.sig (S X) (e X)) i)
      (Signature.Cotype ψ.sig₀ i) (fun sh => ψ.Pos sh.1) (fun _ x => x.idx) where
  equiv {X} := layerEquivC X (e X) i

end

section

variable (S : Type u' → ψ.I → Type u)
  (e : ∀ (α : Type u') {i : ψ.I}, S α i ≃ Σ s₀ : ψ.Shape₀ i, ψ.P s₀ → α)

/-- The inductive family at `i`, as a container in a type parameter (the family constant at
the parameter). -/
def container (i : ψ.I) :
    Container (fun α : Type u' => Signature.Intype (ψ.sig (X := fun _ => α) (S α) (e α)) i)
      (Signature.Intype ψ.sig₀ i) (fun sh => ψ.Pos sh.1) where
  equiv {α} := layerEquivI (fun _ => α) (e α) i

/-- The coinductive family at `i`, as a container in a type parameter. -/
def cocontainer (i : ψ.I) :
    Container (fun α : Type u' => Signature.Cotype (ψ.sig (X := fun _ => α) (S α) (e α)) i)
      (Signature.Cotype ψ.sig₀ i) (fun sh => ψ.Pos sh.1) where
  equiv {α} := layerEquivC (fun _ => α) (e α) i

end

end PSignature

end Codata
