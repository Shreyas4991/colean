import Colean.MutualCmd

/-! # Test: fixes to nesting

One section per fix:

1. a parameter next to the type across a sum at one index, in families and blocks
   (`List (α ⊕ T n)`): the map of the family's indexed structure is the plain one at that index
   through the sum too (`IOcc.map_flat_sum`), so the instances are generated;
2. the generated `PolyMap` instances take `PolyMap` instances of the premises, as the instances
   of the built-in forms do: no map between different functors, no nesting through a leaf at a
   premise without `PolyMap`;
3. the recursor's hypothesis through a sum at one index is by `PolyIso.Mem` at that index, as
   through a product (one analysis, `oneIdx`); `simp` computes membership through a sum at any
   value (`PolyIso.mem_sum`);
4. membership through functors on families (`mem_ofI`, `mem_compI`, `mem_reidx`);
5. the parameters of a field that cannot vary together: the fewest are kept constant, the first
   ones first;
6. at most a few constructors of the presentation per constructor: beyond, an argument through
   sums is not split;
7. the internal names of the constructors of the presentation and of the parts do not collide
   with the user's;
8. `Occ.map_array`;
9. the messages of step 5: a short reason, and a message when no parameter may vary;
10. the eta `PolyMap` across universes for a parameter in `Type (u + 1)`;
11. no disjunct for the members in the parameter of a field without it, and generated binders
    unlike the arguments;
12. `simp` takes the index and the member of a hypothesis or a rule by `IPolyIso.Mem` away at
    the holes, also through a list of pairs at one index (`List (T n × T n)`);
13. nesting through a type at one universe (`NDet : Type → Type`) fixes the universe of the
    occurrences: the layer's variable is at it, and so are the states of the fixpoint, so the
    instances are generated (`stepLevels`). -/

universe u v

namespace NestFixTest

open Codata

noncomputable section

/-! ### 1. A parameter next to the type across a sum at one index -/

datatype FL (α : Type u) : Nat → Type u
  | z : FL α 0
  | s {n : Nat} (p : List (α ⊕ FL α n)) : FL α (n + 1)

/-- info: FL.Colean.Poly.instPolyIso 2 -/
#guard_msgs in
#synth PolyIso (fun X : Type => FL X 2) _ _

example (f : Nat → Int) (a : Nat) :
    (Occ.ofIso fun X => FL X 1).map (Occ.ofIso fun X => FL X 1) f (.s [.inl a, .inr .z]) =
      .s [.inl (f a), .inr .z] := by
  simp

example (x a : Nat) (t : FL Nat 0) :
    PolyIso.Mem (fun X => FL X 1) x (.s [.inl a, .inr t]) ↔
      x = a ∨ PolyIso.Mem (fun X => FL X 0) x t := by
  simp

-- A product inside the sum, and a function into it.
datatype FLP (α : Type u) : Nat → Type u
  | z : FLP α 0
  | s {n : Nat} (p : List (α × FLP α n ⊕ Nat)) : FLP α (n + 1)

/-- info: FLP.Colean.Poly.instPolyIso 1 -/
#guard_msgs in
#synth PolyIso (fun X : Type => FLP X 1) _ _

codatatype CFS (α : Type u) : Nat → Type u
  | mk {n : Nat} (p : Nat → (α ⊕ CFS α n)) : CFS α (n + 1)

/-- info: CFS.Colean.Poly.instPolyIso 1 -/
#guard_msgs in
#synth PolyIso (fun X : Type => CFS X 1) _ _

-- In a block.
mutual
datatype SA (α : Type u)
  | nil
  | mk (p : List (α ⊕ SA α))
datatype SB (α : Type u)
  | mk (a : SA α)
end

/-- info: SA.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso SA.{0} _ _

example (x : Nat) (p : List (Nat ⊕ SA Nat)) :
    PolyIso.Mem SA x (.mk p) ↔ Sum.inl x ∈ p ∨ ∃ t, Sum.inr t ∈ p ∧ PolyIso.Mem SA x t := by
  simp

/-! ### 2. `PolyMap` premises -/

structure NoMap (X : Type u) where
  val : X

instance : PolyIso NoMap.{u} Unit (fun _ => Unit) where
  equiv := ⟨fun b => ⟨(), fun _ => b.val⟩, fun z => ⟨z.2 ()⟩, fun _ => rfl, fun _ => rfl⟩

datatype E (α β : Type u)
  | l (a : α)
  | r (b : β)

/--
error: no `Codata.PolyMap` instance for `NoMap`: the `Codata.PolyIso` instance needs the intended action on functions, and its naturality
-/
#guard_msgs in
datatype W0
  | mk (x : NoMap W0)

-- Through `E`'s instance at the premise `NoMap`, which has no `PolyMap`: refused as well.
/--
error: no `Codata.PolyMap` instance for `NoMap`: the `Codata.PolyIso` instance needs the intended action on functions, and its naturality
-/
#guard_msgs in
datatype W1
  | leaf
  | mk (x : E (NoMap W1) Nat)

-- No map between `E` at two premises with the same shapes.
/--
error: failed to synthesize
  PolyMap (fun X => E (List X) ℕ) fun X => E (Array X) ℕ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth PolyMap (fun X : Type => E (List X) Nat) (fun X : Type => E (Array X) Nat)

/-- info: E.Colean.Poly.instPolyMap -/
#guard_msgs in
#synth PolyMap (fun X : Type => E (List X) Nat) (fun X : Type => E (List X) Nat)

/-! ### 3. The recursor's hypothesis through a sum at one index -/

datatype FS (α : Type) : Nat → Type
  | z : FS α 0
  | s {n : Nat} (p : FS α n ⊕ FS α n) : FS α (n + 1)

/--
info: @FS.rec : {α : Type} →
  {motive : (j₁ : ℕ) → FS α j₁ → Sort u_1} →
    motive 0 FS.z →
      ({n : ℕ} →
          (p : FS α n ⊕ FS α n) →
            ((t : FS α n) → PolyIso.Mem (fun X => X ⊕ X) t p → motive n t) → motive (n + 1) (FS.s p)) →
        {i₁ : ℕ} → (t : FS α i₁) → motive i₁ t
-/
#guard_msgs in
#check @FS.rec

/-- The depth, by the recursor: the hypothesis on the side the value is on. -/
def FS.depth {α : Type} : ∀ {n}, FS α n → Nat := fun t =>
  FS.rec (motive := fun _ _ => Nat) 0
    (fun p ih => match p with
      | .inl a => ih a (by simp) + 1
      | .inr a => ih a (by simp) + 1) t

example : (FS.s (.inr FS.z) : FS Nat 1).depth = 1 := by
  simp [FS.depth]

-- Through a product and through a dependent pair, the sum reached by cases on the value.
datatype FS₂ (α : Type) : Nat → Type
  | z : FS₂ α 0
  | s {n : Nat} (p : (FS₂ α n ⊕ FS₂ α n) × Nat) : FS₂ α (n + 1)

example {α : Type} (P : ∀ n, FS₂ α n → Prop) (h0 : P 0 .z)
    (hs : ∀ n (p : (FS₂ α n ⊕ FS₂ α n) × Nat),
      (∀ t, PolyIso.Mem (fun X => (X ⊕ X) × Nat) t p → P n t) → P (n + 1) (.s p))
    {n : Nat} (t : FS₂ α n) : P n t := by
  induction t with
  | z => exact h0
  | s p ih => exact hs _ p ih

datatype FS₃ (α : Type) : Nat → Type
  | z : FS₃ α 0
  | s {n : Nat} (p : (k : Nat) × (FS₃ α n ⊕ (Fin k → FS₃ α n))) : FS₃ α (n + 1)

example {α : Type} (P : ∀ n, FS₃ α n → Prop) (h0 : P 0 .z)
    (hs : ∀ n (p : (k : Nat) × (FS₃ α n ⊕ (Fin k → FS₃ α n))),
      (∀ t, PolyIso.Mem (fun X => (k : Nat) × (X ⊕ (Fin k → X))) t p → P n t) → P (n + 1) (.s p))
    {n : Nat} (t : FS₃ α n) : P n t := by
  induction t with
  | z => exact h0
  | s p ih => exact hs _ p ih

-- Under a list the sum is not reached by cases on the value: by `IPolyIso.Mem`, which `simp`
-- computes through the sum at any value, the index and the member taken away at the holes
-- (`IPolyIso.forall_mem_compC`, `IPolyIso.forall_mem_sum`).
datatype FS₄ (α : Type) : Nat → Type
  | z : FS₄ α 0
  | s {n : Nat} (p : List (FS₄ α n ⊕ FS₄ α n)) : FS₄ α (n + 1)

example {α : Type} (P : ∀ n, FS₄ α n → Prop) (h0 : P 0 .z)
    (hs : ∀ n (p : List (FS₄ α n ⊕ FS₄ α n)),
      (∀ t, Sum.inl t ∈ p → P n t) → (∀ t, Sum.inr t ∈ p → P n t) → P (n + 1) (.s p))
    {n : Nat} (t : FS₄ α n) : P n t := by
  induction t with
  | z => exact h0
  | @s n p ih =>
    simp at ih
    guard_hyp ih :ₛ (∀ a, Sum.inl a ∈ p → P n a) ∧ ∀ b, Sum.inr b ∈ p → P n b
    exact hs _ p ih.1 ih.2

-- The rules of step 5 for a nested argument at one index only after cases on its positions,
-- under a list: by `IPolyIso.Mem`.
datatype FP (α : Type u) : Nat → Type u
  | z : FP α 0
  | s {n : Nat} (a : α) (p : List (FP α n × FP α n)) : FP α (n + 1)

/--
info: @FP.Colean.Poly.mem_s : ∀ {H : Type u_2 → Type u_1} {S : Type u_3} {R : S → Type u_4} [inst : PolyIso H S R] {X : Type u_2}
  (x : X) {n : ℕ} (a : H X) (p : List (FP (H X) n × FP (H X) n)),
  PolyIso.Mem (fun X => FP (H X) (n + 1)) x (FP.s a p) ↔
    PolyIso.Mem H x a ∨ ∃ p₀ t, IPolyIso.Mem (fun X => List (X n × X n)) p₀ t p ∧ PolyIso.Mem (fun X => FP (H X) p₀) x t
-/
#guard_msgs(whitespace := lax) in
#check @FP.Colean.Poly.mem_s

-- Without indices.
datatype PS
  | leaf
  | mk (p : PS ⊕ Nat)

theorem PS.ind (P : PS → Prop) (h0 : P .leaf) (hm : ∀ p, (∀ t, p = .inl t → P t) → P (.mk p))
    (t : PS) : P t := by
  induction t with
  | leaf => exact h0
  | mk p ih =>
    simp at ih
    exact hm p ih

/-! ### 4. Membership through functors on families -/

structure Both (X : Bool → Type u) where
  yes : X true
  no : X false

instance : IPolyIso Both.{u} Unit (fun _ => Bool) (fun _ b => b) where
  equiv :=
    { toFun := fun t => ⟨(), fun b => match b with | true => t.yes | false => t.no⟩
      invFun := fun z => ⟨z.2 true, z.2 false⟩
      left_inv := fun _ => rfl
      right_inv := fun ⟨_, c⟩ => congrArg (Sigma.mk ()) (funext fun b => by cases b <;> rfl) }

instance : IPolyMap Both.{u} Both.{v} where
  map f t := ⟨f _ t.yes, f _ t.no⟩
  equiv_map f t := congrArg (Sigma.mk ()) (funext fun b => by cases b <;> rfl)

/-- The members of `Both`, which a user of the functor states once. -/
@[simp] theorem Both.mem {X : Bool → Type u} (j : Bool) (x : X j) (c : Both X) :
    IPolyIso.Mem Both j x c ↔
      (⟨true, c.yes⟩ : Σ b, X b) = ⟨j, x⟩ ∨ (⟨false, c.no⟩ : Σ b, X b) = ⟨j, x⟩ := by
  constructor
  · rintro ⟨b, e⟩
    cases b
    · exact .inr e
    · exact .inl e
  · rintro (e | e)
    · exact ⟨true, e⟩
    · exact ⟨false, e⟩

-- Reindexed: `IPolyIso.mem_reidx`.
datatype FlipD : Bool → Type
  | leaf {b : Bool} : FlipD b
  | mk {b : Bool} (children : Both (fun c => FlipD (!c))) : FlipD b

theorem FlipD.ind (P : ∀ b, FlipD b → Prop) (h0 : ∀ b, P b .leaf)
    (hm : ∀ b (c : Both fun c => FlipD (!c)), P false c.yes → P true c.no → P b (.mk c))
    {b : Bool} (t : FlipD b) : P b t := by
  induction t with
  | leaf => exact h0 _
  | mk c ih =>
    simp at ih
    exact hm _ c ih.1 ih.2

-- At a constant family: `PolyIso.mem_ofI`.
datatype AltPlain
  | leaf
  | mk (children : Both (fun _ => AltPlain))

theorem AltPlain.ind (P : AltPlain → Prop) (h0 : P .leaf)
    (hm : ∀ c : Both (fun _ => AltPlain), P c.yes → P c.no → P (.mk c)) (t : AltPlain) : P t := by
  induction t with
  | leaf => exact h0
  | mk c ih =>
    simp at ih
    exact hm c (ih _ (.inr rfl)) (ih _ (.inl rfl))

-- At a family of plain functors: `PolyIso.mem_compI`.
datatype AltIn
  | leaf
  | mk (children : Both (fun _ => List AltIn))

theorem AltIn.ind (P : AltIn → Prop) (h0 : P .leaf)
    (hm : ∀ c : Both (fun _ => List AltIn), (∀ t ∈ c.yes, P t) → (∀ t ∈ c.no, P t) → P (.mk c))
    (t : AltIn) : P t := by
  induction t with
  | leaf => exact h0
  | mk c ih =>
    simp at ih
    exact hm c (fun t h => ih t (.inr h)) (fun t h => ih t (.inl h))

-- At a family of functors on families: `IPolyIso.mem_compI`.
datatype AltInF : Bool → Type
  | leaf {b : Bool} : AltInF b
  | mk {b : Bool} (children : Both (fun c => List (AltInF c))) : AltInF b

theorem AltInF.ind (P : ∀ b, AltInF b → Prop) (h0 : ∀ b, P b .leaf)
    (hm : ∀ b (c : Both fun c => List (AltInF c)), (∀ t ∈ c.yes, P true t) →
      (∀ t ∈ c.no, P false t) → P b (.mk c))
    {b : Bool} (t : AltInF b) : P b t := by
  induction t with
  | leaf => exact h0 _
  | mk c ih =>
    simp at ih
    exact hm _ c ih.2 ih.1

/-! ### 5. Parameters that cannot vary together -/

-- `α` and `β` are domains: kept constant, `γ` varies.
datatype FnFn (α β γ : Type)
  | mk (x : α → β → γ)

/-- info: FnFn.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso (FnFn Nat Nat) _ _

datatype Fn (A : Type) (α : Type)
  | leaf (a : α)
  | node (k : A → Fn A α)

-- `β` is a domain of `Fn`: kept constant, the first `α` varies.
datatype FnRev (α β : Type)
  | mk (x : Fn β α)

/-- info: FnRev.Colean.Poly.instPolyIso -/
#guard_msgs in
#synth PolyIso (fun X : Type => FnRev X Nat) _ _

/-! ### 6. Many sums in one constructor -/

datatype Many (α : Type u)
  | nil
  | cons (a : α) (t : Many α)

-- Thirty-two ways through the sums: the argument is not split, it has a structure in two
-- variables.
datatype Big (α : Type u)
  | leaf
  | mk (p : (Many α ⊕ α) × (Big α ⊕ α) × (Big α ⊕ α) × (Big α ⊕ α) × (Big α ⊕ α))

/-- info: Big.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso Big.{0} _ _

example (x : Nat) (b : Big Nat) :
    PolyIso.Mem Big x (.mk (.inr x, .inl b, .inr 1, .inr 2, .inr 3)) := by
  simp

/-! ### 7. Internal names unlike the user's -/

-- A constructor named as a side of a sum of another.
datatype Tm (α : Type u)
  | var (a : α)
  | app (f : Tm α ⊕ α)
  | app_inl (x : α)

/-- info: Tm.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso Tm.{0} _ _

example (x : Nat) : PolyIso.Mem Tm x (.app (.inr x)) := by simp
example (x : Nat) : PolyIso.Mem Tm x (.app_inl x) := by simp

-- An argument named as a part of another.
datatype PF (α : Type u)
  | leaf
  | mk (p : α × PF α) (p_fst : Nat)

/-- info: PF.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso PF.{0} _ _

/-! ### 8. Arrays -/

datatype OT (α : Type u)
  | mk (o : Option α) (a : Array (OT α))

example (f : Nat → Int) (t : OT Nat) :
    (Occ.ofIso OT).map (Occ.ofIso OT) f (.mk (some 1) #[t]) =
      .mk (some (f 1)) #[(Occ.ofIso OT).map (Occ.ofIso OT) f t] := by
  simp

/-! ### 9. Messages

Step 5 is silent by default; under `set_option codata.deriveDetails true` it reports why a type
gets no instances, with the error itself. -/

#guard_msgs in
datatype UseNoMapQuiet (α : Type)
  | mk (b : NoMap α)

/--
info: `UseNoMap` gets no `Codata.PolyIso` instance, and cannot be nested through: no parameter may vary (`α` occurs in the field `b` of `mk`, without an occurrence structure in it)
-/
#guard_msgs in
set_option codata.deriveDetails true in
datatype UseNoMap (α : Type)
  | mk (b : NoMap α)

namespace Quiet

def Bad.Colean.Poly.fix : Nat := 0

#guard_msgs in
datatype Bad (α : Type)
  | nil
  | cons (a : α) (t : Bad α)

end Quiet

namespace Details

def Bad.Colean.Poly.fix : Nat := 0

/--
warning: `Bad` cannot be nested through: no `Codata.PolyIso` instance was generated. The type itself is not affected.
generating the fixpoint `NestFixTest.Details.Bad.Colean.Poly.fix` failed:
(kernel) constant has already been declared 'NestFixTest.Details.Bad.Colean.Poly.fix'
-/
#guard_msgs in
set_option codata.deriveDetails true in
datatype Bad (α : Type)
  | nil
  | cons (a : α) (t : Bad α)

end Details

/-! ### 10. The eta `PolyMap` across universes -/

datatype BigH (α : Type (u + 1))
  | nil
  | cons (a : α) (t : BigH α)

/-- info: BigH.Colean.Poly.instPolyMapEta -/
#guard_msgs in
#synth PolyMap BigH.{0} BigH.{1}

/-! ### 11. Readable rules -/

-- A field with the block's type but no parameter: no disjunct for its members in the parameter.
mutual
codatatype CA (α : Type u)
  | mk (a : α) (p : List (CA α × Nat))
codatatype CB (α : Type u)
  | mk (a : CA α)
end

/--
info: @CA.Colean.Poly.mem_mk : ∀ {H : Type u_2 → Type u_1} {S : Type u_3} {R : S → Type u_4} [inst : PolyIso H S R] {X : Type u_2}
  (x : X) (a : H X) (p : List (CA (H X) × ℕ)),
  PolyIso.Mem (fun X => CA (H X)) x (CA.mk a p) ↔
    PolyIso.Mem H x a ∨ ∃ t, PolyIso.Mem (fun X => List (X × ℕ)) t p ∧ PolyIso.Mem (fun X => CA (H X)) x t
-/
#guard_msgs(whitespace := lax) in
#check @CA.Colean.Poly.mem_mk

-- Arguments named as the generated binders.
datatype HX (α : Type u)
  | leaf
  | mk (H : α) (X : List (HX α)) (t : Nat)

/--
info: @HX.Colean.Poly.mem_mk : ∀ {H₀ : Type u_2 → Type u_1} {S : Type u_3} {R : S → Type u_4} [inst : PolyIso H₀ S R] {X₀ : Type u_2}
  (x : X₀) (H : H₀ X₀) (X : List (HX (H₀ X₀))) (t : ℕ),
  PolyIso.Mem (fun X => HX (H₀ X)) x (HX.mk H X t) ↔
    PolyIso.Mem H₀ x H ∨ ∃ t₀, PolyIso.Mem (fun X => List X) t₀ X ∧ PolyIso.Mem (fun X => HX (H₀ X)) x t₀
-/
#guard_msgs(whitespace := lax) in
#check @HX.Colean.Poly.mem_mk

/-! ### 12. Quantifiers over the members at several indices

`simp` takes the index and the member of a hypothesis or a rule by `IPolyIso.Mem` away at the
holes, inside a named type constructor too (`IPolyIso.forall_mem_compC`, `exists_mem_compC`, …,
then `IPolyIso.forall_eq_heq_imp`, `exists_eq_heq_and`, …). -/

-- The recursor's hypothesis through a list of pairs at two indices.
datatype FQ (α : Type u) : Nat → Type u
  | z {n : Nat} (a : α) : FQ α n
  | s {n : Nat} (p : List (FQ α n × FQ α (n + 1))) : FQ α (n + 2)

theorem FQ.ind {α : Type u} (P : ∀ n, FQ α n → Prop) (h0 : ∀ n a, P n (.z a))
    (hs : ∀ n (p : List (FQ α n × FQ α (n + 1))), (∀ s t, (s, t) ∈ p → P n s ∧ P (n + 1) t) →
      P (n + 2) (.s p))
    {n : Nat} (t : FQ α n) : P n t := by
  induction t with
  | z a => exact h0 _ a
  | @s n p ih =>
    simp at ih
    guard_hyp ih :ₛ ∀ (s : FQ α n) (t : FQ α (n + 1)), (s, t) ∈ p → P n s ∧ P (n + 1) t
    exact hs n p ih

example (x : Nat) {n : Nat} (p : List (FQ Nat n × FQ Nat (n + 1))) :
    PolyIso.Mem (fun X => FQ X (n + 2)) x (.s p) ↔
      ∃ s t, (s, t) ∈ p ∧
        (PolyIso.Mem (fun X => FQ X n) x s ∨ PolyIso.Mem (fun X => FQ X (n + 1)) x t) := by
  simp

-- The rule of membership through a list of pairs at one index (`FP` above).
example (x : Nat) {n : Nat} (a : Nat) (p : List (FP Nat n × FP Nat n)) :
    PolyIso.Mem (fun X => FP X (n + 1)) x (.s a p) ↔
      x = a ∨ ∃ s t, (s, t) ∈ p ∧
        (PolyIso.Mem (fun X => FP X n) x s ∨ PolyIso.Mem (fun X => FP X n) x t) := by
  simp

-- Through a dependent pair, a sum and a function (`FS₃` above).
example (x : Nat) {n : Nat} (p : (k : Nat) × (FS₃ Nat n ⊕ (Fin k → FS₃ Nat n))) :
    PolyIso.Mem (fun X => FS₃ X (n + 1)) x (.s p) ↔
      (∃ a, p.2 = .inl a ∧ PolyIso.Mem (fun X => FS₃ X n) x a) ∨
        ∃ b, p.2 = .inr b ∧ ∃ i, PolyIso.Mem (fun X => FS₃ X n) x (b i) := by
  simp

-- Through a sum under a list (`FS₄` above).
example (x : Nat) {n : Nat} (p : List (FS₄ Nat n ⊕ FS₄ Nat n)) :
    PolyIso.Mem (fun X => FS₄ X (n + 1)) x (.s p) ↔
      (∃ a, Sum.inl a ∈ p ∧ PolyIso.Mem (fun X => FS₄ X n) x a) ∨
        ∃ b, Sum.inr b ∈ p ∧ PolyIso.Mem (fun X => FS₄ X n) x b := by
  simp

-- Some member of a functor on families with a lemma of its own (`Both.mem`), and at holes
-- directly.
example {X : Bool → Type} (P : ∀ b, X b → Prop) (c : Both X) :
    (∃ j t, IPolyIso.Mem Both j t c ∧ P j t) ↔ P false c.no ∨ P true c.yes := by
  simp

example {X : Nat → Type} (P Q : ∀ n, X n → Prop) {i k : Nat} (c : X i) (d : X k) (l : List (X i)) :
    ((∃ j t, (i = j ∧ HEq c t) ∧ P j t) ↔ P i c) ∧
      ((∃ j t, ((i = j ∧ HEq c t) ∨ (k = j ∧ HEq d t)) ∧ P j t) ↔ P i c ∨ P k d) ∧
      ((∃ j t, (Q j t ∨ (i = j ∧ HEq c t)) ∧ P j t) ↔ (∃ j t, Q j t ∧ P j t) ∨ P i c) ∧
      ((∃ j t, (∃ y, y ∈ l ∧ i = j ∧ HEq y t) ∧ P j t) ↔ ∃ y ∈ l, P i y) := by
  simp

end

/-! ### 13. Nesting through a type at one universe

`NDet (Game α)` with `NDet : Type → Type` puts the occurrences of `Game` in `Type`: `Game.F`
takes its variable there, and so do the layer of the instances and the states of their fixpoint,
so the instances of `Game` are generated, in `Type`, and types nest through it in turn. The same
for `datatype` and through a type of either kind. -/

namespace FixedUniverse

codatatype NDet (α : Type)
  | ret (a : α)
  | choose (next : List (NDet α))

#guard_msgs in
codatatype Game (α : Type)
  | move (label : α) (options : NDet (Game α))

/-- info: Game.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso Game _ _

/--
info: @Game.Colean.Poly.instPolyIso : {H : Type → Type} →
  {S : Type} →
    {R : S → Type} →
      [inst : PolyIso H S R] →
        PolyIso (fun X => Game (H X)) ((shapeSig (Game.Colean.Poly.B S R)).Cotype ())
          (Path (Game.Colean.Poly.P S R) (coTree (Game.Colean.Poly.B S R)))
-/
#guard_msgs in
#check @Game.Colean.Poly.instPolyIso

example (f : Nat → Int) (a : Nat) (o : NDet (Game Nat)) :
    (Occ.ofIso Game).map (Occ.ofIso Game) f (.move a o) =
      .move (f a)
        ((Occ.ofIso NDet).map (Occ.ofIso NDet) ((Occ.ofIso Game).map (Occ.ofIso Game) f) o) := by
  simp

example (x a : Nat) (o : NDet (Game Nat)) :
    PolyIso.Mem Game x (.move a o) ↔ x = a ∨ ∃ t, PolyIso.Mem NDet t o ∧ PolyIso.Mem Game x t := by
  simp

-- A third type nests through `Game`.
#guard_msgs in
codatatype Arena (α : Type)
  | node (a : α) (g : Game (Arena α))

/-- info: Arena.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso Arena _ _

example {X Y : Type} (f : X → Y) (a : Nat) (g : Game X) :
    Arena.F.fmap f (.node a g) = .node a ((Occ.ofIso Game).map (Occ.ofIso Game) f g) := by
  simp

-- `datatype` through `datatype`.
datatype MyList (α : Type)
  | nil
  | cons (a : α) (t : MyList α)

#guard_msgs in
datatype Rose2 (α : Type)
  | node (a : α) (kids : MyList (Rose2 α))

/-- info: Rose2.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso Rose2 _ _

example (f : Nat → Int) (a : Nat) (k : MyList (Rose2 Nat)) :
    (Occ.ofIso Rose2).map (Occ.ofIso Rose2) f (.node a k) =
      .node (f a)
        ((Occ.ofIso MyList).map (Occ.ofIso MyList) ((Occ.ofIso Rose2).map (Occ.ofIso Rose2) f) k)
      := by
  simp

-- `codatatype` through `codatatype`.
codatatype CoList (α : Type)
  | nil
  | cons (a : α) (t : CoList α)

#guard_msgs in
codatatype CoRose (α : Type)
  | node (a : α) (kids : CoList (CoRose α))

/-- info: CoRose.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso CoRose _ _

example (f : Nat → Int) (a : Nat) (k : CoList (CoRose Nat)) :
    (Occ.ofIso CoRose).map (Occ.ofIso CoRose) f (.node a k) =
      .node (f a)
        ((Occ.ofIso CoList).map (Occ.ofIso CoList) ((Occ.ofIso CoRose).map (Occ.ofIso CoRose) f) k)
      := by
  simp

-- Above `Type`, `codatatype` gets its instances; `datatype` needs its trees of shapes at that
-- universe, here in `Type`.
codatatype NDetU (α : Type u)
  | ret (a : α)
  | choose (next : List (NDetU α))

#guard_msgs in
codatatype GameU (α : Type u)
  | move (label : α) (options : NDetU.{u} (GameU α))

/--
warning: `DGameU` cannot be nested through: no `Codata.PolyIso` instance was generated. The type itself is not affected.
a field fixes the universe of the occurrences at `Type u`, and the fixpoint needs `fold` on states in `Type`, its trees of shapes
-/
#guard_msgs in
set_option codata.deriveDetails true in
datatype DGameU (α : Type u)
  | move (label : α) (options : NDetU.{u} (DGameU α))

end FixedUniverse

end NestFixTest
