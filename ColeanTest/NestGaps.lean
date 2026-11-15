import Colean.MutualCmd

/-! # Test: generated instances in the cases that once had none

Step 5 (`Gen/Derive.lean`) presents a declared type as a polynomial functor in its parameters
that may vary. These are the cases it used to give up on, each with the generated API used
through it: the instances, the `simp` rules of the map and of membership, `fold`, `corec`, and
the recursors' hypotheses by membership.

* a field mentioning several parameters that vary (`p : α × β`): its structure in all of them,
  each at its premise; a parameter is kept constant when the field has no structure in all of
  them together;
* a parameter in the same field as a recursive occurrence (`p : α × T α`, `f : T α ⊕ α`): the
  field is split through its products and sums into parts with one kind of positions each;
* in a block, a nested argument whose positions are at a type of the block only after cases on
  them (`p : A α × B α`, `p : A α × Nat`, `p : A α ⊕ B α`): split in the same way;
* in a family, a nested argument at several indices (`p : T n × T (n + 1)`): split in the same
  way, so that the rules of the map and of membership are by components;
* in a family or a block, a nested argument at one index after cases on its positions (`T n × T n`,
  `A × Nat`): the recursor's hypothesis by `PolyIso.Mem` at that index;
* a leaf applied to an occurrence in an argument that is not its last (`Vec (List T) 2`): the
  structure, and so the recursor's hypothesis, is the instance that instance search finds. -/

universe u v

namespace NestGapsTest

open Codata

noncomputable section

/-! ### Several parameters in one field -/

datatype P2 (α β : Type u)
  | mk (p : α × β)

/-- info: P2.Colean.Poly.instPolyIso -/
#guard_msgs in
#synth PolyIso (fun X : Type => P2 X Nat) _ _

/-- info: P2.Colean.Poly.instPolyIsoEta Nat -/
#guard_msgs in
#synth PolyIso (P2 Nat) _ _

/--
info: @P2.Colean.Poly.map_mk : ∀ {H₁ H₂ : Type u_2 → Type u_1} {H'₁ H'₂ : Type u_3 → Type u_8} {S₁ : Type u_4} {R₁ : S₁ → Type u_5}
  {S₂ : Type u_6} {R₂ : S₂ → Type u_7} [inst₁ : PolyIso H₁ S₁ R₁] [inst₂ : PolyIso H₂ S₂ R₂]
  [inst'₁ : PolyIso H'₁ S₁ R₁] [inst'₂ : PolyIso H'₂ S₂ R₂] {X : Type u_2} {Y : Type u_3} (f : X → Y) (p : H₁ X × H₂ X),
  (Occ.ofIso fun X => P2 (H₁ X) (H₂ X)).map (Occ.ofIso fun X => P2 (H'₁ X) (H'₂ X)) f (P2.mk p) =
    P2.mk (((Occ.ofIso H₁).prod (Occ.ofIso H₂)).map ((Occ.ofIso H'₁).prod (Occ.ofIso H'₂)) f p)
-/
#guard_msgs(whitespace := lax) in
#check @P2.Colean.Poly.map_mk

datatype ThroughP2
  | leaf
  | mk (p : P2 ThroughP2 Nat)

/-- The number of nodes, by the folds of the two types. -/
def ThroughP2.size : ThroughP2 → Nat :=
  ThroughP2.fold (S := Nat) fun
    | .leaf => 1
    | .mk p => P2.fold (S := Nat) (fun | .mk q => q.1 + q.2) p + 1

example : (ThroughP2.mk (.mk (.mk (.mk (.leaf, 2)), 5))).size = 10 := by
  simp [ThroughP2.size]

-- The map through the instance at the two premises, and membership in the first component.
example (f : Nat → Nat) (a b : Nat) :
    (Occ.ofIso fun X => P2 X X).map (Occ.ofIso fun X => P2 X X) f (P2.mk (a, b)) =
      P2.mk (f a, f b) := by
  simp

example (t a : ThroughP2) (n : Nat) :
    PolyIso.Mem (fun X => P2 X Nat) t (P2.mk (a, n)) ↔ t = a := by
  simp

/-- Induction: the hypothesis at the first component. -/
theorem ThroughP2.size_pos (t : ThroughP2) : 0 < t.size := by
  induction t with
  | leaf => simp [ThroughP2.size]
  | mk p ih =>
    simp [ThroughP2.size]

/-! A third parameter in a field of its own, and parameters in different universes. -/

datatype P3 (α β γ : Type u)
  | mk (p : α × β) (c : γ)

datatype ThroughP3
  | leaf
  | mk (x : P3 Nat ThroughP3 ThroughP3)

/-- info: P3.Colean.Poly.instPolyIso -/
#guard_msgs in
#synth PolyIso (fun X : Type => P3 X X Nat) _ _

datatype PU (α : Type u) (β : Type v)
  | mk (p : α × List β)

/-- info: PU.Colean.Poly.instPolyIso -/
#guard_msgs in
#synth PolyIso (fun X : Type => PU X X) _ _

/-! A declared leaf taking two parameters in one field: its instance at both premises. -/

datatype E (α β : Type u)
  | l (a : α)
  | r (b : β)

datatype EP (α β : Type u)
  | mk (e : E α β) (f : E α (List β))

datatype ThroughEP
  | leaf
  | mk (x : EP ThroughEP Nat)

example (t a : ThroughEP) (n : Nat) :
    PolyIso.Mem (fun X => EP X Nat) t (EP.mk (.l a) (.r [n])) ↔ t = a := by
  simp

/-! A parameter that cannot vary with the others in a field is kept constant: `Fn`'s parameter
`A` is a function domain, so `K` varies in `β` only. -/

datatype Fn (A : Type) (α : Type u)
  | leaf (a : α)
  | node (k : A → Fn A α)

datatype K (α β : Type)
  | mk (x : Fn α β)

/-- info: K.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso (K Nat) _ _

/--
error: failed to synthesize
  PolyIso (fun X => K X Nat) ?m.1 ?m.2

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth PolyIso (fun X : Type => K X Nat) _ _

/-! ### A mixed block whose middle run passes an outer type on

`C` mentions `A`, so `B`, between them, passes its parameter `X` for `A` on to `C`: its field
`c : C.Open α X` mentions `α` and `X`. Both vary in `B.Open`; with `α` a function domain in `C`,
only `X` does, which is all the outer run needs. -/

namespace Distant

mixed_mutual
codatatype A (α : Type u)
  | mk (b : B α)
datatype B (α : Type u)
  | nil
  | cons (c : C α) (b : B α)
codatatype C (α : Type u)
  | mk (a : A α) (c : C α)
end

/-- info: B.Open.Colean.Poly.instPolyIso -/
#guard_msgs in
#synth PolyIso (fun X : Type => B.Open X X) _ _

/-- A tree with an empty list of `C`s at each node. -/
def A.leaf {α : Type u} : A α := A.corec (S := Unit) (fun _ => .mk .nil) ()

theorem A.leaf_eq {α : Type u} : (A.leaf : A α) = .mk .nil := by
  conv => lhs; rw [← A.ctor_dtor A.leaf, A.leaf, A.dtor_corec]
  simp

end Distant

namespace DistantDomain

mixed_mutual
codatatype A (α : Type)
  | mk (b : B α)
datatype B (α : Type)
  | nil
  | cons (c : C α) (b : B α)
codatatype C (α : Type)
  | mk (a : α → A α) (c : C α)
end

/-- info: B.Open.Colean.Poly.instPolyIsoEta -/
#guard_msgs in
#synth PolyIso (fun X : Type => B.Open Nat X) _ _

-- `α` is constant: there is no instance in it.
/--
error: failed to synthesize
  PolyIso (fun X => B.Open X Nat) ?m.1 ?m.2

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth PolyIso (fun X : Type => B.Open X Nat) _ _

end DistantDomain

/-! ### A parameter in the same field as a recursive occurrence -/

codatatype PairStr (α : Type u)
  | mk (p : α × PairStr α)

/--
info: @PairStr.Colean.Poly.map_mk : ∀ {H : Type u_2 → Type u_1} {H' : Type u_3 → Type u_6} {S : Type u_4} {R : S → Type u_5}
  [inst : PolyIso H S R] [inst' : PolyIso H' S R] {X : Type u_2} {Y : Type u_3} (f : X → Y) (p : H X × PairStr (H X)),
  (Occ.ofIso fun X => PairStr (H X)).map (Occ.ofIso fun X => PairStr (H' X)) f (PairStr.mk p) =
    PairStr.mk
      ((Occ.ofIso H).map (Occ.ofIso H') f p.fst,
        (Occ.ofIso fun X => PairStr (H X)).map (Occ.ofIso fun X => PairStr (H' X)) f p.snd)
-/
#guard_msgs(whitespace := lax) in
#check @PairStr.Colean.Poly.map_mk

/--
info: @PairStr.Colean.Poly.mem_mk : ∀ {H : Type u_2 → Type u_1} {S : Type u_3} {R : S → Type u_4} [inst : PolyIso H S R]
  {X : Type u_2} (x : X) (p : H X × PairStr (H X)),
  PolyIso.Mem (fun X => PairStr (H X)) x (PairStr.mk p) ↔
    PolyIso.Mem H x p.fst ∨ PolyIso.Mem (fun X => PairStr (H X)) x p.snd
-/
#guard_msgs(whitespace := lax) in
#check @PairStr.Colean.Poly.mem_mk

example (f : Nat → Nat) (a : Nat) (s : PairStr Nat) :
    (Occ.ofIso PairStr).map (Occ.ofIso PairStr) f (PairStr.mk (a, s)) =
      PairStr.mk (f a, (Occ.ofIso PairStr).map (Occ.ofIso PairStr) f s) := by
  simp

datatype ThroughPairStr
  | leaf
  | mk (x : PairStr ThroughPairStr)

/-- The stream `a, a, a, …`, by `corec`. -/
def PairStr.const {α : Type u} (a : α) : PairStr α :=
  PairStr.corec (S := Unit) (fun _ => .mk (a, ())) ()

theorem PairStr.const_eq {α : Type u} (a : α) : PairStr.const a = .mk (a, .const a) := by
  conv => lhs; rw [← PairStr.ctor_dtor (PairStr.const a), PairStr.const, PairStr.dtor_corec]
  simp [PairStr.const]

-- The members of the constant stream, through the instance.
example (t a : ThroughPairStr) : PolyIso.Mem PairStr t (PairStr.const a) ↔
    t = a ∨ PolyIso.Mem PairStr t (PairStr.const a) := by
  conv => lhs; rw [PairStr.const_eq]
  simp

/-! Through a sum: a constructor of the presentation, and a rule, for each side. -/

datatype Tm (α : Type u)
  | var (a : α)
  | app (f : Tm α ⊕ α) (arg : Tm α)

/--
info: @Tm.Colean.Poly.mem_app_inr : ∀ {H : Type u_2 → Type u_1} {S : Type u_3} {R : S → Type u_4} [inst : PolyIso H S R]
  {X : Type u_2} (x : X) (f_inr : H X) (arg : Tm (H X)),
  PolyIso.Mem (fun X => Tm (H X)) x (Tm.app (Sum.inr f_inr) arg) ↔
    PolyIso.Mem H x f_inr ∨ PolyIso.Mem (fun X => Tm (H X)) x arg
-/
#guard_msgs(whitespace := lax) in
#check @Tm.Colean.Poly.mem_app_inr

datatype ThroughTm
  | leaf
  | mk (t : Tm ThroughTm)

def ThroughTm.size : ThroughTm → Nat :=
  ThroughTm.fold (S := Nat) fun
    | .leaf => 1
    | .mk t => Tm.fold (S := Nat)
        (fun | .var a => a | .app (.inl n) m => n + m | .app (.inr a) m => a + m) t + 1

example : (ThroughTm.mk (.app (.inr .leaf) (.var (.mk (.var .leaf))))).size = 4 := by
  simp [ThroughTm.size]

example (t a b : ThroughTm) :
    PolyIso.Mem (fun X => Tm X) t (Tm.app (.inl (.var a)) (.var b)) ↔ t = a ∨ t = b := by
  simp

/-- Induction through `Tm`: the hypothesis at the members of the term, by the rules of each
side of the sum. -/
theorem ThroughTm.ind (P : ThroughTm → Prop) (hl : P .leaf)
    (happ : ∀ a b, P a → P b → P (.mk (.app (.inr a) (.var b))))
    (hother : ∀ t, P (.mk t)) (t : ThroughTm) : P t := by
  induction t with
  | leaf => exact hl
  | mk t ih =>
    cases t with
    | var _ => exact hother _
    | app f arg =>
      cases f with
      | inl _ => exact hother _
      | inr a =>
        cases arg with
        | var b => exact happ a b (ih a (by simp)) (ih b (by simp))
        | app _ _ => exact hother _

/-! Nested parts and a sum inside a product. -/

datatype Mix (α : Type u)
  | leaf (a : α)
  | node (p : (Mix α ⊕ α) × List (Mix α)) (k : Nat → Mix α)

example (x a b : Nat) :
    PolyIso.Mem Mix x (Mix.node (.inr a, [.leaf b]) fun _ => .leaf b) ↔ x = a ∨ x = b := by
  simp

/-! In a family. -/

codatatype VStr (α : Type u) : Nat → Type u
  | mk {n : Nat} (p : α × VStr α n) : VStr α (n + 1)

/-- info: VStr.Colean.Poly.instPolyIso 3 -/
#guard_msgs in
#synth PolyIso (fun X : Type => VStr X 3) _ _

codatatype VL (α : Type u) : Nat → Type u
  | mk {n : Nat} (p : α × List (VL α n)) : VL α (n + 1)

/-- info: VL.Colean.Poly.instPolyIso 3 -/
#guard_msgs in
#synth PolyIso (fun X : Type => VL X 3) _ _

/-! A mixed block with an outer type in a field with the forests themselves. -/

namespace Pair

mixed_mutual
codatatype Tree (α : Type u)
  | node (a : α) (children : Forest α)
datatype Forest (α : Type u)
  | nil
  | cons (p : Tree α × Forest α)
end

/--
info: @Forest.mem_cons : ∀ {α : Type u_1} (p : Tree α × Forest α) (x : Tree α), x ∈ Forest.cons p ↔ x = p.fst ∨ x ∈ p.snd
-/
#guard_msgs in
#check @Forest.mem_cons

/-- The tree with two copies of itself as children. -/
def Tree.bin {α : Type u} (a : α) : Tree α :=
  Tree.corec (S := Unit) (fun _ => .node a (.cons ((), .cons ((), .nil)))) ()

theorem Tree.bin_eq {α : Type u} (a : α) :
    Tree.bin a = .node a (.cons (.bin a, .cons (.bin a, .nil))) := by
  conv => lhs; rw [← Tree.ctor_dtor (Tree.bin a), Tree.bin, Tree.dtor_corec]
  simp [Tree.bin]

example {α : Type u} (s t : Tree α) : t ∈ Forest.cons (s, .cons (t, .nil)) := by simp

/-- The number of trees in a forest, by its recursor. -/
def Forest.size {α : Type u} (f : Forest α) : Nat :=
  Forest.rec (motive := fun _ => Nat) 0 (fun p ih => ih p.2 (by simp) + 1) f

example {α : Type u} (s t : Tree α) : (Forest.cons (s, .cons (t, .nil))).size = 2 := by
  simp [Forest.size]

end Pair

/-! ### A type of a block with a product or a sum in a nested argument -/

mutual
datatype QA (α : Type u)
  | nil
  | mk (a : α) (p : QA α × QB α)
datatype QB (α : Type u)
  | mk (a : α) (q : QA α)
end

/--
info: @QA.Colean.Poly.map_mk : ∀ {H : Type u_2 → Type u_1} {H' : Type u_3 → Type u_6} {S : Type u_4} {R : S → Type u_5}
  [inst : PolyIso H S R] [inst' : PolyIso H' S R] {X : Type u_2} {Y : Type u_3} (f : X → Y) (a : H X)
  (p : QA (H X) × QB (H X)),
  (Occ.ofIso fun X => QA (H X)).map (Occ.ofIso fun X => QA (H' X)) f (QA.mk a p) =
    QA.mk ((Occ.ofIso H).map (Occ.ofIso H') f a)
      ((Occ.ofIso fun X => QA (H X)).map (Occ.ofIso fun X => QA (H' X)) f p.fst,
        (Occ.ofIso fun X => QB (H X)).map (Occ.ofIso fun X => QB (H' X)) f p.snd)
-/
#guard_msgs(whitespace := lax) in
#check @QA.Colean.Poly.map_mk

datatype ThroughQB
  | leaf
  | mk (q : QB ThroughQB)

example (t a b : ThroughQB) :
    PolyIso.Mem QB t (.mk a (.mk b (.nil, .mk a .nil))) ↔ t = a ∨ t = b := by
  simp [or_comm]

/-- The leaves of a `QB` of numbers, by the folds of the block. -/
def QB.sum (q : QB Nat) : Nat :=
  QA_QB.fold (S := fun _ => Nat) (fun _ y => QA_QB.F.casesOn y 0 (fun a p => a + p.1 + p.2)
    (fun a n => a + n)) q

def ThroughQB.size : ThroughQB → Nat :=
  ThroughQB.fold (S := Nat) fun
    | .leaf => 1
    | .mk q => q.sum + 1

example : (ThroughQB.mk (.mk .leaf .nil)).size = 2 := by
  simp [ThroughQB.size, QB.sum]

mutual
datatype SA (α : Type u)
  | nil
  | mk (a : α) (p : SA α ⊕ SB α)
datatype SB (α : Type u)
  | mk (q : SA α)
end

example (x a : Nat) : PolyIso.Mem SA x (.mk a (.inr (.mk .nil))) ↔ x = a := by
  simp

mutual
datatype NA (α : Type u)
  | nil
  | mk (p : List (NA α) × NB α)
datatype NB (α : Type u)
  | mk (a : α) (q : NA α)
end

example (x a b : Nat) :
    PolyIso.Mem NB x (.mk a (.mk ([.nil], .mk b .nil))) ↔ x = a ∨ x = b := by
  simp

/-! ### In a family, the rules by components

A nested argument of a family whose positions are at several indices, or at one only after cases
on them, is split through its products and sums as in a block: the rules of the map and of
membership are then stated with its components, each at the type at its index, rather than
through the indexed structure (`IOcc.map`, `IPolyIso.Mem` at an index). -/

datatype Chain2 (α : Type u) : Nat → Type u
  | leaf {n : Nat} (a : α) : Chain2 α n
  | link {n : Nat} (p : Chain2 α n × Chain2 α (n + 1)) : Chain2 α (n + 2)

/--
info: @Chain2.Colean.Poly.mem_link : ∀ {H : Type u_2 → Type u_1} {S : Type u_3} {R : S → Type u_4} [inst : PolyIso H S R]
  {X : Type u_2} (x : X) {n : Nat} (p : Chain2 (H X) n × Chain2 (H X) (n + 1)),
  PolyIso.Mem (fun X => Chain2 (H X) (n + 2)) x (Chain2.link p) ↔
    PolyIso.Mem (fun X => Chain2 (H X) n) x p.fst ∨ PolyIso.Mem (fun X => Chain2 (H X) (n + 1)) x p.snd
-/
#guard_msgs(whitespace := lax) in
#check @Chain2.Colean.Poly.mem_link

example (f : Nat → Nat) (a b : Nat) :
    (Occ.ofIso fun X => Chain2 X 2).map (Occ.ofIso fun X => Chain2 X 2) f
        (Chain2.link (.leaf a, .leaf b)) = Chain2.link (.leaf (f a), .leaf (f b)) := by
  simp

example (x a b : Nat) :
    PolyIso.Mem (fun X => Chain2 X 2) x (Chain2.link (.leaf a, .leaf b)) ↔ x = a ∨ x = b := by
  simp

/-! ### Positions at one index after cases on them

In a family or a block, when every position of a nested argument is at one index, but through a
product only after cases on the position (`T n × T n`, `T n × Nat`), the recursor's hypothesis is
by `PolyIso.Mem` at that index, as at one index at variables: the hypothesis at the positions is
brought to that index by cases on them. -/

datatype Twin : Nat → Type
  | leaf {n : Nat} : Twin n
  | node {n : Nat} (p : Twin n × Twin n) : Twin (n + 1)

/--
info: @Twin.rec : {motive : (j₁ : Nat) → Twin j₁ → Sort u_1} →
  ({n : Nat} → motive n Twin.leaf) →
    ({n : Nat} →
        (p : Twin n × Twin n) →
          ((t : Twin n) → PolyIso.Mem (fun X => X × X) t p → motive n t) → motive (n + 1) (Twin.node p)) →
      {i₁ : Nat} → (t : Twin i₁) → motive i₁ t
-/
#guard_msgs in
#check @Twin.rec

/-- The number of leaves, by the recursor, whose rule computes it. -/
def Twin.size {n : Nat} : Twin n → Nat :=
  Twin.rec (motive := fun _ _ => Nat) 1 (fun p ih => ih p.1 (by simp) + ih p.2 (by simp))

example : (Twin.node (.leaf, .node (.leaf, .leaf)) : Twin 2).size = 3 := by
  simp [Twin.size]

/-- Induction: `simp` makes the hypothesis one for each component. -/
theorem Twin.ind (P : ∀ n, Twin n → Prop) (hl : ∀ n, P n .leaf)
    (hn : ∀ n (a b : Twin n), P n a → P n b → P (n + 1) (.node (a, b))) (n : Nat) (t : Twin n) :
    P n t := by
  induction t with
  | leaf => exact hl _
  | node p ih =>
    simp at ih
    exact hn _ p.1 p.2 ih.1 ih.2

datatype TwinL : Nat → Type
  | leaf {n : Nat} : TwinL n
  | node {n : Nat} (p : List (TwinL n × TwinL n)) : TwinL (n + 1)

/--
info: @TwinL.rec : {motive : (j₁ : Nat) → TwinL j₁ → Sort u_1} →
  ({n : Nat} → motive n TwinL.leaf) →
    ({n : Nat} →
        (p : List (TwinL n × TwinL n)) →
          ((t : TwinL n) → PolyIso.Mem (fun X => List (X × X)) t p → motive n t) → motive (n + 1) (TwinL.node p)) →
      {i₁ : Nat} → (t : TwinL i₁) → motive i₁ t
-/
#guard_msgs in
#check @TwinL.rec

mutual
datatype BA
  | nil
  | mk (p : BA × Nat)
datatype BB
  | mk (a : BA)
end

/--
info: @BA.rec : {motive_1 : BA → Sort u_1} →
  {motive_2 : BB → Sort u_1} →
    motive_1 BA.nil →
      ((p : BA × Nat) → ((t : BA) → PolyIso.Mem (fun X => X × Nat) t p → motive_1 t) → motive_1 (BA.mk p)) →
        ((a : BA) → motive_1 a → motive_2 (BB.mk a)) → (t : BA) → motive_1 t
-/
#guard_msgs in
#check @BA.rec

/-- The depth, by the recursor of the block. -/
def BA.depth : BA → Nat :=
  BA.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) 0 (fun p ih => ih p.1 (by simp) + 1)
    (fun _ n => n)

example : (BA.mk (.mk (.nil, 1), 2)).depth = 2 := by
  simp [BA.depth]

/-! ### A leaf applied to an occurrence in an argument other than its last

The recursor's hypothesis is stated with the instance that instance search finds for
`fun X => Vec (List X) 2`, `Vec`'s at the premise `List`, so a hypothesis written by hand is the
recursor's. -/

datatype Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (t : Vec α n) : Vec α (n + 1)

datatype VLst
  | leaf
  | node (cs : Vec (List VLst) 2)

theorem VLst.ind (P : VLst → Prop) (hl : P .leaf)
    (hn : ∀ cs, (∀ t, PolyIso.Mem (fun X => Vec (List X) 2) t cs → P t) → P (.node cs))
    (t : VLst) : P t := by
  induction t with
  | leaf => exact hl
  | node cs ih => exact hn cs ih

example (t a b c : VLst) :
    PolyIso.Mem (fun X => Vec (List X) 2) t (.cons [a, b] (.cons [c] .nil)) ↔
      t = a ∨ t = b ∨ t = c := by
  simp [or_assoc]

def VLst.size : VLst → Nat :=
  VLst.fold (S := Nat) fun
    | .leaf => 1
    | .node cs =>
      Vec.fold (S := fun _ => Nat) (fun _ y => Vec.F.casesOn y 0 fun a s => a.sum + s) cs + 1

example : (VLst.node (.cons [.leaf, .leaf] (.cons [.leaf] .nil))).size = 4 := by
  simp [VLst.size]

-- In a family, at the index of the family.
datatype FV : Nat → Type
  | leaf : FV 0
  | node {n : Nat} (cs : Vec (List (FV n)) 2) : FV (n + 1)

theorem FV.ind (P : ∀ n, FV n → Prop) (hl : P 0 .leaf)
    (hn : ∀ n cs, (∀ t, PolyIso.Mem (fun X => Vec (List X) 2) t cs → P n t) → P (n + 1) (.node cs))
    (n : Nat) (t : FV n) : P n t := by
  induction t with
  | leaf => exact hl
  | node cs ih => exact hn _ cs ih

end

end NestGapsTest
