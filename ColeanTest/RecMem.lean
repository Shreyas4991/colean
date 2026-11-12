import Colean.MutualCmd

/-! # Test: induction hypotheses of nested arguments by membership

The recursor states the hypothesis of a nested argument `c` by membership, for the functor of
its type, `∀ t, PolyIso.Mem (fun X => G X) t c → motive t`, and the `simp` lemmas of
`PolyIso.lean` turn it into the container's own membership or into components. Through lists,
options, a product, a declared type, in families at one index or at several, and in a block. -/

universe u

namespace RecMemTest

open Codata

noncomputable section

/-! ### Through `List` -/

data Rose (α : Type u)
  | node (a : α) (cs : List (Rose α))

/--
info: @Rose.rec : {α : Type u_2} →
  {motive : Rose α → Sort u_1} →
    ((a : α) →
        (cs : List (Rose α)) →
          ((t : Rose α) → PolyIso.Mem (fun X => List X) t cs → motive t) → motive (Rose.node a cs)) →
      (t : Rose α) → motive t
-/
#guard_msgs in
#check @Rose.rec

/--
info: @Rose.rec_node : ∀ {α : Type u_1} {motive : Rose α → Sort u_2} (a : α) (cs : List (Rose α))
  (node : (a : α) → (cs : List (Rose α)) → ((t : Rose α) → PolyIso.Mem (fun X => List X) t cs → motive t) → motive (Rose.node a cs)),
  Rose.rec node (Rose.node a cs) = node a cs fun t _ => Rose.rec node t
-/
#guard_msgs(whitespace := lax) in
#check @Rose.rec_node

/-- The number of nodes, by the recursor: the hypothesis applies to the members of the list,
which `List.attach` gives with their proofs. -/
def Rose.size {α : Type u} : Rose α → Nat :=
  Rose.rec (motive := fun _ => Nat) fun _ cs ih =>
    (cs.attach.map fun x => ih x.1 ((PolyIso.mem_list _ _).mpr x.2)).sum + 1

@[simp] theorem Rose.size_node {α : Type u} (a : α) (cs : List (Rose α)) :
    (Rose.node a cs).size = (cs.map Rose.size).sum + 1 := by
  simp [Rose.size, List.map_attach_eq_pmap]

example : (Rose.node 0 [.node 1 [], .node 2 [.node 3 []]]).size = 4 := by simp

/-- The same count by the fold. -/
def Rose.size' {α : Type u} (t : Rose α) : Nat :=
  Rose.fold (S := Nat) (fun | .node _ cs => cs.sum + 1) t

/-- Induction: the hypothesis is used at the members of the list. -/
theorem Rose.size_eq {α : Type u} (t : Rose α) : t.size = t.size' := by
  induction t with
  | node a cs ih =>
    simp only [PolyIso.mem_list] at ih
    rw [Rose.size_node, Rose.size', Rose.fold_node, Occ.map_list]
    exact congrArg (· + 1) (congrArg List.sum (List.map_congr_left ih))

/-! ### Through `Option` -/

data OTree
  | node (n : Nat) (l r : Option OTree)

/--
info: @OTree.rec : {motive : OTree → Sort u_1} →
  ((n : ℕ) →
      (l r : Option OTree) →
        ((t : OTree) → PolyIso.Mem (fun X => Option X) t l → motive t) →
          ((t : OTree) → PolyIso.Mem (fun X => Option X) t r → motive t) → motive (OTree.node n l r)) →
    (t : OTree) → motive t
-/
#guard_msgs in
#check @OTree.rec

/-- The sum of the labels. -/
def OTree.sum : OTree → Nat :=
  OTree.rec (motive := fun _ => Nat) fun n l r ihl ihr =>
    n + (l.attach.map fun x => ihl x.1 ((PolyIso.mem_option _ _).mpr x.2)).getD 0 +
      (r.attach.map fun x => ihr x.1 ((PolyIso.mem_option _ _).mpr x.2)).getD 0

example : (OTree.node 1 (some (.node 2 none none)) none).sum = 3 := by
  simp [OTree.sum]

/-! ### Through a product -/

data Weighted
  | leaf (n : Nat)
  | node (l r : Weighted × Nat)

/--
info: @Weighted.rec : {motive : Weighted → Sort u_1} →
  ((n : ℕ) → motive (Weighted.leaf n)) →
    ((l r : Weighted × ℕ) →
        ((t : Weighted) → PolyIso.Mem (fun X => X × ℕ) t l → motive t) →
          ((t : Weighted) → PolyIso.Mem (fun X => X × ℕ) t r → motive t) → motive (Weighted.node l r)) →
      (t : Weighted) → motive t
-/
#guard_msgs in
#check @Weighted.rec

/-- The membership in a pair is the first component (`mem_prod`, `mem_id`, `not_mem_const`). -/
example (t : Weighted) (l : Weighted × Nat) : PolyIso.Mem (fun X => X × Nat) t l ↔ t = l.1 := by
  simp

/-- The weighted sum of the leaves. -/
def Weighted.total : Weighted → Nat :=
  Weighted.rec (motive := fun _ => Nat) id fun l r ihl ihr =>
    ihl l.1 (by simp) * l.2 + ihr r.1 (by simp) * r.2

example : (Weighted.node (.leaf 2, 3) (.leaf 1, 4)).total = 10 := by
  simp [Weighted.total]

/-- Induction through the product. -/
theorem Weighted.total_le (t : Weighted) (h : ∀ n, 0 < n) : 0 < t.total := by
  induction t with
  | leaf n => simpa [Weighted.total] using h n
  | node l r ihl ihr =>
    have := ihl l.1 (by simp)
    simp only [Weighted.total, Weighted.rec_node] at this ⊢
    exact Nat.add_pos_left (Nat.mul_pos this (h _)) _

/-! ### Through a declared type, with its generated instance -/

data Forest (X : Type u)
  | nil
  | cons (x : X) (rest : Forest X)

data FTree
  | node (n : Nat) (cs : Forest FTree)

/--
info: @FTree.rec : {motive : FTree → Sort u_1} →
  ((n : ℕ) →
      (cs : Forest FTree) →
        ((t : FTree) → PolyIso.Mem (fun X => Forest X) t cs → motive t) → motive (FTree.node n cs)) →
    (t : FTree) → motive t
-/
#guard_msgs in
#check @FTree.rec

/-- The label at the root, by the recursor; its rule computes it. -/
def FTree.root : FTree → Nat := FTree.rec (motive := fun _ => Nat) fun n _ _ => n

example : (FTree.node 3 .nil).root = 3 := by simp [FTree.root]

/-- A property of every member, through the positions of the presentation
(`PolyIso.forall_mem_iff`). -/
example (cs : Forest FTree) (P : FTree → Prop) (h : ∀ t, PolyIso.Mem Forest t cs → P t) (q) :
    P ((PolyIso.equiv cs).2 q) :=
  PolyIso.forall_mem_iff.mp h q

/-! ### In a family, at one index -/

data LT : Nat → Type
  | leaf : LT 0
  | node {n : Nat} (cs : List (LT n)) : LT (n + 1)

/--
info: @LT.rec : {motive : (j₁ : ℕ) → LT j₁ → Sort u_1} →
  motive 0 LT.leaf →
    ({n : ℕ} →
        (cs : List (LT n)) →
          ((t : LT n) → PolyIso.Mem (fun X => List X) t cs → motive n t) → motive (n + 1) (LT.node cs)) →
      {i₁ : ℕ} → (t : LT i₁) → motive i₁ t
-/
#guard_msgs in
#check @LT.rec

/-- The number of leaves. -/
def LT.leaves : {n : Nat} → LT n → Nat :=
  @LT.rec (fun _ _ => Nat) 1 fun cs ih =>
    (cs.attach.map fun x => ih x.1 ((PolyIso.mem_list _ _).mpr x.2)).sum

@[simp] theorem LT.leaves_node {n : Nat} (cs : List (LT n)) :
    (LT.node cs).leaves = (cs.map LT.leaves).sum := by
  simp [LT.leaves, List.map_attach_eq_pmap]

example : (LT.node [LT.leaf, LT.leaf]).leaves = 2 := by simp [LT.leaves]

/-- The same count, with a right fold for the sum. -/
def LT.leaves' : {n : Nat} → LT n → Nat :=
  @LT.rec (fun _ _ => Nat) 1 fun cs ih =>
    (cs.attach.map fun x => ih x.1 ((PolyIso.mem_list _ _).mpr x.2)).foldr (· + ·) 0

@[simp] theorem LT.leaves'_node {n : Nat} (cs : List (LT n)) :
    (LT.node cs).leaves' = (cs.map LT.leaves').foldr (· + ·) 0 := by
  simp [LT.leaves', List.map_attach_eq_pmap]

/-- Induction at one index: the hypothesis is at `n` for every member of the list. -/
theorem LT.leaves_eq {n : Nat} (t : LT n) : t.leaves = t.leaves' := by
  induction t with
  | leaf => simp [LT.leaves, LT.leaves']
  | node cs ih =>
    simp only [PolyIso.mem_list] at ih
    rw [LT.leaves_node, LT.leaves'_node, List.map_congr_left ih]
    rfl

/-! ### In a family, at several indices -/

data Chain : Nat → Type
  | zero : Chain 0
  | link {n : Nat} (p : Chain n × Chain (n + 1)) : Chain (n + 2)

/--
info: @Chain.rec : {motive : (j₁ : ℕ) → Chain j₁ → Sort u_1} →
  motive 0 Chain.zero →
    ({n : ℕ} →
        (p : Chain n × Chain (n + 1)) →
          ((j₁ : ℕ) → (t : Chain j₁) → IPolyIso.Mem (fun X => X n × X (n + 1)) j₁ t p → motive j₁ t) →
            motive (n + 2) (Chain.link p)) →
      {i₁ : ℕ} → (t : Chain i₁) → motive i₁ t
-/
#guard_msgs in
#check @Chain.rec

/-- The number of links: each component of the pair is a member at its index (`mem_prod`,
`mem_hole`). -/
def Chain.size : {n : Nat} → Chain n → Nat :=
  @Chain.rec (fun _ _ => Nat) 0 fun p ih => ih _ p.1 (by simp) + ih _ p.2 (by simp) + 1

example {n : Nat} (p : Chain n × Chain (n + 1)) : (Chain.link p).size = p.1.size + p.2.size + 1 := by
  simp [Chain.size]

/-! ### In a block -/

mutual
data Tm
  | num (n : Nat)
  | add (args : List Tm)
  | bind (b : Bd) (body : Tm)
data Bd
  | mk (val : Option Tm)
end

/--
info: @Tm.rec : {motive_1 : Tm → Sort u_1} →
  {motive_2 : Bd → Sort u_1} →
    ((n : ℕ) → motive_1 (Tm.num n)) →
      ((args : List Tm) → ((t : Tm) → PolyIso.Mem (fun X => List X) t args → motive_1 t) → motive_1 (Tm.add args)) →
        ((b : Bd) → (body : Tm) → motive_2 b → motive_1 body → motive_1 (Tm.bind b body)) →
          ((val : Option Tm) → ((t : Tm) → PolyIso.Mem (fun X => Option X) t val → motive_1 t) → motive_2 (Bd.mk val)) →
            (t : Tm) → motive_1 t
-/
#guard_msgs in
#check @Tm.rec

/-- The number of numerals. -/
def Tm.nums : Tm → Nat :=
  Tm.rec (motive_2 := fun _ => Nat) (fun _ => 1)
    (fun args ih => (args.attach.map fun x => ih x.1 ((PolyIso.mem_list _ _).mpr x.2)).sum)
    (fun _ _ b t => b + t)
    (fun val ih => (val.attach.map fun x => ih x.1 ((PolyIso.mem_option _ _).mpr x.2)).getD 0)

example : (Tm.add [.num 1, .bind (.mk (some (.num 2))) (.num 3)]).nums = 3 := by
  simp [Tm.nums, List.map_attach_eq_pmap]

/-! Across the types of a block, through a product: the positions are at two types, so the
hypothesis is by `IPolyIso.Mem`, one per type of the argument, at its own motive. `simp` does not
see that a member `t : PA` is at `PA_PB.Ix.PA`, since `PA` is a definition, so the memberships
below are given by their position. -/

mutual
data PA
  | nil
  | mk (p : PA × PB)
data PB
  | mk (a : PA)
end

/--
info: @PA.rec : {motive_1 : PA → Sort u_1} →
  {motive_2 : PB → Sort u_1} →
    motive_1 PA.nil →
      ((p : PA × PB) →
          ((t : PA) → IPolyIso.Mem (fun X => X PA_PB.Ix.PA × X PA_PB.Ix.PB) PA_PB.Ix.PA t p → motive_1 t) →
            ((t : PB) → IPolyIso.Mem (fun X => X PA_PB.Ix.PA × X PA_PB.Ix.PB) PA_PB.Ix.PB t p → motive_2 t) →
              motive_1 (PA.mk p)) →
        ((a : PA) → motive_1 a → motive_2 (PB.mk a)) → (t : PA) → motive_1 t
-/
#guard_msgs in
#check @PA.rec

/-- The depth, by the recursors per type. -/
def PA.depth : PA → Nat :=
  PA.rec (motive_2 := fun _ => Nat) 0
    (fun p iha ihb => max (iha p.1 ⟨.inl (), rfl⟩) (ihb p.2 ⟨.inr (), rfl⟩) + 1) (fun _ k => k)

example : (PA.mk (.nil, .mk .nil)).depth = 1 := by simp [PA.depth]

end

end RecMemTest
