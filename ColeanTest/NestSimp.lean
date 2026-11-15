import Colean.MutualCmd

/-! # Test: `simp` through the instances of declared types

A type declared with `datatype` or `codatatype` gets, with its instances, `simp` lemmas for the map
and for membership on each constructor (`T.Colean.Poly.map_c`, `T.Colean.Poly.mem_c`). So another
type's rules, which go through the map of the instance, compute on constructors, and the induction
hypotheses of its recursor, by membership, become hypotheses on the arguments. -/

universe u

namespace NestSimpTest

open Codata

noncomputable section

/-! ### Trees with a forest of children -/

datatype Forest (X : Type u)
  | nil
  | cons (t : X) (f : Forest X)

datatype Tree
  | node (n : Nat) (cs : Forest Tree)

/--
info: @Forest.Colean.Poly.map_cons : ∀ {H : Type u_2 → Type u_1} {H' : Type u_3 → Type u_6} {S : Type u_4} {R : S → Type u_5}
  [inst : PolyIso H S R] [inst' : PolyIso H' S R] {X : Type u_2} {Y : Type u_3} (g : X → Y) (t : H X)
  (f : Forest (H X)),
  (Occ.ofIso fun X => Forest (H X)).map (Occ.ofIso fun X => Forest (H' X)) g (Forest.cons t f) =
    Forest.cons ((Occ.ofIso H).map (Occ.ofIso H') g t)
      ((Occ.ofIso fun X => Forest (H X)).map (Occ.ofIso fun X => Forest (H' X)) g f)
-/
#guard_msgs(whitespace := lax) in
#check @Forest.Colean.Poly.map_cons

/--
info: @Forest.Colean.Poly.mem_cons : ∀ {H : Type u_2 → Type u_1} {S : Type u_3} {R : S → Type u_4} [inst : PolyIso H S R]
  {X : Type u_2} (x : X) (t : H X) (f : Forest (H X)),
  PolyIso.Mem (fun X => Forest (H X)) x (Forest.cons t f) ↔ PolyIso.Mem H x t ∨ PolyIso.Mem (fun X => Forest (H X)) x f
-/
#guard_msgs(whitespace := lax) in
#check @Forest.Colean.Poly.mem_cons

/-- The sum of a forest of numbers. -/
def Forest.sum : Forest Nat → Nat :=
  Forest.fold (S := Nat) fun | .nil => 0 | .cons a b => a + b

/-- The number of nodes, by the folds of the two types. -/
def Tree.size : Tree → Nat :=
  Tree.fold (S := Nat) fun | .node _ cs => cs.sum + 1

-- `fold_node` maps the children through `Forest`'s instance; `map_cons`, `map_nil` push it in.
example : (Tree.node 0 (.cons (.node 1 .nil) (.cons (.node 2 .nil) .nil))).size = 3 := by
  simp [Tree.size, Forest.sum]

example (t : Tree) (a b : Tree) :
    PolyIso.Mem (fun X => Forest X) t (.cons a (.cons b .nil)) ↔ t = a ∨ t = b := by
  simp

/-- The sum, from the other side of each pair. -/
def Forest.sum' : Forest Nat → Nat :=
  Forest.fold (S := Nat) fun | .nil => 0 | .cons a b => b + a

theorem Forest.sum_eq_sum' (m : Forest Nat) : m.sum = m.sum' := by
  induction m with
  | nil => simp [Forest.sum, Forest.sum']
  | cons a r ih =>
    simp only [Forest.sum, Forest.sum', Forest.fold_cons] at ih ⊢
    omega

/-- Maps that agree on the members of a forest agree on it: `mem_cons` splits the hypothesis on
the members into one on the head and one on the rest. -/
theorem Forest.map_congr {f g : Tree → Nat} (cs : Forest Tree)
    (h : ∀ t, PolyIso.Mem (fun X => Forest X) t cs → f t = g t) :
    (Occ.ofIso Forest).map (Occ.ofIso Forest) f cs =
      (Occ.ofIso Forest).map (Occ.ofIso Forest) g cs := by
  induction cs with
  | nil => simp
  | cons t r ih =>
    simp only [Forest.Colean.Poly.map_cons, Occ.map_ofIso_id, Forest.Colean.Poly.mem_cons,
      PolyIso.mem_id] at h ⊢
    rw [h t (.inl rfl), ih fun s hs => h s (.inr hs)]

/-- The size by `sum'`. -/
def Tree.size' : Tree → Nat :=
  Tree.fold (S := Nat) fun | .node _ cs => cs.sum' + 1

/-- Induction through the forest: the hypothesis of the recursor on the members of the forest. -/
theorem Tree.size_eq_size' (t : Tree) : t.size = t.size' := by
  induction t with
  | node n cs ih =>
    simp only [Tree.size, Tree.size', Tree.fold_node] at ih ⊢
    rw [Forest.map_congr cs ih, Forest.sum_eq_sum']

/-! ### Through `codatatype` -/

codatatype CStr (α : Type u)
  | cons (a : α) (t : CStr α)

codatatype CTree
  | node (n : Nat) (cs : CStr CTree)

-- The map through `CStr`'s instance on a constructor.
example (f : Nat → Nat) (a : Nat) (s : CStr Nat) :
    (Occ.ofIso CStr).map (Occ.ofIso CStr) f (CStr.cons a s) =
      CStr.cons (f a) ((Occ.ofIso CStr).map (Occ.ofIso CStr) f s) := by
  simp

example (x a b : Nat) (s : CStr Nat) :
    PolyIso.Mem (fun X => CStr X) x (.cons a (.cons b s)) ↔
      x = a ∨ x = b ∨ PolyIso.Mem (fun X => CStr X) x s := by
  simp

/-- A node whose children are all itself: two, then one per element of `s₀`. -/
def CTree.two (s₀ : CStr Unit) : CTree :=
  CTree.corec (S := Unit) (fun _ => .node 1 (.cons () (.cons () s₀))) ()

-- `dtor_corec` maps the state's stream through `CStr`'s instance; `map_cons` computes it.
example (s₀ : CStr Unit) :
    (CTree.two s₀).dtor = .node 1 (.cons (CTree.two s₀) (.cons (CTree.two s₀)
      ((Occ.ofIso CStr).map (Occ.ofIso CStr) (fun _ => CTree.two s₀) s₀))) := by
  simp only [CTree.two, CTree.dtor_corec, CTree.F.fmap_node, CStr.Colean.Poly.map_cons,
    Occ.map_ofIso_id]

-- `datatype` through `codatatype`.
datatype Bush
  | leaf
  | node (c : CStr Bush)

example (t a b : Bush) (s : CStr Bush) :
    PolyIso.Mem (fun X => CStr X) t (.cons a (.cons b s)) ↔
      t = a ∨ t = b ∨ PolyIso.Mem (fun X => CStr X) t s := by
  simp

/-- Induction through a stream: the hypothesis is used at its head. -/
theorem Bush.ind_head (P : Bush → Prop) (hl : P .leaf) (hn : ∀ a s, P a → P (.node (.cons a s)))
    (t : Bush) : P t := by
  induction t with
  | leaf => exact hl
  | node c ih =>
    cases c with
    | cons a s =>
      simp only [CStr.Colean.Poly.mem_cons, PolyIso.mem_id] at ih
      exact hn a s (ih a (.inl rfl))

/-! ### Through an indexed family -/

datatype Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (t : Vec α n) : Vec α (n + 1)

/--
info: @Vec.Colean.Poly.map_cons : ∀ {H : Type u_2 → Type u_1} {H' : Type u_3 → Type u_6} {S : Type u_4} {R : S → Type u_5}
  [inst : PolyIso H S R] [inst' : PolyIso H' S R] {X : Type u_2} {Y : Type u_3} (f : X → Y) {n : ℕ} (a : H X)
  (t : Vec (H X) n),
  (Occ.ofIso fun X => Vec (H X) (n + 1)).map (Occ.ofIso fun X => Vec (H' X) (n + 1)) f (Vec.cons a t) =
    Vec.cons ((Occ.ofIso H).map (Occ.ofIso H') f a)
      ((Occ.ofIso fun X => Vec (H X) n).map (Occ.ofIso fun X => Vec (H' X) n) f t)
-/
#guard_msgs(whitespace := lax) in
#check @Vec.Colean.Poly.map_cons

/--
info: @Vec.Colean.Poly.mem_cons : ∀ {H : Type u_2 → Type u_1} {S : Type u_3} {R : S → Type u_4} [inst : PolyIso H S R] {X : Type u_2}
  (x : X) {n : ℕ} (a : H X) (t : Vec (H X) n),
  PolyIso.Mem (fun X => Vec (H X) (n + 1)) x (Vec.cons a t) ↔ PolyIso.Mem H x a ∨ PolyIso.Mem (fun X => Vec (H X) n) x t
-/
#guard_msgs(whitespace := lax) in
#check @Vec.Colean.Poly.mem_cons

datatype Tri
  | leaf (n : Nat)
  | node (cs : Vec Tri 3)

/-- The sum of the leaves. -/
def Tri.sum : Tri → Nat :=
  Tri.fold (S := Nat) fun
    | .leaf n => n
    | .node cs => Vec.fold (S := fun _ => Nat) (fun _ y => Vec.F.casesOn y 0 fun a s => a + s) cs

example : (Tri.node (.cons (.leaf 1) (.cons (.leaf 2) (.cons (.node (.cons (.leaf 3)
    (.cons (.leaf 4) (.cons (.leaf 5) .nil)))) .nil)))).sum = 15 := by
  simp [Tri.sum]

-- The hypothesis of the recursor at the three children.
theorem Tri.ind_three (t : Tri) (P : Tri → Prop) (hl : ∀ n, P (.leaf n))
    (hn : ∀ a b c, P a → P b → P c → P (.node (.cons a (.cons b (.cons c .nil))))) : P t := by
  induction t with
  | leaf n => exact hl n
  | node cs ih =>
    cases cs with
    | cons a cs => cases cs with
      | cons b cs => cases cs with
        | cons c cs => cases cs with
          | nil =>
            simp only [Vec.Colean.Poly.mem_cons, Vec.Colean.Poly.mem_nil, PolyIso.mem_id,
              or_false] at ih
            exact hn a b c (ih a (.inl rfl)) (ih b (.inr (.inl rfl))) (ih c (.inr (.inr rfl)))

-- A family through a family, at its own index: the leaf is at a fixed index of the family
-- (`IOcc.ofOcc`), which `IOcc.map_ofOcc` takes off.
datatype VTree : Nat → Type
  | leaf : VTree 0
  | node {n : Nat} (cs : Vec (VTree n) n) : VTree (n + 1)

/-- The number of nodes. -/
def VTree.size {n : Nat} (t : VTree n) : Nat :=
  VTree.fold (S := fun _ => Nat) (fun _ y => VTree.F.casesOn y 1
    (fun cs => Vec.fold (S := fun _ => Nat) (fun _ y => Vec.F.casesOn y 0 fun a s => a + s) cs + 1))
    t

example : (VTree.node (.cons (VTree.node .nil) .nil)).size = 2 := by
  simp [VTree.size, IOcc.map_ofOcc]

example (t a : VTree 1) : PolyIso.Mem (fun X => Vec X 1) t (.cons a .nil) ↔ t = a := by
  simp

/-! ### Through a type of a block -/

mutual
datatype Ping (α : Type u)
  | nil
  | cons (a : α) (b : Pong α)
datatype Pong (α : Type u)
  | cons (a : α) (b : Ping α)
end

/--
info: @Ping.Colean.Poly.map_cons : ∀ {H : Type u_2 → Type u_1} {H' : Type u_3 → Type u_6} {S : Type u_4} {R : S → Type u_5}
  [inst : PolyIso H S R] [inst' : PolyIso H' S R] {X : Type u_2} {Y : Type u_3} (f : X → Y) (a : H X) (b : Pong (H X)),
  (Occ.ofIso fun X => Ping (H X)).map (Occ.ofIso fun X => Ping (H' X)) f (Ping.cons a b) =
    Ping.cons ((Occ.ofIso H).map (Occ.ofIso H') f a)
      ((Occ.ofIso fun X => Pong (H X)).map (Occ.ofIso fun X => Pong (H' X)) f b)
-/
#guard_msgs(whitespace := lax) in
#check @Ping.Colean.Poly.map_cons

/--
info: @Ping.Colean.Poly.mem_cons : ∀ {H : Type u_2 → Type u_1} {S : Type u_3} {R : S → Type u_4} [inst : PolyIso H S R]
  {X : Type u_2} (x : X) (a : H X) (b : Pong (H X)),
  PolyIso.Mem (fun X => Ping (H X)) x (Ping.cons a b) ↔ PolyIso.Mem H x a ∨ PolyIso.Mem (fun X => Pong (H X)) x b
-/
#guard_msgs(whitespace := lax) in
#check @Ping.Colean.Poly.mem_cons

datatype Chain
  | leaf
  | mk (p : Ping Chain)

/-- The number of nodes. -/
def Chain.size : Chain → Nat :=
  Chain.fold (S := Nat) fun
    | .leaf => 1
    | .mk p => (Ping_Pong.fold (S := fun _ => Nat) (fun _ y => Ping_Pong.F.casesOn y 0
      (fun a b => a + b) (fun a b => a + b)) p) + 1

example : (Chain.mk (.cons .leaf (.cons (.mk .nil) .nil))).size = 3 := by
  simp [Chain.size]

example (t a b : Chain) :
    PolyIso.Mem (fun X => Ping X) t (.cons a (.cons b .nil)) ↔ t = a ∨ t = b := by
  simp

/-! ### Two holes -/

datatype E (α β : Type u)
  | l (a : α)
  | r (b : β)

datatype T₃
  | leaf
  | mk (p : E (List T₃) T₃)

/-- The number of nodes. -/
def T₃.size : T₃ → Nat :=
  T₃.fold (S := Nat) fun
    | .leaf => 1
    | .mk p => E.fold (S := Nat) (fun | .l a => a.sum | .r b => b) p + 1

example : (T₃.mk (.l [.leaf, .mk (.r .leaf)])).size = 4 := by
  simp [T₃.size]

-- Membership through `fun X => E (List X) X`: in the list, or the right component.
example (t a b : T₃) : PolyIso.Mem (fun X => E (List X) X) t (.l [a, b]) ↔ t = a ∨ t = b := by
  simp

example (t a : T₃) : PolyIso.Mem (fun X => E (List X) X) t (.r a) ↔ t = a := by
  simp

/-- Induction through the two holes: the hypothesis on the members of the list, or on the right
component. -/
theorem T₃.ind_mem (P : T₃ → Prop) (hl : P .leaf) (hL : ∀ l, (∀ a ∈ l, P a) → P (.mk (.l l)))
    (hR : ∀ a, P a → P (.mk (.r a))) (t : T₃) : P t := by
  induction t with
  | leaf => exact hl
  | mk p ih =>
    cases p with
    | l l =>
      simp only [E.Colean.Poly.mem_l, PolyIso.mem_list] at ih
      exact hL l ih
    | r a =>
      simp only [E.Colean.Poly.mem_r, PolyIso.mem_id] at ih
      exact hR a (ih a rfl)

/-! ### Fields with a structure in the parameter -/

datatype Pair (α : Type u)
  | mk (p : α × α) (l : List α)

example (f : Nat → Nat) (a b : Nat) (l : List Nat) :
    (Occ.ofIso Pair).map (Occ.ofIso Pair) f (Pair.mk (a, b) l) = Pair.mk (f a, f b) (l.map f) := by
  simp

example (x a b : Nat) (l : List Nat) :
    PolyIso.Mem Pair x (Pair.mk (a, b) l) ↔ x = a ∨ x = b ∨ x ∈ l := by
  simp [or_assoc]

/-! ### A recursive argument under a telescope -/

datatype Fan (α : Type u)
  | leaf (a : α)
  | node (k : Nat → Fan α)

example (f : Nat → Nat) :
    (Occ.ofIso Fan).map (Occ.ofIso Fan) f (.node fun n => .leaf n) = .node fun n => .leaf (f n) := by
  simp

-- A member of some child.
example (x : Nat) : PolyIso.Mem Fan x (.node fun n => .leaf n) := by
  simp

end

end NestSimpTest
