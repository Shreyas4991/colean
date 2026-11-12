import Colean

/-! The examples of `README.md`, checked: each section is one example, verbatim. -/

noncomputable section

universe u

namespace ReadmeStreams

codata Strm (α : Type u)
  | cons (head : α) (tail : Strm α)

/-- `a, f a, f (f a), …`: the state is the next element. -/
def Strm.iterate {α : Type u} (f : α → α) (a : α) : Strm α :=
  Strm.corec (fun x => .cons x (f x)) a

def Strm.map {α β : Type u} (f : α → β) : Strm α → Strm β :=
  Strm.corec fun s => match s.dtor with | .cons a t => .cons (f a) t

@[simp] theorem Strm.dtor_iterate {α : Type u} (f : α → α) (a : α) :
    (Strm.iterate f a).dtor = .cons a (Strm.iterate f (f a)) := by
  simp [Strm.iterate, Strm.dtor_corec]

@[simp] theorem Strm.map_cons {α β : Type u} (f : α → β) (a : α) (s : Strm α) :
    (Strm.cons a s).map f = .cons (f a) (s.map f) := by
  rw [← Strm.ctor_dtor (Strm.map f _), Strm.map, Strm.dtor_corec]
  simp

/-- By coinduction: relate the two sides at every `b`, and show one step. -/
theorem Strm.map_iterate {α : Type u} (f : α → α) (a : α) :
    (Strm.iterate f a).map f = Strm.iterate f (f a) := by
  refine Strm.bisim (fun x y => ∃ b, x = (Strm.iterate f b).map f ∧
    y = Strm.iterate f (f b)) ?_ ⟨a, rfl, rfl⟩
  rintro _ _ ⟨b, rfl, rfl⟩
  rw [← Strm.ctor_dtor (Strm.iterate f b)]
  simp only [Strm.dtor_iterate, Strm.ctor_cons, Strm.map_cons, Strm.dtor_cons]
  exact .cons _ _ _ ⟨f b, rfl, rfl⟩

end ReadmeStreams

namespace ReadmeVec

data Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

def Vec.toList {α : Type u} {n : Nat} (v : Vec α n) : List α :=
  Vec.rec (motive := fun _ _ => List α) [] (fun a _ l => a :: l) v

theorem Vec.length_toList {α : Type u} {n : Nat} (v : Vec α n) : v.toList.length = n := by
  induction v with
  | nil => simp [Vec.toList]
  | cons a v ih => simp_all [Vec.toList]

example {α : Type u} (v : Vec α 0) : v = .nil := by
  cases v with
  | nil => rfl

end ReadmeVec

namespace ReadmeMutual

mutual
data Tree
  | node (n : Nat) (cs : Forest)
data Forest
  | nil
  | cons (t : Tree) (f : Forest)
end

def Tree.size (t : Tree) : Nat :=
  Tree.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ _ k => k + 1) 0 (fun _ _ a b => a + b) t

theorem Tree.size_pos (t : Tree) : 0 < t.size := by
  induction t using Tree.rec (motive_2 := fun _ => True) with
  | node n cs ih => simp [Tree.size]
  | nil => trivial
  | cons t f iht ihf => trivial

end ReadmeMutual

namespace ReadmeRose

data Rose (α : Type u)
  | node (a : α) (cs : List (Rose α))

def Rose.size {α : Type u} (t : Rose α) : Nat :=
  Rose.fold (S := Nat) (fun | .node _ cs => cs.sum + 1) t

def Rose.labels {α : Type u} (t : Rose α) : List α :=
  Rose.fold (S := List α) (fun | .node a ls => a :: ls.flatten) t

@[simp] theorem Rose.size_node {α : Type u} (a : α) (cs : List (Rose α)) :
    (Rose.node a cs).size = (cs.map Rose.size).sum + 1 := by
  simp [Rose.size, Rose.fold_node]; rfl

@[simp] theorem Rose.labels_node {α : Type u} (a : α) (cs : List (Rose α)) :
    (Rose.node a cs).labels = a :: (cs.map Rose.labels).flatten := by
  simp [Rose.labels, Rose.fold_node]; rfl

/-- The induction hypothesis holds at every member of the list of children. -/
theorem Rose.length_labels {α : Type u} (t : Rose α) : t.labels.length = t.size := by
  induction t with
  | node a cs ih =>
    simp only [Codata.PolyIso.mem_list] at ih
    simp [List.length_flatten, Function.comp_def, List.map_congr_left ih]

end ReadmeRose

namespace ReadmeMixed

mixed_mutual
codata Tree (α : Type u)
  | node (a : α) (children : Forest α)
data Forest (α : Type u)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

/-- An infinite binary tree: the corecursion builds a finite forest of states. -/
def Tree.bin {α : Type u} (a : α) : Tree α :=
  Tree.corec (S := Unit) (fun _ => .node a (.cons () (.cons () .nil))) ()

theorem Tree.bin_eq {α : Type u} (a : α) :
    Tree.bin a = .node a (.cons (.bin a) (.cons (.bin a) .nil)) := by
  conv_lhs => rw [← Tree.ctor_dtor (Tree.bin a), Tree.bin, Tree.dtor_corec]
  simp [Tree.bin]

def Forest.length {α : Type u} (f : Forest α) : Nat :=
  Forest.fold (S := Nat) (fun | .nil => 0 | .cons _ n => n + 1) f

end ReadmeMixed

namespace ReadmeCCPO

@[with_ccpo]
codata CoList (α : Type u)
  | nil
  | cons (a : α) (t : CoList α)

def CoList.nats (n : Nat) : CoList Nat := .cons n (nats (n + 1))
partial_fixpoint

def CoList.map {α β : Type u} (f : α → β) (s : CoList α) : CoList β :=
  match s.dtor with
  | .nil => .nil
  | .cons a t => .cons (f a) (map f t)
partial_fixpoint

/-- Not productive: the least fixpoint is the bottom, `nil`. -/
def CoList.stuck : CoList Nat := stuck
partial_fixpoint

example {α β : Type u} (f : α → β) (a : α) (t : CoList α) :
    (CoList.cons a t).map f = .cons (f a) (t.map f) := by
  rw [CoList.map]; simp

open Lean.Order in
example : CoList.stuck = .nil := by
  have h : CoList.stuck ⊑ .nil :=
    CoList.stuck.fixpoint_induct _ (Codata.admissible_rel _) fun _ h => h
  exact PartialOrder.rel_antisymm h (CoList.bot_eq ▸ bot_le _)

end ReadmeCCPO

end
