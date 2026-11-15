import Mathlib.Logic.Equiv.Defs
import Colean.DataCmd

/-! # Test: `datatype` with two recursive arguments, and the native inductive type -/

universe u

namespace DataTest

noncomputable section

datatype FinTree (α : Type u)
  | leaf
  | node (a : α) (l r : FinTree α)

#check @FinTree.rec
#check @FinTree.fold_node

/-- The native type, for comparison. -/
inductive Native (α : Type u)
  | leaf
  | node (a : α) (l r : Native α)

def FinTree.toNative {α : Type u} (t : FinTree α) : Native α :=
  FinTree.fold (S := Native α) (fun | .leaf => .leaf | .node a l r => .node a l r) t

def FinTree.ofNative {α : Type u} : Native α → FinTree α
  | .leaf => .leaf
  | .node a l r => .node a (ofNative l) (ofNative r)

theorem FinTree.toNative_ofNative {α : Type u} (t : Native α) : (FinTree.ofNative t).toNative = t := by
  induction t with
  | leaf => simp [FinTree.ofNative, FinTree.toNative]
  | node a l r ihl ihr => simp [FinTree.ofNative, FinTree.toNative] at *; simp [ihl, ihr]

theorem FinTree.ofNative_toNative {α : Type u} (t : FinTree α) : FinTree.ofNative t.toNative = t := by
  induction t with
  | leaf => simp [FinTree.ofNative, FinTree.toNative]
  | node a l r ihl ihr => simp [FinTree.toNative] at *; simp [FinTree.ofNative, ihl, ihr]

/-- `FinTree α` is the native inductive type. -/
def FinTree.equivNative {α : Type u} : FinTree α ≃ Native α :=
  ⟨FinTree.toNative, FinTree.ofNative, FinTree.ofNative_toNative, FinTree.toNative_ofNative⟩

/-- Mirror, by the fold, and an involution by induction. -/
def FinTree.mirror {α : Type u} (t : FinTree α) : FinTree α :=
  FinTree.fold (S := FinTree α) (fun | .leaf => .leaf | .node a l r => .node a r l) t

@[simp] theorem FinTree.mirror_leaf {α : Type u} : (FinTree.leaf : FinTree α).mirror = .leaf := by
  simp [FinTree.mirror]

@[simp] theorem FinTree.mirror_node {α : Type u} (a : α) (l r : FinTree α) :
    (FinTree.node a l r).mirror = .node a r.mirror l.mirror := by
  simp [FinTree.mirror]

theorem FinTree.mirror_mirror {α : Type u} (t : FinTree α) : t.mirror.mirror = t := by
  induction t with
  | leaf => simp
  | node a l r ihl ihr => simp [ihl, ihr]

/-- The dependent recursor computes on the constructors, propositionally. -/
example {α : Type u} (a : α) (l r : FinTree α) (leaf : Nat) (node : α → Nat → Nat → Nat) :
    FinTree.rec (motive := fun _ => Nat) leaf (fun a _ _ nl nr => node a nl nr) (FinTree.node a l r) =
      node a (FinTree.rec leaf (fun a _ _ nl nr => node a nl nr) l)
        (FinTree.rec leaf (fun a _ _ nl nr => node a nl nr) r) := by
  simp

end

end DataTest
