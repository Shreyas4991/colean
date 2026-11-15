import Colean.MutualCmd

/-! # Test: the front end, as `inductive` elaborates a declaration

Universes left to the command become universe parameters `u_1`, … (`Type _`, `Sort _`, an
auto-bound `α`, section variables), and the constructors may fix them. Parameters keep the binder
annotations the user wrote, and the types of a block must agree on them. The recursors have their
motive's universe first, as does every declaration with a motive or a state, named `u` when free
(`T.fold.{u, u_1}`). A default value or tactic is on the constructor only. Injectivity is
stated as `injEq` is, with `HEq` where the two sides' types differ. Types with dotted names may
form a block. A single index that is a proposition is reported at the index. A constructor has
the declaration ranges of its own syntax. The internals are under `T.Colean`, `protected`.
`induction` on a `codatatype` is its case analysis, and on a type of a `datatype` block it is
refused, as on a mutual inductive. A constructor may be named as an internal, not as a generated
declaration of its type or functor, nor twice. -/

namespace FrontEndTest

noncomputable section

/-! ### Universes left to the command -/

datatype AB3 (α : Type _)
  | mk (a : α) (t : AB3 α)
  | nil

/-- info: FrontEndTest.AB3.{u_1} (α : Type u_1) : Type u_1 -/
#guard_msgs in #check AB3

datatype AB5 {α} (a : α)
  | nil

/-- info: @AB5 : {α : Sort u_1} → α → Type -/
#guard_msgs in #check @AB5

datatype AB2 (xs : List α)
  | mk (a : α) (t : AB2 xs)

/-- info: @AB2 : {α : Type u_1} → List α → Type u_1 -/
#guard_msgs in #check @AB2

codatatype CS (α : Sort _) (β : Type _)
  | mk (b : β) (f : α → CS α β)

/-- info: FrontEndTest.CS.{u_1, u_2} (α : Sort u_1) (β : Type u_2) : Type (max u_1 u_2) -/
#guard_msgs in #check CS

section

variable {α : Type _}

datatype SA
  | mk (a : α) (t : SA)
  | nil

end

/-- info: @SA.mk : {α : Type u_1} → α → SA → SA -/
#guard_msgs in #check @SA.mk

-- The universe of an index, fixed by a constructor; the family is in the universe of its
-- encoding, one up.
datatype A2 : (α : Type _) → Type _
  | mk (a : Nat) : A2 Nat

/-- info: A2 : Type → Type 1 -/
#guard_msgs in #check @A2

-- Mathlib's `Type*`.
datatype TS (α : Type*) (β : Type*)
  | mk (a : α) (b : β) (t : TS α β)
  | nil

/-- info: FrontEndTest.TS.{u_1, u_2} (α : Type u_1) (β : Type u_2) : Type (max u_1 u_2) -/
#guard_msgs in #check TS

example : AB3 Nat := .mk 1 .nil

example : CS Unit Nat := CS.corec (S := Unit) (fun _ => .mk 0 fun _ => ()) ()

/-! ### The recursor's universes: the motive's first, as in `inductive`

So for every declaration with a motive or a state: its universe first, named `u` when the type
has no universe `u`, else the first of `u_1`, `u_2`, … it has not. -/

/-- `AB3.rec.{2, 0}` is the recursor into `Sort 2` of `AB3.{0}`, as `List.rec.{2, 0}` is. -/
example : AB3.{0} Nat → Type := AB3.rec.{2, 0} (fun _ _ _ => Unit) Unit

example : AB3.{0} Nat → Type := fun t =>
  AB3.casesOn.{2, 0} (motive := fun _ => Type) t (fun _ _ => Unit) Unit

/-- `AB3.fold.{1, 0}` folds `AB3.{0}` into `Type`. -/
example : AB3.{0} Nat → Type := AB3.fold.{1, 0} fun | .mk _ _ => Unit | .nil => Unit

/-- `CS.corec.{0, 1, 0}` unfolds a state in `Type` into `CS.{1, 0}`. -/
example : CS.{1, 0} Unit Nat := CS.corec.{0, 1, 0} (S := Unit) (fun _ => .mk 0 fun _ => ()) ()

/--
info: FrontEndTest.AB3.rec.{u, u_1} {α : Type u_1} {motive : AB3 α → Sort u}
  (mk : (a : α) → (t : AB3 α) → motive t → motive (AB3.mk a t)) (nil : motive AB3.nil) (t : AB3 α) : motive t
-/
#guard_msgs in #check AB3.rec

/-- info: FrontEndTest.AB3.fold.{u, u_1} {α : Type u_1} {S : Type u} (a : AB3.F α S → S) (t : AB3 α) : S -/
#guard_msgs in #check AB3.fold

/--
info: FrontEndTest.CS.corec.{u, u_1, u_2} {α : Sort u_1} {β : Type u_2} {S : Type u} (c : S → CS.F α β S) (s : S) : CS α β
-/
#guard_msgs in #check CS.corec

-- With a universe `u` of its own, the motive's is `u_1`; with `u` and `u_1`, `u_2`.
datatype UU (α : Type u)
  | mk (a : α)

/--
info: FrontEndTest.UU.rec.{u_1, u} {α : Type u} {motive : UU α → Sort u_1} (mk : (a : α) → motive (UU.mk a)) (t : UU α) :
  motive t
-/
#guard_msgs in #check UU.rec

datatype UU₁ (α : Type u_1) (β : Type u)
  | mk (a : α) (b : β)

/--
info: FrontEndTest.UU₁.casesOn_mk.{u_2, u_1, u} {α : Type u_1} {β : Type u} {motive : UU₁ α β → Sort u_2} (a : α) (b : β)
  (mk : (a : α) → (b : β) → motive (UU₁.mk a b)) : UU₁.casesOn (UU₁.mk a b) mk = mk a b
-/
#guard_msgs in #check UU₁.casesOn_mk

/-! ### Binder annotations of the parameters -/

datatype DA {α : Type} (xs : List α)
  | mk

/-- info: @DA : {α : Type} → List α → Type -/
#guard_msgs in #check @DA

datatype TV (v : Fin n)
  | mk (t : TV v)
  | nil

/-- info: @TV : {n : ℕ} → Fin n → Type -/
#guard_msgs in #check @TV

example : TV (3 : Fin 5) := .mk .nil

-- Right of the colon, as in `inductive`, the parameters left implicit are the parameters.
datatype DB {α : Type} : Nat → Type
  | mk (a : α) : DB 1 → DB 0
  | nil : DB 1

/-- info: @DB.mk : {α : Type} → α → DB 1 → DB 0 -/
#guard_msgs in #check @DB.mk

/-- info: @DB.F : {α : Type} → (ℕ → Type u_1) → ℕ → Type u_1 -/
#guard_msgs in #check @DB.F

/-- error: the types of a mutual block must have the same parameters as `BA`, with the same binder
annotations, and `α` is bound differently -/
#guard_msgs in
mutual
datatype BA {α : Type}
  | mk (b : BB α)
datatype BB (α : Type)
  | mk (a : BA (α := α))
  | nil
end

/-! ### Generated binders named as a parameter: primed, so that they can still be named -/

codatatype PS (S : Type)
  | cons (head : S) (tail : PS S)

/--
info: @PS.corec : {S : Type} → {S' : Type u_1} → (S' → PS.F S S') → S' → PS S
-/
#guard_msgs in #check @PS.corec

example : PS Nat := PS.corec (S' := Unit) (fun _ => .cons 1 ()) ()

codatatype PS2 (S S' : Type)
  | cons (head : S) (other : S') (tail : PS2 S S')

/--
info: @PS2.corec : {S S' : Type} → {S'' : Type u_1} → (S'' → PS2.F S S' S'') → S'' → PS2 S S'
-/
#guard_msgs in #check @PS2.corec

example : PS2 Nat Bool := PS2.corec (S'' := Unit) (fun _ => .cons 1 true ()) ()

/-! ### Constructors with instance and strict-implicit binders, and injectivity -/

section

variable {α : Type} [Inhabited α] {n : Nat}

datatype SV
  | mk (a : α) (h : a = default) (v : Fin n) (t : SV)
  | nil

end

-- The proof is left out of the conjunction, and does not stop the lemma.
/--
info: @SV.mk_inj : ∀ {α : Type} [inst : Inhabited α] {n : ℕ} (a : α) (h : a = default) (v : Fin n) (t : SV) (a' : α)
  (h' : a' = default) (v' : Fin n) (t' : SV), SV.mk a h v t = SV.mk a' h' v' t' ↔ a = a' ∧ v = v' ∧ t = t'
-/
#guard_msgs in #check @SV.mk_inj

datatype IB (α) [Inhabited α]
  | mk [DecidableEq α] (a : α) (t : IB α)
  | nil

-- The instance is an argument like any other: its copy is implicit.
/--
info: @IB.mk_inj : ∀ {α : Sort u_1} [inst : Inhabited α] [a₁ : DecidableEq α] (a : α) (t : IB α) {a₁' : DecidableEq α}
  (a' : α) (t' : IB α), IB.mk a t = IB.mk a' t' ↔ a₁ = a₁' ∧ a = a' ∧ t = t'
-/
#guard_msgs in #check @IB.mk_inj

example (a : Nat) : IB Nat := .mk a .nil

example (a b : Nat) (h : IB.mk a .nil = IB.mk b .nil) : a = b := by
  simpa using h

-- An implicit and a strict-implicit argument that the result does not determine: `HEq` where the
-- two sides' types differ.
datatype IM
  | mk {n : Nat} (v : Fin n) (h : n > 0)
  | mk₂ ⦃n : Nat⦄ (v : Fin n)

/--
info: @IM.mk_inj : ∀ {n : ℕ} (v : Fin n) (h : n > 0) {n' : ℕ} (v' : Fin n') (h' : n' > 0),
  IM.mk v h = IM.mk v' h' ↔ n = n' ∧ v ≍ v'
-/
#guard_msgs in #check @IM.mk_inj

/--
info: IM.mk₂_inj : ∀ ⦃n : ℕ⦄ (v : Fin n) ⦃n' : ℕ⦄ (v' : Fin n'), IM.mk₂ v = IM.mk₂ v' ↔ n = n' ∧ v ≍ v'
-/
#guard_msgs in #check @IM.mk₂_inj

example (v w : Fin 3) (h : IM.mk₂ v = IM.mk₂ w) : v = w := by
  simpa using h

-- A proof argument that depends on data.
datatype PD
  | mk (n : Nat) (h : n % 2 = 0) (t : PD)
  | nil

/--
info: PD.mk_inj : ∀ (n : ℕ) (h : n % 2 = 0) (t : PD) (n' : ℕ) (h' : n' % 2 = 0) (t' : PD),
  PD.mk n h t = PD.mk n' h' t' ↔ n = n' ∧ t = t'
-/
#guard_msgs in #check @PD.mk_inj

/-! ### Default values and tactics: on the constructor only -/

datatype DT
  | nil
  | mk (n : Nat := 3) (t : DT) (m : Nat := by exact 2)

/--
info: @DT.rec : {motive : DT → Sort u_1} →
  motive DT.nil → ((n : ℕ) → (t : DT) → (m : ℕ) → motive t → motive (DT.mk n t m)) → (t : DT) → motive t
-/
#guard_msgs in #check @DT.rec

/--
info: DT.mk_inj : ∀ (n : ℕ) (t : DT) (m n' : ℕ) (t' : DT) (m' : ℕ), DT.mk n t m = DT.mk n' t' m' ↔ n = n' ∧ t = t' ∧ m = m'
-/
#guard_msgs in #check @DT.mk_inj

/-- info: @DT.F.mk : {X : Type u_1} → ℕ → X → ℕ → DT.F X -/
#guard_msgs in #check @DT.F.mk

-- The constructor keeps them.
example : DT.mk (t := .nil) = DT.mk 3 .nil 2 := rfl

datatype DO
  | mk (n : Nat := 3)

/-- info: @DO.mk : optParam ℕ 3 → DO -/
#guard_msgs in #check @DO.mk

/-! ### Dotted names in a block -/

mutual
datatype Foo.A
  | a (b : Foo.B)
  | z
datatype Foo.B
  | b (a : Foo.A)
end

/-- info: Foo.A_B : Foo.A_B.Ix → Type -/
#guard_msgs in #check @Foo.A_B

/-- info: Foo.A_B.Ix.A : Foo.A_B.Ix -/
#guard_msgs in #check @Foo.A_B.Ix.A

example : Foo.A := .a (.b .z)

mutual
datatype Qa.X
  | mk (y : Qb.X)
  | nil
datatype Qb.X
  | mk (x : Qa.X)
end

/-- info: Qa_X_Qb_X : Qa_X_Qb_X.Ix → Type -/
#guard_msgs in #check @Qa_X_Qb_X

-- The shared constructor name is qualified by the type's name in the block.
/-- info: @Qa_X_Qb_X.F.Qa_X_mk : {X : Qa_X_Qb_X.Ix → Type u_1} → X Qa_X_Qb_X.Ix.Qb_X → Qa_X_Qb_X.F X Qa_X_Qb_X.Ix.Qa_X -/
#guard_msgs in #check @Qa_X_Qb_X.F.Qa_X_mk

example : Qa.X := .mk (.mk .nil)

/--
error: `Qc.X` and `Qc_X` give the same constructor `Qc_X` to the index of their block, which joins
the components of a type's name by `_`; rename one of them
-/
#guard_msgs in
mutual
datatype Qc_X
  | mk (y : Qc.X)
  | nil
datatype Qc.X
  | mk (x : Qc_X)
end

-- In a mixed block too, the types are declared in their common namespace.
mixed_mutual
codatatype Foo.Tree (α : Type)
  | node (a : α) (cs : Foo.Forest α)
datatype Foo.Forest (α : Type)
  | nil
  | cons (t : Foo.Tree α) (f : Foo.Forest α)
end

/-- info: FrontEndTest.Foo.Forest.instMembershipTree {α : Type} : Membership (Foo.Tree α) (Foo.Forest α) -/
#guard_msgs in #check Foo.Forest.instMembershipTree

/-! ### Dotted names, as `inductive`

A declaration `datatype Baz.Qux …` is elaborated inside `namespace Baz`, so the constructors
refer to the type as `Qux` or `Baz.Qux`, in their arguments and in their result type, and see
the declarations of `Baz` by their short names; a block whose types share a namespace is
elaborated inside it. -/

section
set_option autoImplicit false

def Baz.Label := Nat

datatype Baz.Qux
  | leaf
  | mk (t : Qux)
  | mk₂ (t : Baz.Qux) (l : Label) : Qux

/-- info: FrontEndTest.Baz.Qux.mk₂ (t : Baz.Qux) (l : Baz.Label) : Baz.Qux -/
#guard_msgs in #check Baz.Qux.mk₂

codatatype Baz.CoQux (α : Type)
  | mk (a : α) (t : CoQux α) : Baz.CoQux α

/-- info: FrontEndTest.Baz.CoQux.mk {α : Type} (a : α) (t : Baz.CoQux α) : Baz.CoQux α -/
#guard_msgs in #check Baz.CoQux.mk

-- A nested occurrence by the short name, and the recursor.
datatype Baz.RoseQ
  | node (cs : List RoseQ)

/--
info: @Baz.RoseQ.rec : {motive : Baz.RoseQ → Sort u_1} →
  ((cs : List Baz.RoseQ) → ((t : Baz.RoseQ) → t ∈ cs → motive t) → motive (Baz.RoseQ.node cs)) →
    (t : Baz.RoseQ) → motive t
-/
#guard_msgs in #check @Baz.RoseQ.rec

mutual
datatype Ns.T
  | mk (u : U)
  | nil
datatype Ns.U
  | mk (t : Ns.T) : U
end

/-- info: FrontEndTest.Ns.T_U (m : Ns.T_U.Ix) : Type -/
#guard_msgs in #check Ns.T_U

/-- info: FrontEndTest.Ns.T.mk (u : Ns.U) : Ns.T -/
#guard_msgs in #check Ns.T.mk

mixed_mutual
codatatype Ns.CoT
  | node (f : CoF)
datatype Ns.CoF
  | nil
  | cons (t : CoT) (f : Ns.CoF)
end

/-- info: FrontEndTest.Ns.CoT.node (f : Ns.CoF) : Ns.CoT -/
#guard_msgs in #check Ns.CoT.node

-- Without a common namespace, the types are referred to by their full names, as in `inductive`.
/--
error: Unknown identifier `V`

Note: It is not possible to treat `V` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
-/
#guard_msgs in
mutual
datatype Ns₁.S
  | mk (v : V)
datatype Ns₂.V
  | mk (s : Ns₁.S)
end

end

/-! ### A single index that is a proposition -/

/--
error: the index of `P1` is a proposition, and a single index must be a type: the encoding indexes the family by a type (a proposition next to another index is fine); a parameter, or an argument of the constructors, does the same, proofs being irrelevant
-/
#guard_msgs in
codatatype P1 : (0 < 5) → Type
  | mk (h : 0 < 5) (t : P1 h) : P1 h

-- Next to another index, it is fine.
codatatype P2 : (n : Nat) → (0 < n) → Type
  | mk {n : Nat} (h : 0 < n) (t : P2 n h) : P2 n h

/--
error: the index of `P3` may be a proposition, its type being in a universe that may be `Prop`, and a single index must be a type: the encoding indexes the family by a type; give its type a universe `Type _`
-/
#guard_msgs in
datatype P3 (α : Sort _) : α → Type _
  | mk (a : α) : P3 α a

/-! ### Universes left to the command in blocks -/

mutual
datatype MA (α : Type _)
  | mk (a : α) (b : MB α)
datatype MB (α : Type _)
  | nil
  | mk (a : MA α)
end

/-- info: MA : Type u_1 → Type u_1 -/
#guard_msgs in #check @MA

/-- info: MA_MB.Ix : Type u_1 → Type -/
#guard_msgs in #check @MA_MB.Ix

mixed_mutual
codatatype MT (α : Type _)
  | node (a : α) (cs : MF α)
datatype MF (α : Type _)
  | nil
  | cons (t : MT α) (f : MF α)
end

/-- info: @MF.cons : {α : Type u_1} → MT α → MF α → MF α -/
#guard_msgs in #check @MF.cons

-- An inner run of two types, whose index is declared before the runs.
mixed_mutual
codatatype NT (α : Type _)
  | node (a : α) (cs : NF α)
datatype NF (α : Type _)
  | nil
  | cons (t : NT α) (g : NG α)
datatype NG (α : Type _)
  | nil
  | cons (f : NF α)
end

/-- info: NF_NG.Ix : Type u_1 → Type -/
#guard_msgs in #check @NF_NG.Ix

/-- info: @NG.cons : {α : Type u_1} → NF α → NG α -/
#guard_msgs in #check @NG.cons

/-! ### Protected declarations

The internals are `protected`, as `inductive` protects its auxiliary constructions: after `open T`
their short names do not resolve, while the full names and dot notation do. The eliminators `rec`,
`casesOn` (as Lean leaves them), `fold`, `corec` and `dtor` are not protected. -/

datatype PT
  | leaf
  | node (l r : PT)

section
open PT

example : PT → Nat := rec (motive := fun _ => Nat) 1 (fun _ _ a b => a + b + 1)

example : PT → Nat := fold fun _ => 0

/-- error: Unknown identifier `toC` -/
#guard_msgs in #check toC

-- The internals are under `PT.Colean`, protected there too.
section
open PT.Colean

/-- error: Unknown identifier `toC` -/
#guard_msgs in #check toC

example : PT.Colean.Shape := .leaf

end

/-- The full names, dot notation and the constructors. -/
def PT.size (t : PT) : Nat :=
  PT.rec (motive := fun _ => Nat) 1 (fun _ _ a b => a + b + 1) t

example (t : PT) : Nat := t.fold fun _ => 0

example : PT := node leaf (node leaf leaf)

example : (node leaf leaf).size = 3 := by simp [PT.size, PT.rec_node, PT.rec_leaf]

example (t : PT) : 0 < t.size := by
  induction t using PT.rec with
  | leaf => simp [PT.size, PT.rec_leaf]
  | node l r _ _ => simp [PT.size, PT.rec_node]

end

/-! ### Declaration ranges: a constructor's own syntax, its name selected -/

open Lean in
/-- The lines of the ranges of `n`, from the line of `T`, and the column of its selection. -/
def rangeOf (T n : Name) : MetaM (Nat × Nat × Nat) := do
  let some t ← findDeclarationRanges? T | throwError "no range for {T}"
  let some r ← findDeclarationRanges? n | throwError "no range for {n}"
  return (r.range.pos.line - t.range.pos.line, r.range.endPos.line - t.range.pos.line,
    r.selectionRange.pos.column)

datatype RG
  | nil
  | cons (n : Nat)
      (t : RG)

/-- info: (2, 3, 4) -/
#guard_msgs in #eval rangeOf ``RG ``RG.cons

end

/-! ### `induction` on the types

`induction` on a `codatatype` is its case analysis, `T.casesOn` being the `induction`
eliminator as well as the `cases` one: `codatatype` has no induction, and the type is not shown as
its encoding. On a type of a `datatype` block, plain `induction` is refused, as Lean refuses a
mutual inductive, with the recursor per type as the hint; `induction t using Tm.rec (motive_2 := …)`
is the induction. -/

codatatype ICo (α : Type)
  | nil
  | cons (head : α) (tail : ICo α)

/--
error: unsolved goals
case nil
⊢ True

case cons
head✝ : ℕ
tail✝ : ICo ℕ
⊢ True
-/
#guard_msgs in
example (s : ICo Nat) : True := by induction s

example (s : ICo Nat) : True := by
  induction s with
  | nil => trivial
  | cons h t => trivial

mutual
codatatype ICA
  | a (x : ICB)
codatatype ICB
  | b (y : ICA)
  | e
end

/--
error: unsolved goals
case b
y✝ : ICA
⊢ True

case e
⊢ True
-/
#guard_msgs in
example (t : ICB) : True := by induction t

mixed_mutual
datatype IOut
  | node (a : Nat) (children : IIn)
codatatype IIn
  | nil
  | cons (t : IOut) (f : IIn)
end

/--
error: unsolved goals
case nil
⊢ True

case cons
t✝ : IOut
f✝ : IIn
⊢ True
-/
#guard_msgs in
example (t : IIn) : True := by induction t

mutual
datatype ITm
  | var (n : Nat)
  | app (f : ITm) (args : IArgs)
datatype IArgs
  | nil
  | cons (t : ITm) (rest : IArgs)
end

/--
error: The `induction` tactic does not support the type `ITm` because it is a type of a mutual `datatype` block

Hint: Use its recursor, with the other motives given by name: `induction t using ITm.rec (motive_2 := …)`, or the `cases` tactic
-/
#guard_msgs in
example (t : ITm) : True := by induction t

example (t : ITm) : 0 < 1 := by
  induction t using ITm.rec (motive_2 := fun _ => 0 < 1) with
  | var n => decide
  | app f a _ _ => decide
  | nil => decide
  | cons t r _ _ => decide

example (t : ITm) : True := by
  cases t with
  | var n => trivial
  | app f a => trivial

-- The closed types of a `datatype` block inside a `mixed_mutual` block are refused too.
mixed_mutual
codatatype IMOut
  | node (a : Nat) (children : IMTm)
datatype IMTm
  | nil
  | cons (t : IMOut) (f : IMArgs)
datatype IMArgs
  | nil
  | cons (t : IMTm) (f : IMArgs)
end

/--
error: The `induction` tactic does not support the type `IMArgs` because it is a type of a mutual `datatype` block

Hint: Use its recursor, with the other motives given by name: `induction t using IMArgs.rec (motive_1 := …)`, or the `cases` tactic
-/
#guard_msgs in
example (t : IMArgs) : True := by induction t

/-! ### Constructor names

The internals are under `T.Colean` (`T.Colean.B`, the positions, `T.Colean.Shape`, `T.Colean.sig`,
`T.Colean.toC`, `T.Colean.Poly.*`), and the functor's action on functions is `T.F.fmap`, so
constructors may have these names. A constructor named like a generated declaration of its type,
or of the functor, which has a constructor of the same name, is refused before anything is
declared, also one generated from another constructor (`a_inj`, `a_ne_b`, `F.rel_a_b`, the
membership lemmas of a mixed block), and so are constructors that give two generated declarations
one name; so is a constructor declared twice, with the message of `inductive`. -/

datatype Letter
  | A
  | B
  | C

/-- info: FrontEndTest.Letter.B : Letter -/
#guard_msgs in #check Letter.B

example : Letter.A ≠ Letter.B := by simp

datatype Op
  | map
  | filter
  | reduce

example : Op.map ≠ Op.filter := by simp

example : Op.fold (fun | .map => 1 | .filter => 2 | .reduce => 3) Op.map = 1 := by simp

datatype Shape2
  | Shape
  | sig

example : Shape2.Shape ≠ Shape2.sig := by simp

codatatype Q
  | Poly (q : Q)
  | toC (q : Q)

example (q : Q) : (Q.Poly q).dtor = .Poly q := by simp

/--
error: constructor `dtor` clashes with the generated declaration `FrontEndTest.Cmd.dtor`; rename the constructor
-/
#guard_msgs in
codatatype Cmd
  | dtor
  | ctor

/-- error: Unknown identifier `Cmd` -/
#guard_msgs in #check Cmd

/--
error: constructor `fold_eq` clashes with the generated declaration `FrontEndTest.Cmd.fold_eq`; rename the constructor
-/
#guard_msgs in
datatype Cmd
  | stop
  | fold_eq (c : Cmd)

-- A rule of another constructor.
/--
error: constructor `dtor_a` clashes with the generated declaration `FrontEndTest.Cmd.dtor_a`; rename the constructor
-/
#guard_msgs in
datatype Cmd
  | a
  | dtor_a

/--
error: constructor `Colean` clashes with `FrontEndTest.Cmd.Colean`, the namespace of the generated internals; rename the constructor
-/
#guard_msgs in
datatype Cmd
  | Colean

-- The functor `Cmd.F` has a constructor for each constructor.
/--
error: constructor `fmap` clashes with the generated declaration `FrontEndTest.Cmd.F.fmap`: the functor `FrontEndTest.Cmd.F` has a constructor `FrontEndTest.Cmd.F.fmap` for it; rename the constructor
-/
#guard_msgs in
datatype Cmd
  | fmap
  | filter

/--
error: constructor `rec` clashes with the generated declaration `FrontEndTest.Cmd.F.rec`: the functor `FrontEndTest.Cmd.F` has a constructor `FrontEndTest.Cmd.F.rec` for it; rename the constructor
-/
#guard_msgs in
codatatype Cmd
  | rec
  | next (c : Cmd)

/--
error: constructor `mono` clashes with the generated declaration `FrontEndTest.Cmd.F.Rel.mono`: the lifting `FrontEndTest.Cmd.F.Rel` has a constructor `FrontEndTest.Cmd.F.Rel.mono` for it; rename the constructor
-/
#guard_msgs in
codatatype Cmd
  | stop
  | mono (c : Cmd)

-- In a block, a constructor of one type only keeps its name in the block's functor; one of
-- several types is qualified there (`CA_CB.F.CA_recOn`). The layer per type has it under its own
-- name (`CA.F.fmap`), which must not be a declaration of the layer either.
/--
error: constructor `fmap` clashes with the generated declaration `FrontEndTest.CA_CB.F.fmap`: the functor `FrontEndTest.CA_CB.F` has a constructor `FrontEndTest.CA_CB.F.fmap` for it; rename the constructor
-/
#guard_msgs in
mutual
datatype CA
  | fmap (b : CB)
datatype CB
  | stop
end

/--
error: constructor `fmap` clashes with the generated declaration `FrontEndTest.CA.F.fmap`: the layer `FrontEndTest.CA.F` has a constructor `FrontEndTest.CA.F.fmap` for it; rename the constructor
-/
#guard_msgs in
mutual
datatype CA
  | fmap (b : CB)
  | stop
datatype CB
  | fmap (a : CA)
  | contract
end

/--
error: constructor `fmap_stop` clashes with the generated declaration `FrontEndTest.CA.F.fmap_stop`: the layer `FrontEndTest.CA.F` has a constructor `FrontEndTest.CA.F.fmap_stop` for it; rename the constructor
-/
#guard_msgs in
mutual
datatype CA
  | fmap_stop (b : CB)
  | stop
datatype CB
  | fmap_stop (a : CA)
  | contract
end

mutual
datatype CA
  | recOn (b : CB)
  | stop
datatype CB
  | recOn (a : CA)
  | contract
end

example : CB.recOn .stop ≠ CB.contract := by simp

-- A lemma generated from another constructor: injectivity, disjointness, a rule.
/--
error: constructor `a_inj` clashes with the generated declaration `FrontEndTest.C7.a_inj` (injectivity of `FrontEndTest.C7.a`); rename the constructor
-/
#guard_msgs in
codatatype C7
  | a (t : C7)
  | a_inj

/--
error: constructor `a_ne_b` clashes with the generated declaration `FrontEndTest.Cmd.a_ne_b` (disjointness of `FrontEndTest.Cmd.a` and `FrontEndTest.Cmd.b`); rename the constructor
-/
#guard_msgs in
datatype Cmd
  | a
  | b
  | a_ne_b

/--
error: constructor `fold_a` clashes with the generated declaration `FrontEndTest.Cmd.fold_a`; rename the constructor
-/
#guard_msgs in
datatype Cmd
  | a
  | fold_a

-- The functor's constructor named as a one-step lemma of the lifting, or as a rule of the map.
/--
error: constructor `rel_a_b` clashes with the generated declaration `FrontEndTest.Cmd.F.rel_a_b` (one step of `FrontEndTest.Cmd.F.Rel` at `FrontEndTest.Cmd.a` and `FrontEndTest.Cmd.b`): the functor `FrontEndTest.Cmd.F` has a constructor `FrontEndTest.Cmd.F.rel_a_b` for it; rename the constructor
-/
#guard_msgs in
codatatype Cmd
  | a (c : Cmd)
  | b
  | rel_a_b

/--
error: constructor `fmap_a` clashes with the generated declaration `FrontEndTest.Cmd.F.fmap_a`: the functor `FrontEndTest.Cmd.F` has a constructor `FrontEndTest.Cmd.F.fmap_a` for it; rename the constructor
-/
#guard_msgs in
datatype Cmd
  | a (n : Nat)
  | fmap_a

-- A rule of a constructor named as a fixed declaration: of the type, or a law of the map.
/--
error: constructor `inj` clashes with the generated declaration `FrontEndTest.Cmd.dtor_inj`: a rule of `FrontEndTest.Cmd.inj` would have this name too; rename the constructor
-/
#guard_msgs in
datatype Cmd
  | inj (n : Nat)

/--
error: constructor `id` clashes with the generated declaration `FrontEndTest.Cmd.F.fmap_id`, a law of `FrontEndTest.Cmd.F.fmap`: the rule of `FrontEndTest.Cmd.F.fmap` at `FrontEndTest.Cmd.id` would have this name too; rename the constructor
-/
#guard_msgs in
codatatype Cmd
  | id (c : Cmd)
  | stop

-- Two generated declarations with one name.
/--
error: constructors `b` and `b_ne` give two generated declarations the name `FrontEndTest.Cmd.b_ne_ne_b`: disjointness of `FrontEndTest.Cmd.b` and `FrontEndTest.Cmd.ne_b`, and disjointness of `FrontEndTest.Cmd.b_ne` and `FrontEndTest.Cmd.b`; rename one of them
-/
#guard_msgs in
datatype Cmd
  | b
  | b_ne
  | ne_b

-- Names close to the generated ones, and `a_inj` next to an `a` without arguments, which has
-- no injectivity lemma.
datatype Near
  | a (n : Nat)
  | a_in
  | b
  | ne_b
  | inj_a
  | c
  | c_inj

example : Near.a 1 ≠ Near.a_in := by simp
example (m n : Nat) : Near.a m = Near.a n ↔ m = n := Near.a_inj m n
example : Near.c ≠ Near.c_inj := by simp

-- In a `mixed_mutual` block, the closed type of an inner run restates the open type as `T.Open`.
/--
error: constructor `Open` clashes with the generated declaration `FrontEndTest.XF.Open`; rename the constructor
-/
#guard_msgs in
mixed_mutual
codatatype XT
  | node (f : XF)
datatype XF
  | nil
  | Open (t : XT)
end

-- And the membership lemmas of its constructors and its instances of membership.
/--
error: constructor `mem_cons` clashes with the generated declaration `FrontEndTest.XF.mem_cons` (membership in `FrontEndTest.XF.cons`); rename the constructor
-/
#guard_msgs in
mixed_mutual
codatatype XT
  | node (f : XF)
datatype XF
  | nil
  | cons (t : XT) (f : XF)
  | mem_cons
end

/--
error: constructor `instMembershipXT` clashes with the generated declaration `FrontEndTest.XF.instMembershipXT` (membership of `XT` in `FrontEndTest.XF`); rename the constructor
-/
#guard_msgs in
mixed_mutual
codatatype XT
  | node (f : XF)
datatype XF
  | nil
  | cons (t : XT) (f : XF)
  | instMembershipXT
end

/--
error: Cannot define multiple constructors with the same name `FrontEndTest.Bad.mk`
---
error: Cannot define multiple constructors with the same name `FrontEndTest.Bad.mk`
-/
#guard_msgs in
codatatype Bad
  | mk
  | mk

/-- error: Unknown identifier `Bad` -/
#guard_msgs in #check Bad

/-! ### `data` and `codata` are not keywords

The commands are `datatype` and `codatatype`; `data` and `codata` stay free for identifiers. -/

def foo (data : Nat) := data
def bar (codata : Nat) := codata

example : foo 1 + bar 2 = 3 := rfl

end FrontEndTest
