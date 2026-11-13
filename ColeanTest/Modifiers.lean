import Colean.MutualCmd

/-! # Test: modifiers, as on `inductive`

A declaration is parsed as `inductive` is, its keyword swapped: doc comments, attributes,
`private`, `protected` and `noncomputable` on the type and on the constructors, universe names
`T.{u}` and `where`, in single declarations, `mutual` blocks and `mixed_mutual` blocks. Doc
comments and attributes are added once everything is declared; a `private` type makes everything
generated from it private, its block included. `unsafe`, `partial`, `meta`, `deriving`, a
`private` constructor, and a block mixing `private` and public types are rejected. -/

universe u

open Lean

namespace ModTest

/-- The doc string of `n`, if any. -/
def doc (n : Name) : MetaM (Option String) := do
  findDocString? (← getEnv) n

/-- Is the constant that `id` names private? -/
def priv (id : Ident) : MetaM Bool := do
  return isPrivateName (← resolveGlobalConstNoOverload id)

/-! ### Doc comments -/

/-- A stream that may stop. -/
codata DS (α : Type)
  /-- The end. -/
  | nil
  | /-- One more. -/ cons (a : α) (t : DS α)

/-- info: (some "A stream that may stop.", some "The end.", some "One more.") -/
#guard_msgs in
#eval return (← doc ``DS, ← doc ``DS.nil, ← doc ``DS.cons)

-- Both forms on one constructor: Lean's error, and the declaration goes on with the one before
-- the `|`.
/-- error: Duplicate doc string -/
#guard_msgs in
data DD
  /-- One. -/
  | /-- Two. -/ mk

/-- info: some "One." -/
#guard_msgs in #eval doc ``DD.mk

mutual
/-- Even numbers. -/
data DE
  | z
  /-- The successor of an odd number. -/
  | s (o : DO)
/-- Odd numbers. -/
data DO
  | s (e : DE)
end

/--
info: (some "Even numbers.", some "Odd numbers.", some "The successor of an odd number.")
-/
#guard_msgs in #eval return (← doc ``DE, ← doc ``DO, ← doc ``DE.s)

mixed_mutual
/-- Finitely branching trees. -/
codata DT (α : Type u)
  | node (a : α) (children : DF α)
/-- Finite forests. -/
data DF (α : Type u)
  | nil
  /-- A tree and a forest. -/
  | cons (t : DT α) (f : DF α)
end

/--
info: (some "Finitely branching trees.", some "Finite forests.", some "A tree and a forest.")
-/
#guard_msgs in #eval return (← doc ``DT, ← doc ``DF, ← doc ``DF.cons)

/-! ### Attributes -/

@[deprecated "use `DS`" (since := "2026-11-13")]
codata Old
  | a
  | @[deprecated "use `b`" (since := "2026-11-13")] c
  | b

/--
warning: `ModTest.Old` has been deprecated: use `DS`
---
info: Old : Type
-/
#guard_msgs in #check (Old)

/-- warning: `ModTest.Old.c` has been deprecated: use `b` -/
#guard_msgs in noncomputable example := Old.c

/-! ### `protected` -/

namespace P

/-- A protected type, referred to by its qualified name, as with `inductive`. -/
protected codata PT
  | stop
  | go (t : P.PT)

end P

/-- A protected constructor. -/
codata PC
  | protected stop
  | go (t : PC)

namespace Q

mutual
/-- Protected types of a block. -/
protected data QE
  | z
  | s (o : Q.QO)
protected data QO
  | s (e : Q.QE)
end

end Q

section
open P PC Q

/-- error: Unknown identifier `PT` -/
#guard_msgs in #check PT

/-- error: Unknown identifier `QO` -/
#guard_msgs in #check QO

/-- info: ModTest.Q.QE.s (o : Q.QO) : Q.QE -/
#guard_msgs in #check Q.QE.s

/-- error: Unknown identifier `stop` -/
#guard_msgs in #check stop

/-- info: ModTest.PC.go (t : PC) : PC -/
#guard_msgs in #check go

/-- info: ModTest.P.PT.go (t : P.PT) : P.PT -/
#guard_msgs in #check P.PT.go

end

/-! ### `private` -/

private codata PS (α : Type)
  | nil
  | cons (a : α) (t : PS α)

/-- info: [true, true, true, true, true] -/
#guard_msgs in
#eval [mkIdent `PS, mkIdent `PS.cons, mkIdent `PS.corec, mkIdent `PS.F, mkIdent `PS.dtor_cons].mapM
  priv

theorem PS.cons_ne (a : α) (t : PS α) : PS.cons a t ≠ .nil := by simp

private data PV (α : Type) : Nat → Type
  | nil : PV α 0
  | cons {n : Nat} (a : α) (v : PV α n) : PV α (n + 1)

/-- info: [true, true, true] -/
#guard_msgs in #eval [mkIdent `PV, mkIdent `PV.rec, mkIdent `PV.Shape].mapM priv

example (v : PV α n) : True := by induction v <;> trivial

mutual
private data PE
  | z
  | s (o : PO)
private data PO
  | s (e : PE)
end

/-- info: [true, true, true, true, true] -/
#guard_msgs in
#eval [mkIdent `PE, mkIdent `PE_PO, mkIdent `PE_PO.Ix, mkIdent `PE_PO.Ix.PE, mkIdent `PO.rec].mapM
  priv

example : PE.s (PO.s PE.z) ≠ PE.z := by simp

mixed_mutual
private codata PTr (α : Type u)
  | node (a : α) (children : PFo α)
private data PFo (α : Type u)
  | nil
  | cons (t : PTr α) (f : PFo α)
end

/-- info: [true, true, true, true, true] -/
#guard_msgs in
#eval [mkIdent `PTr, mkIdent `PFo, mkIdent `PFo.Open, mkIdent `PFo.rec, mkIdent `PTr.corec].mapM
  priv

/-- info: @PFo.cons : {α : Type u_1} → PTr α → PFo α → PFo α -/
#guard_msgs in #check @PFo.cons

-- A private block of two types inside a mixed block: its name and open name private too.
mixed_mutual
private codata QT (α : Type u)
  | node (a : α) (r : QR α)
private data QR (α : Type u)
  | node (t : QT α) (f : QF α)
private data QF (α : Type u)
  | nil
  | cons (r : QR α) (f : QF α)
end

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval [mkIdent `QR_QF, mkIdent `QR_QF.Open, mkIdent `QR_QF.Ix, mkIdent `QF.rec].mapM priv

@[with_ccpo]
private codata PR (α : Type)
  | stop
  | cons (a : α) (t : PR α)

/-- info: [true, true] -/
#guard_msgs in #eval [mkIdent `PR.instCCPO, mkIdent `PR.bot_eq].mapM priv

noncomputable def PR.const (a : Nat) : PR Nat := .cons a (const a)
partial_fixpoint

private codata PR2
  | stop
  | next (t : PR2)

attribute [with_ccpo] PR2

/-! ### Universe names, `where`, `noncomputable` -/

codata UT.{v} (α : Type v)
  | nil
  | cons (a : α) (t : UT α)

/-- info: ModTest.UT.{v} (α : Type v) : Type v -/
#guard_msgs in #check UT

mutual
data UE.{v} (α : Type v)
  | z (a : α)
  | s (o : UO α)
data UO.{v} (α : Type v)
  | s (e : UE α)
end

/-- info: ModTest.UO.{v} (α : Type v) : Type v -/
#guard_msgs in #check UO

data WL (α : Type) where
  | nil
  | cons (a : α) (t : WL α)

/-- info: @WL.cons : {α : Type} → α → WL α → WL α -/
#guard_msgs in #check @WL.cons

noncomputable codata NC
  | a

/-! ### Rejected -/

/-- error: `unsafe` is not supported by `codata` -/
#guard_msgs in
unsafe codata EU
  | a

/-- error: `partial` is not supported by `data` -/
#guard_msgs in
partial data EP
  | a

/-- error: `meta` is not supported by `data` -/
#guard_msgs in
meta data EM
  | a

/-- error: `deriving` is not supported by `codata` -/
#guard_msgs in
codata ED
  | a
  deriving Inhabited

/-- error: `unsafe` is not supported by `codata` -/
#guard_msgs in
codata ECU
  | unsafe a

/--
error: Constructor cannot be marked `private` because it is already in a `private` inductive datatype
-/
#guard_msgs in
private codata EPP
  | private a

/-- error: Constructor cannot be `protected` because it is in a `private` inductive datatype -/
#guard_msgs in
private codata EPQ
  | protected a

/--
error: a `private` constructor of a public type is not supported by `codata`: the declarations about the constructor are named after the type, and would be public; make the type `private`
-/
#guard_msgs in
codata EPC
  | private a

/--
error: the types of a block must be all `private` or all public, and `EMB` is not `private` while `EMA` is: the block's own declarations, its name and its index, are private or not with them
-/
#guard_msgs in
mutual
private data EMA
  | z
  | s (o : EMB)
data EMB
  | s (e : EMA)
end

/-- error: the types of a block must have the same universe names as `EUA` -/
#guard_msgs in
mutual
data EUA.{v} (α : Type v)
  | z
  | s (o : EUB α)
data EUB.{w} (α : Type w)
  | s (e : EUA α)
end

-- A binder without a type, as in `inductive`.
/-- error: Failed to infer type of binder `x` -/
#guard_msgs in
data EB
  | mk x

/-- error: a `mixed_mutual` block must consist of `codata` and `data` declarations only -/
#guard_msgs in
mixed_mutual
codata EX
  | a
def ex := 1
end

end ModTest
