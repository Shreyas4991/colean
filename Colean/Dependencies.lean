import Colean.Dependencies.FromMathlib.Equiv
import Colean.Dependencies.FromMathlib.ListOfFn
import Colean.Dependencies.FromBatteries.Forall2
import Colean.Dependencies.FromMathlib.Forall2

/-!
# What Colean uses from Mathlib and Batteries

Colean depends on Lean core only. The few definitions and theorems it needs from Mathlib and
Batteries are copied into `Dependencies/FromMathlib/` and `Dependencies/FromBatteries/`, with
Mathlib's and Batteries' names, arguments and statements, in the namespace `Colean`: equivalences
(`Colean.Equiv`, notation `≃` after `open Colean`), lists as tuples
(`Colean.List.equivSigmaTuple`), and the relation of two lists elementwise
(`Colean.List.Forall₂`) with its `simp` lemmas.
-/
