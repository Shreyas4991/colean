import Colean.MutualCmd

/-! # Test: the info tree

The names of the types and the constructors, where the declaration writes them, carry the
declarations they name, as with `inductive`: for hovering and go-to-definition. -/

open Lean Elab Command

namespace InfoTest

/-- The constants that the declaration `src` names where it is written. -/
def declaredInfo (src : String) : CommandElabM (Array Name) := do
  let .ok stx := Parser.runParserCategory (← getEnv) `command src
    | throwError "parse error"
  let trees ← withoutModifyingEnv do
    modifyInfoState fun s => { s with enabled := true, trees := {} }
    elabCommand stx
    return (← getInfoState).trees
  return trees.foldl (init := #[]) fun out t => t.foldInfo (init := out) fun _ i acc =>
    match i with
    | .ofTermInfo ti => if ti.isBinder && ti.expr.isConst then acc.push ti.expr.constName! else acc
    | _ => acc

/-- info: [InfoTest.A, InfoTest.A.nil, InfoTest.A.cons] -/
#guard_msgs in
run_cmd do logInfo m!"{← declaredInfo "codatatype A (α : Type) | nil | cons (a : α) (t : A α)"}"

/-- info: [InfoTest.E, InfoTest.O, InfoTest.E.z, InfoTest.E.s, InfoTest.O.s] -/
#guard_msgs in
run_cmd do logInfo m!"{← declaredInfo "mutual\n datatype E | z | s (o : O)\n datatype O | s (e : E)\nend"}"

end InfoTest
