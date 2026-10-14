import Lean
import Qq
import Lean.Elab.Coinductive

open Lean Parser Command
open Lean.Elab.Command

/-!
  `inductive_with_todo` — behaves exactly like `inductive` but always appends a
  nullary constructor `todo` to the type, i.e.

  ```lean
  inductive_with_todo Foo
  | bar : Foo
  ```

  is equivalent to

  ```lean
  inductive Foo
  | bar  : Foo
  | todo : Foo
  ```
-/

/--
  Syntax for `inductive_with_todo`.

  Structure mirrors `Lean.Parser.Command.inductive`:
  ```
  "inductive " >> declId >> optDeclSig >> optional(":=" | "where") >>
  many ctor >> optional computedFields >> optDeriving
  ```
  We use the same positional layout so that the args array is compatible when
  we re-tag the node as `Lean.Parser.Command.inductive` below.
-/
syntax (name := inductiveWithTodo)
    "inductive_with_todo " declId optDeclSig
    (" where")? ctor* optDeriving : command

/--
  Core inductive elaboration hook.
  Constructs an `InductiveElabStep1` identical to what the standard `inductive`
  elaborator would produce, except that a synthetic `todo` constructor (no
  arguments, no explicit return type) is appended to the constructor list.
-/
@[inductive_elab inductiveWithTodo]
def elabInductiveWithTodoDescr : InductiveElabDescr where
  mkInductiveView modifiers stx := do
    /-
      Our `inductiveWithTodo` syntax has the following child layout:
        [0]  "inductive_with_todo " keyword atom
        [1]  declId
        [2]  optDeclSig
        [3]  (" where")?   — optional keyword
        [4]  ctor*         — many constructors
        [5]  optDeriving

      `Lean.Parser.Command.inductive` expects:
        [0]  "inductive " keyword atom
        [1]  declId
        [2]  optDeclSig
        [3]  optional (":=" | " where")
        [4]  many ctor
        [5]  optional computedFields  (we leave this empty)
        [6]  optDeriving

      We build the args array explicitly so that `inductiveSyntaxToView`
      (called inside `elabInductiveCommand.mkInductiveView`) sees the right
      positions regardless of differences in the leading keyword or the
      missing computedFields slot.
    -/
    let inductiveArgs : Array Syntax := #[
      Syntax.atom .none "inductive ",   -- [0] keyword
      stx[1],                           -- [1] declId
      stx[2],                           -- [2] optDeclSig
      stx[3],                           -- [3] optional " where" (compatible node)
      stx[4],                           -- [4] many ctor
      mkNullNode,                       -- [5] empty optional computedFields
      stx[5]                            -- [6] optDeriving
    ]
    let inductiveStx :=
      Syntax.node .none `Lean.Parser.Command.inductive inductiveArgs
    -- Delegate to the standard inductive elaborator.
    let step1 ← elabInductiveCommand.mkInductiveView modifiers inductiveStx
    -- Build a synthetic CtorView for `todo`.
    -- No `binders` and no `type?` means the constructor has type `T params…`
    -- (i.e. `todo : Foo`, `todo : TodoList α`, etc.).
    let todoRef := stx[1].mkSynthetic   -- reuse declId position, made synthetic
    let todoCtorView : CtorView := {
      ref      := todoRef
      declId   := todoRef
      modifiers := {}
      declName := step1.view.declName ++ `todo
    }
    return { step1 with
      view := { step1.view with ctors := step1.view.ctors.push todoCtorView } }

/-- Command elaborator: dispatch standalone `inductive_with_todo` through the
    standard inductive pipeline (which will invoke `elabInductiveWithTodoDescr`). -/
@[command_elab inductiveWithTodo]
def elabInductiveWithTodoCmd : CommandElab := fun stx =>
  elabInductive {} stx


-- ============================================================
-- Tests
-- ============================================================

inductive_with_todo Foo
| bar : Foo
| baz : Nat → Foo


#check Foo.baz
#check Foo.todo


inductive_with_todo TodoList (α : Type)
| cons : α → TodoList α → TodoList α

#check TodoList.todo
#check TodoList.cons


def TodoList.length (α : Type) (li : TodoList α) : Nat :=
  match li with
  | todo => 0
  | cons hd tl => 1 + tl.length
