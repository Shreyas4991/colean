import Lean

/-!
# The syntax of the commands

The `codata` and `data` declarations, elaborated by `CodataCmd.lean` and `DataCmd.lean` through
the generators of `Gen/`, and read by the blocks of `MutualCmd.lean`, which elaborates the
`mixed_mutual` blocks too; and the attribute `with_ccpo` (`CodataCmd.lean`).

A declaration is parsed as Lean's `inductive`, with its keyword swapped: the modifiers
(`declModifiers`: a doc comment, attributes, `private`, `protected`, …), the name with optional
universe names (`declId`, `T.{u}`), the binders and the declared sort (`optDeclSig`), an
optional `where`, the constructors (Lean's `ctor`, each with its own doc comment and modifiers)
and `deriving`. Computed fields are not part of it. Which modifiers the commands accept is
`DeclStx.elabMods` (`Gen/Front.lean`).
-/

open Lean Parser Command

namespace Codata

/-- `codata T (params) [: (i₁ : I₁) → I₂ → Type u] where | ctor₁ … | ctor₂ …` declares a
coinductive type, or family, as a subtype of `Raw`. -/
syntax (name := codataCmd) declModifiers "codata " declId ppIndent(optDeclSig)
  (" :=" <|> " where")? Lean.Parser.Command.ctor* Lean.Parser.Command.optDeriving : command

/-- `data T (params) [: (i₁ : I₁) → I₂ → Type u] where | ctor₁ … | ctor₂ …` declares an
inductive type, or family, as a subtype of `Raw`. -/
syntax (name := dataCmd) declModifiers "data " declId ppIndent(optDeclSig)
  (" :=" <|> " where")? Lean.Parser.Command.ctor* Lean.Parser.Command.optDeriving : command

/-- The declarations of a `mixed_mutual` block: commands up to `end`, as in `mutual`. Since a
declaration may start with its modifiers, the two commands cannot be told apart by their first
token; the elaborator checks that each is a `codata` or `data` declaration. -/
@[run_parser_attribute_hooks]
def mixedMutualDecls : Parser := many1 (ppLine >> notSymbol "end" >> commandParser)

/-- `mixed_mutual … end`: a block of `codata` and `data` declarations nested in the order written,
the first outermost (`MutualCmd.lean`). -/
syntax (name := mixedMutualCmd) "mixed_mutual" mixedMutualDecls ppDedent(ppLine "end") : command

/-- `with_ccpo`, or `with_ccpo c`: the order of approximation on a `codata` type, with the
constructor `c` without arguments at the bottom (by default the first one), as Lean's
`Lean.Order.CCPO`, and the monotonicity lemmas of the constructors, so that corecursive functions
into the type can be defined by `partial_fixpoint` (`Gen/CCPO.lean`). Applied after the
declaration, `attribute [with_ccpo] T`, or among its modifiers, `@[with_ccpo] codata T …`. -/
syntax (name := with_ccpo) "with_ccpo" (ppSpace ident)? : attr

/-- The binders of a declaration are its interface: the unused-variables linter skips them, as
it does for `inductive`. -/
@[unused_variables_ignore_fn]
def ignoreDeclBinders : Lean.Linter.IgnoreFunction := fun _ stack _ =>
  stack.any fun (stx, _) => stx.isOfKind ``codataCmd || stx.isOfKind ``dataCmd

end Codata
