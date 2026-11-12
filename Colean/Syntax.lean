import Lean

/-!
# The syntax of the commands

The `codata` and `data` declarations, elaborated by `CodataCmd.lean` and `DataCmd.lean` through
the generators of `Gen/`, and read by the blocks of `MutualCmd.lean`, which elaborates the
`mixed_mutual` blocks too; the attribute `with_ccpo` (`CodataCmd.lean`), and attributes written
before a `codata` declaration.
-/

open Lean Parser.Term

namespace Codata

/-- A constructor of a `codata` declaration: a name, binders `(x y : A)` or `{x y : A}`, and
optionally its result type `T params idx`. -/
syntax codataCtor := "| " ident (ppSpace bracketedBinder)* (" : " term)?

/-- `codata T (params) [: (i₁ : I₁) → I₂ → Type u] | ctor₁ … | ctor₂ …` declares a coinductive
type, or family, as a subtype of `Raw`. -/
syntax (name := codataCmd) "codata " ident (ppSpace bracketedBinder)* (" : " term)?
  codataCtor* : command

/-- `data T (params) [: (i₁ : I₁) → I₂ → Type u] | ctor₁ … | ctor₂ …` declares an inductive
type, or family, as a subtype of `Raw`. -/
syntax (name := dataCmd) "data " ident (ppSpace bracketedBinder)* (" : " term)?
  codataCtor* : command

/-- `mixed_mutual … end`: a block of `codata` and `data` declarations nested in the order written,
the first outermost (`MutualCmd.lean`). -/
syntax (name := mixedMutualCmd) "mixed_mutual" (ppLine (codataCmd <|> dataCmd))+
  ppDedent(ppLine "end") : command

/-- `with_ccpo`, or `with_ccpo c`: the order of approximation on a `codata` type, with the
constructor `c` without arguments at the bottom (by default the first one), as Lean's
`Lean.Order.CCPO`, and the monotonicity lemmas of the constructors, so that corecursive functions
into the type can be defined by `partial_fixpoint` (`Gen/CCPO.lean`). Applied after the
declaration, `attribute [with_ccpo] T`, or written before it, `@[with_ccpo] codata T …`. -/
syntax (name := with_ccpo) "with_ccpo" (ppSpace ident)? : attr

/-- `@[attrs] codata T …`: the declaration, then `attribute [attrs] T` (for `with_ccpo`). -/
syntax (name := codataAttrCmd) Parser.Term.attributes ppSpace codataCmd : command

/-- The binders of a declaration are its interface: the unused-variables linter skips them, as
it does for `inductive`. -/
@[unused_variables_ignore_fn]
def ignoreDeclBinders : Lean.Linter.IgnoreFunction := fun _ stack _ =>
  stack.any fun (stx, _) => stx.isOfKind ``codataCmd || stx.isOfKind ``dataCmd

end Codata
