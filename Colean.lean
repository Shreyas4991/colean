-- This module serves as the root of the `Colean` library.
-- Import modules here that should be built as part of the library.
import Colean.Dependencies
import Colean.Raw
import Colean.Framework
import Colean.PolyIso
import Colean.Model.Cotype
import Colean.Model.Intype
import Colean.Model.Occ
import Colean.Model.Poly
import Colean.Model.Occ2
import Colean.Model.IOcc2
import Colean.Model.CCPO
import Colean.Syntax
import Colean.Gen.Decl
import Colean.Gen.Occ
import Colean.Gen.Ctx
import Colean.Gen.Front
import Colean.Gen.Functor
import Colean.Gen.Signature
import Colean.Gen.Iso
import Colean.Gen.Rel
import Colean.Gen.Model
import Colean.Gen.Framework
import Colean.Gen.Extras
import Colean.Gen.Surface
import Colean.Gen.Derive
import Colean.Gen.Command
import Colean.Gen.Mixed
import Colean.Gen.CCPO
import Colean.CodataCmd
import Colean.DataCmd
import Colean.MutualCmd

/-!
# (Co)inductive types as subtypes of one general type
The library depends on Lean core only: what it needs from Mathlib and Batteries is copied, under
their names in the namespace `Colean`, into `Dependencies/`.
The framework (`Framework`), the user interface for nesting (`PolyIso`), the model (`Model/`),
the command syntax (`Syntax`), the command generators by step, on `Expr` (`Gen/`), the `codatatype`
and `datatype` commands (`CodataCmd`, `DataCmd`) and their mutual and mixed blocks (`MutualCmd`),
and the attribute `with_ccpo` for `partial_fixpoint` (`Model/CCPO`, `Gen/CCPO`, `CodataCmd`).
The tests are the separate library `ColeanTest`. The decomposition is described in
`architecture.md`.
-/
