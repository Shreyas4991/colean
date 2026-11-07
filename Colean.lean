-- This module serves as the root of the `Colean` library.
-- Import modules here that should be built as part of the library.
import Colean.Raw
import Colean.Framework
import Colean.PolyIso
import Colean.Model.Cotype
import Colean.Model.Intype
import Colean.Model.Occ
import Colean.Model.Poly
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
import Colean.CodataCmd
import Colean.DataCmd
import Colean.MutualCmd

/-!
# (Co)inductive types as subtypes of one general type
The framework (`Framework`), the user interface for nesting (`PolyIso`), the model (`Model/`),
the command syntax (`Syntax`), the command generators by step, on `Expr` (`Gen/`), the `codata`
and `data` commands (`CodataCmd`, `DataCmd`) and their mutual blocks (`MutualCmd`). The tests are
the separate library `ColeanTest`. The decomposition is described in `architecture.md`.
-/
