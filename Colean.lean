-- This module serves as the root of the `Colean` library.
-- Import modules here that should be built as part of the library.
import Colean.Raw
import Colean.Framework
import Colean.PolyIso
import Colean.Model.Cotype
import Colean.Model.Intype
import Colean.Model.Occ
import Colean.Cmd.Analysis
import Colean.Cmd.Functor
import Colean.Cmd.Model
import Colean.Cmd.Framework
import Colean.Cmd.Extras
import Colean.Cmd.Surface
import Colean.CodataCmd
import Colean.DataCmd
import Colean.MutualCmd

/-!
# (Co)inductive types as subtypes of one general type
The framework (`Framework`), the user interface for nesting (`PolyIso`), the model (`Model/`),
the command generators by step (`Cmd/`), the `codata` and `data` commands (`CodataCmd`,
`DataCmd`) and their mutual blocks (`MutualCmd`). The tests are the separate library
`ColeanTest`. The decomposition is described in `architecture.md`.
-/
