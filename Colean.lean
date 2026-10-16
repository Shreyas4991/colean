-- This module serves as the root of the `Colean` library.
-- Import modules here that should be built as part of the library.
import Colean.Raw
import Colean.Codata
import Colean.CodataCmd
import Colean.Data
import Colean.DataCmd
import Colean.Test.Alt
import Colean.Test.Bounded
import Colean.Test.BTree
import Colean.Test.CoList
import Colean.Test.CoNat
import Colean.Test.Cyc
import Colean.Test.Diag
import Colean.Test.ITree
import Colean.Test.PList
import Colean.Test.PTree
import Colean.Test.Str
import Colean.Test.Tele
import Colean.Test.Tree
import Colean.Test.Vec
import Colean.Test.Walk
import Colean.Test.FinList
import Colean.Test.FinTree
import Colean.Test.FinVec
import Colean.Test.LeT
import Colean.Test.Nat
import Colean.Test.WType

/-!
# (Co)inductive types as subtypes of one general type
The generic theory (`Codata`, `Data`), the `codata` and `data` commands (`CodataCmd`,
`DataCmd`) and the tests (one type per file in `Test/`).
-/
