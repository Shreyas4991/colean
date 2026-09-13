import MetricCorec.Subtypes.Raw
import MetricCorec.Subtypes.Codata
import MetricCorec.Subtypes.CodataCmd
import MetricCorec.Subtypes.Data
import MetricCorec.Subtypes.DataCmd
import MetricCorec.Subtypes.Test.Alt
import MetricCorec.Subtypes.Test.Bounded
import MetricCorec.Subtypes.Test.BTree
import MetricCorec.Subtypes.Test.CoList
import MetricCorec.Subtypes.Test.CoNat
import MetricCorec.Subtypes.Test.Cyc
import MetricCorec.Subtypes.Test.Diag
import MetricCorec.Subtypes.Test.ITree
import MetricCorec.Subtypes.Test.PList
import MetricCorec.Subtypes.Test.PTree
import MetricCorec.Subtypes.Test.Str
import MetricCorec.Subtypes.Test.Tele
import MetricCorec.Subtypes.Test.Tree
import MetricCorec.Subtypes.Test.Vec
import MetricCorec.Subtypes.Test.Walk
import MetricCorec.Subtypes.Test.FinList
import MetricCorec.Subtypes.Test.FinTree
import MetricCorec.Subtypes.Test.FinVec
import MetricCorec.Subtypes.Test.LeT
import MetricCorec.Subtypes.Test.Nat
import MetricCorec.Subtypes.Test.WType
-- import MetricCorec.Subtypes.Sketch.CoList
-- import MetricCorec.Subtypes.Sketch.CoListLemmas
-- import MetricCorec.Subtypes.Sketch.FinList
-- import MetricCorec.Subtypes.Sketch.FinTree
-- import MetricCorec.Subtypes.Sketch.IdxCyc
-- import MetricCorec.Subtypes.Sketch.IdxVec
-- import MetricCorec.Subtypes.Sketch.ITree
-- import MetricCorec.Subtypes.Sketch.ITreeLemmas
-- import MetricCorec.Subtypes.Sketch.Mutual
-- import MetricCorec.Subtypes.Sketch.StrArith
-- import MetricCorec.Subtypes.Sketch.Str
-- import MetricCorec.Subtypes.Sketch.StrLemmas
-- import MetricCorec.Subtypes.Sketch.Tree
-- import MetricCorec.Subtypes.Sketch.TreeLemmas
-- import MetricCorec.Subtypes.Sketch.Vec

/-!
# (Co)inductive types as subtypes of one general type
The generic theory (`Codata`, `Data`), the `codata` and `data` commands (`CodataCmd`,
`DataCmd`), the tests (one type per file in `Test/`) and the hand-written sketches that preceded
the commands (`Sketch/`).
-/
