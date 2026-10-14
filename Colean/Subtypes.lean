import Colean.Subtypes.Raw
import Colean.Subtypes.Framework
import Colean.Subtypes.Model.Cotype
import Colean.Subtypes.Model.Intype
import Colean.Subtypes.Model.Occ
import Colean.Subtypes.Model.Param
import Colean.Subtypes.Cmd.Analysis
import Colean.Subtypes.Cmd.Functor
import Colean.Subtypes.Cmd.Model
import Colean.Subtypes.Cmd.Framework
import Colean.Subtypes.Cmd.Extras
import Colean.Subtypes.Cmd.Surface
import Colean.Subtypes.CodataCmd
import Colean.Subtypes.DataCmd
import Colean.Subtypes.MutualCmd
import Colean.Subtypes.Test.Alt
import Colean.Subtypes.Test.Bounded
import Colean.Subtypes.Test.BTree
import Colean.Subtypes.Test.CoList
import Colean.Subtypes.Test.CoNat
import Colean.Subtypes.Test.Cyc
import Colean.Subtypes.Test.Diag
import Colean.Subtypes.Test.ITree
import Colean.Subtypes.Test.PList
import Colean.Subtypes.Test.PTree
import Colean.Subtypes.Test.Str
import Colean.Subtypes.Test.Tele
import Colean.Subtypes.Test.Tree
import Colean.Subtypes.Test.Vec
import Colean.Subtypes.Test.Walk
import Colean.Subtypes.Test.FinList
import Colean.Subtypes.Test.FinTree
import Colean.Subtypes.Test.FinVec
import Colean.Subtypes.Test.LeT
import Colean.Subtypes.Test.Nat
import Colean.Subtypes.Test.WType
import Colean.Subtypes.Test.MTree
import Colean.Subtypes.Test.MRose
import Colean.Subtypes.Test.EvenOdd
import Colean.Subtypes.Test.Rose
import Colean.Subtypes.Test.FinRose
import Colean.Subtypes.Test.Param
import Colean.Subtypes.Test.Mixed
import Colean.Subtypes.Test.MixedOrder
import Colean.Subtypes.Test.MixedRuns
import Colean.Subtypes.Test.OccNest
-- import Colean.Subtypes.Sketch.CoList
-- import Colean.Subtypes.Sketch.CoListLemmas
-- import Colean.Subtypes.Sketch.FinList
-- import Colean.Subtypes.Sketch.FinTree
-- import Colean.Subtypes.Sketch.IdxCyc
-- import Colean.Subtypes.Sketch.IdxVec
-- import Colean.Subtypes.Sketch.ITree
-- import Colean.Subtypes.Sketch.ITreeLemmas
-- import Colean.Subtypes.Sketch.Mutual
-- import Colean.Subtypes.Sketch.StrArith
-- import Colean.Subtypes.Sketch.Str
-- import Colean.Subtypes.Sketch.StrLemmas
-- import Colean.Subtypes.Sketch.Tree
-- import Colean.Subtypes.Sketch.TreeLemmas
-- import Colean.Subtypes.Sketch.Vec

/-!
# (Co)inductive types as subtypes of one general type
The framework (`Framework`), the model (`Model/`), the command generators by step (`Cmd/`),
the `codata` and `data` commands (`CodataCmd`, `DataCmd`) and their mutual blocks (`MutualCmd`),
the tests (one type per file in `Test/`) and the hand-written sketches that preceded the commands
(`Sketch/`). The decomposition is described in `architecture.md`.
-/
