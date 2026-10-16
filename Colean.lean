-- This module serves as the root of the `Colean` library.
-- Import modules here that should be built as part of the library.
import Colean.Raw
import Colean.Framework
import Colean.Model.Cotype
import Colean.Model.Intype
import Colean.Model.Occ
import Colean.Model.Param
import Colean.Cmd.Analysis
import Colean.Cmd.Functor
import Colean.Cmd.Model
import Colean.Cmd.Framework
import Colean.Cmd.Extras
import Colean.Cmd.Surface
import Colean.CodataCmd
import Colean.DataCmd
import Colean.MutualCmd
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
import Colean.Test.MTree
import Colean.Test.MRose
import Colean.Test.EvenOdd
import Colean.Test.Rose
import Colean.Test.FinRose
import Colean.Test.Param
import Colean.Test.Mixed
import Colean.Test.MixedOrder
import Colean.Test.MixedRuns
import Colean.Test.OccNest
-- import Colean.Sketch.CoList
-- import Colean.Sketch.CoListLemmas
-- import Colean.Sketch.FinList
-- import Colean.Sketch.FinTree
-- import Colean.Sketch.IdxCyc
-- import Colean.Sketch.IdxVec
-- import Colean.Sketch.ITree
-- import Colean.Sketch.ITreeLemmas
-- import Colean.Sketch.Mutual
-- import Colean.Sketch.StrArith
-- import Colean.Sketch.Str
-- import Colean.Sketch.StrLemmas
-- import Colean.Sketch.Tree
-- import Colean.Sketch.TreeLemmas
-- import Colean.Sketch.Vec

/-!
# (Co)inductive types as subtypes of one general type
The framework (`Framework`), the model (`Model/`), the command generators by step (`Cmd/`),
the `codata` and `data` commands (`CodataCmd`, `DataCmd`) and their mutual blocks (`MutualCmd`),
the tests (one type per file in `Test/`) and the hand-written sketches that preceded the commands
(`Sketch/`). The decomposition is described in `architecture.md`.
-/
