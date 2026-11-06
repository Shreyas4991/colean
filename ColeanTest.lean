-- The tests of the `Colean` library, one type per file.
import ColeanTest.Alt
import ColeanTest.Bounded
import ColeanTest.BTree
import ColeanTest.CoList
import ColeanTest.CoNat
import ColeanTest.Cyc
import ColeanTest.Diag
import ColeanTest.ITree
import ColeanTest.PList
import ColeanTest.PTree
import ColeanTest.Str
import ColeanTest.Tele
import ColeanTest.Tree
import ColeanTest.Vec
import ColeanTest.Walk
import ColeanTest.FinList
import ColeanTest.FinTree
import ColeanTest.FinVec
import ColeanTest.LeT
import ColeanTest.Nat
import ColeanTest.WType
import ColeanTest.MTree
import ColeanTest.MRose
import ColeanTest.EvenOdd
import ColeanTest.Rose
import ColeanTest.FinRose
import ColeanTest.OccNest
import ColeanTest.Nest
import ColeanTest.Names
import ColeanTest.MixedRejected
-- These nest through declared types, which needs `PolyIso` instances for them: `mixed_mutual`
-- cannot be given such instances by hand, so they wait for the generation of the instances.
-- import ColeanTest.Param
-- import ColeanTest.Mixed
-- import ColeanTest.MixedOrder
-- import ColeanTest.MixedRuns
