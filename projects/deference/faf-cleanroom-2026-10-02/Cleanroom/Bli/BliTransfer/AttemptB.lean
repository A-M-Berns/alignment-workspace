import Cleanroom.Bli.BliTransfer.AttemptB.Defs
import Cleanroom.Bli.BliTransfer.AttemptB.Splice
import Cleanroom.Bli.BliTransfer.AttemptB.Transfer
import Cleanroom.Bli.BliTransfer.AttemptB.Restricted
import Cleanroom.Bli.BliTransfer.AttemptB.Witnesses
import Cleanroom.Bli.BliTransfer.AttemptB.Certificate
import Cleanroom.Bli.BliTransfer.AttemptB.OracleBridge
import Cleanroom.Bli.BliTransfer.AttemptB.WitnessMap
import Cleanroom.Bli.BliTransfer.AttemptB.Clamp
import Cleanroom.Bli.BliTransfer.AttemptB.SmallCode
import Cleanroom.Bli.BliTransfer.AttemptB.Computable
import Cleanroom.Bli.BliTransfer.AttemptB.WitnessLia

/-!
# `bli-transfer` · attempt B (angle B: the splice-stream route)

Root module of attempt B of the dual package `bli-transfer` (area `bli`, namespace
`Cleanroom.Bli.BliTransfer.AttemptB`). Angle B certifies the splice on the class of traders
*presented* by FAF's `MachineSpliceStream.serialize_*` combinators (`SpliceBuilt`,
`SpliceBuiltTrader`): a run-level `FP` oracle (`SpliceOracle`, spelling-quantified) rewrites
each presented price leaf (`SpliceOracle.spliceLeaf_machineSpliceStream`), so the splice of a
presented trader is efficiently computable and no presented trader exploits the overlay
(`overlay_noExploit_spliceBuilt`, kind `C`, `(c)` the class). The criterion-level statement is
`overlay_isLogicalInductor_of_transfer` with the transfer for every e.c. trader as its
hypothesis. Shared with angle A: the definitions of record (`Defs`), the rewrite and its laws
(`Splice`), the accounting (`Transfer`), T2 (`Restricted`, `Witnesses`). Angle B's further
results: FAF's freeze oracle is a splice oracle (`OracleBridge`), the non-vacuity package at the
LIA (`WitnessMap`, `WitnessLia`), T3 refuted (`Clamp`: the clamped market is never a logical
inductor; e.c. magnitude is not `2^{poly}`), and T1.4 with the smallness test on codes certified
(`SmallCode`, `Computable`; no OPEN statement).

Deliverables: `run/wp/bli-transfer/attempt-b/` (report, findings, ledger) and
`run/wp/bli-transfer/bli-transfer-B-open.txt`.
-/
