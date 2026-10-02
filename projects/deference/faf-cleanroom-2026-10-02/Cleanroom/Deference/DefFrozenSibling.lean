import Cleanroom.Deference.DefFrozenSibling.Defs
import Cleanroom.Deference.DefFrozenSibling.Computable
import Cleanroom.Deference.DefFrozenSibling.Gated
import Cleanroom.Deference.DefFrozenSibling.Tracking
import Cleanroom.Deference.DefFrozenSibling.Engine
import Cleanroom.Deference.DefFrozenSibling.Limits
import Cleanroom.Deference.DefFrozenSibling.Value
import Cleanroom.Deference.DefFrozenSibling.Misc
import Cleanroom.Deference.DefFrozenSibling.OffG
import Cleanroom.Deference.DefFrozenSibling.OnG

/-!
# `def-frozen-sibling` — root module

The sealed-sibling (frozen-deliberation) construction and the timely fragment
([[def-frozen-sibling-mandate]]): `Defs` (the carrier `FrozenSystem` and the fragments defined
from the processes), `Computable` (membership in `G` as a computable function of the day; repair
round 1), `Gated` (provability induction along an e.c. sub-fragment), `Tracking` (T1,
T2), `Engine` (T3 both sides), `Limits` (T7), `Value` (T4), `Misc` (T6, T12, T13, F5, F6), `OffG`
(T5, the counter-model, the open statements of record; imports the LIA compiler), `OnG` (the
one-way inhabitant at a timely day, N+ for the on-`G` suite; imports `OffG`). Report: [[def-frozen-sibling-report]]; ledger: [[def-frozen-sibling-ledger]];
findings: [[def-frozen-sibling-findings]].
-/
