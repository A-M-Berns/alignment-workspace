import Cleanroom.Corrigibility.CorrLegitGeneral.Defs
import Cleanroom.Corrigibility.CorrLegitGeneral.Transfer
import Cleanroom.Corrigibility.CorrLegitGeneral.Reflection
import Cleanroom.Corrigibility.CorrLegitGeneral.Locality
import Cleanroom.Corrigibility.CorrLegitGeneral.LocalValue
import Cleanroom.Corrigibility.CorrLegitGeneral.Eval
import Cleanroom.Corrigibility.CorrLegitGeneral.WitnessesFn66
import Cleanroom.Corrigibility.CorrLegitGeneral.TwoCell
import Cleanroom.Corrigibility.CorrLegitGeneral.ThreeCell
import Cleanroom.Corrigibility.CorrLegitGeneral.ThreeCellRefuted
import Cleanroom.Corrigibility.CorrLegitGeneral.ThreeCellRefutedFull
import Cleanroom.Corrigibility.CorrLegitGeneral.Betweenness
import Cleanroom.Corrigibility.CorrLegitGeneral.BetweennessDiagonal
import Cleanroom.Corrigibility.CorrLegitGeneral.WitnessesTieFull
import Cleanroom.Corrigibility.CorrLegitGeneral.Vacuity
import Cleanroom.Corrigibility.CorrLegitGeneral.Compose
import Cleanroom.Corrigibility.CorrLegitGeneral.WitnessesCompose
import Cleanroom.Corrigibility.CorrLegitGeneral.WitnessesComposeEvent
import Cleanroom.Corrigibility.CorrLegitGeneral.WitnessesLeak
import Cleanroom.Corrigibility.CorrLegitGeneral.WitnessesFn50
import Cleanroom.Corrigibility.CorrLegitGeneral.WitnessesReflectVisible
import Cleanroom.Corrigibility.CorrLegitGeneral.Extreme
import Cleanroom.Corrigibility.CorrLegitGeneral.Mutual
import Cleanroom.Corrigibility.CorrLegitGeneral.WitnessesMutualSmall
import Cleanroom.Corrigibility.CorrLegitGeneral.Informed
import Cleanroom.Corrigibility.CorrLegitGeneral.Channel
import Cleanroom.Corrigibility.CorrLegitGeneral.Fact21
import Cleanroom.Corrigibility.CorrLegitGeneral.Fact21TwoCell
import Cleanroom.Corrigibility.CorrLegitGeneral.TrustAttained
import Cleanroom.Corrigibility.CorrLegitGeneral.Fact21Trust
import Cleanroom.Corrigibility.CorrLegitGeneral.Imports
import Cleanroom.Corrigibility.CorrLegitGeneral.CorrFrame

/-!
# corr-legit-general — root module

Legitimacy-conditioned Total Trust and its DDB shape (faf-cleanroom run, 2026-10-01; repair
rounds 1–3 the same day). Files: `Defs` (criterion of record), `Transfer` (T1, T5), `Reflection`
(T2), `Locality` (T3), `LocalValue` (T4(a)–(b)), `Eval` (finite evaluation helpers),
`WitnessesFn66` (fn 66, the tie refutation), `TwoCell` (the surviving two-cell Value theorem),
`ThreeCell` (fn 65: the literal refutation at two cells; the finest-question case; the index of
how the conjecture was settled), `ThreeCellRefuted` (fn 65's weak reading and `hdet`-literal
reading refuted at three cells — the former OPEN, withdrawn in repair round 3),
`ThreeCellRefutedFull` (the same refutation with full-support rows), `Betweenness`
(T4(c): the P2 family, betweenness necessary and sufficient off the diagonal),
`BetweennessDiagonal` (T4(c)'s boundary: the diagonal, where Trust and Value come apart),
`WitnessesTieFull` (the tie refutation with full support), `Vacuity` (the one-cell and Dirac
traps), `Compose` (T6), `WitnessesCompose` (T6(c) and the positive instance),
`WitnessesComposeEvent` (T6(d): the smaller event composes where `Ω` fails; a `compose_value`
instance), `WitnessesLeak` (T3(b), T3(c), T2(c)), `WitnessesFn50` (T2(c)'s boundary: DDB fn 50,
single-score accuracy strictly weaker than local Total Trust on the proposition's own question),
`WitnessesReflectVisible` (T2(a) local: the visible-modesty witness), `Extreme` (T7), `Mutual`
(T8), `WitnessesMutualSmall` (T8's witnesses on three worlds, gated), `Channel` (T9), `Informed`
(T10), `Fact21` (T11), `Fact21TwoCell` (Fact 2.1's frame at the two-cell `q = {0}`: Trust and
Value hold, global Total Trust fails), `TrustAttained` (T11's reduction), `Fact21Trust` (T11's
Trust half, proved: Fact 2.1 complete), `Imports` (T12), `CorrFrame` (T13). The open list
(`run/wp/corr-legit-general/corr-legit-general-open.txt`) is empty since repair round 3.
`WitnessesMutual.lean` (T8's four-world witnesses) is **not imported here**: it elaborates end to
end (`scripts/lean-check`, repair round 1, about 24 CPU-minutes, one error fixed) but its compile
under `lake build` was stopped by the run's memory watchdog after 100 wall-minutes on the shared
slice; the theorems do not depend on it, and `WitnessesMutualSmall` carries the same content on
three worlds inside the gate (report, "State of the package"). Deliverables in
`run/wp/corr-legit-general/`.
-/
