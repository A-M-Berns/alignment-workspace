import Cleanroom.Fa.FaForcingTrader.B.Defs
import Cleanroom.Fa.FaForcingTrader.B.Feedback
import Cleanroom.Fa.FaForcingTrader.B.Certificate
import Cleanroom.Fa.FaForcingTrader.B.Witnesses
import Cleanroom.Fa.FaForcingTrader.B.Open

/-!
# `fa-forcing-trader` · angle B: the citation route

Root of `Cleanroom.Fa.FaForcingTrader.B` ([[fa-forcing-trader-mandate]], "Attempt angles", B).
Report: `run/wp/fa-forcing-trader/fa-forcing-trader-report-B.md`; findings `-findings-B.md`;
ledger `-ledger-B.md`; open list `fa-forcing-trader-B-open.txt`.

| file | content |
|---|---|
| `Defs` | `LegibleOn` (the one (c)-shape), `scheduleIndicator` (+ `_pgenerable` from FAF's `deferralImageFlag` ruler, `_supported`), `schedGate`/`schedGateBelow` (+ `_pgenerable`, `_denote`, `_pos_imp`, `_supported`), `WindowDisjoint`, the legibility transfer lemmas |
| `Feedback` | `quoteSide_fullLimit` (the one engine: FAF's `luv_wubexp_ofComputation` over a `CrossQuotePackage`), `selfSide_fullLimit` (`cee` + the engine at `H`), **T6′** `theoremSS_fullLimit` (+ `_general`, `_below`), **T7′** `theoremSS_schedThresholdAbove`/`Below` |
| `Certificate` | the grid truth and the counting lemma; `quoteSide_fullLimit_grid` (the engine from a certificate on the *computable* grid truth, via `lic_wubaff`); `StrictlyReflected` and the identification of FAF's `normalizedMeshTruth` with the grid truth under it; `FeedbackTruthComputation.ofMachineRatCodes` |
| `Witnesses` | `linearSchedule` (N+ for `WindowDisjoint`), `scheduleIndicator_divergent` (every schedule's mass diverges), `legibleOn_schedGate_self` (N−) |
| `Open` | OPEN: `exists_gridCertificate_of_marketComputation` (Lemma 1 (b)–(d) in FAF's machine model), `exists_twoMarket_legible_pair` (T11) |

Angle A's shared `Defs.lean`/`Schedule.lean` had not been committed when B started; B's `Defs`
carries its own copies (same names and meanings) for the reconciler to unify.
-/
