import Cleanroom.Fa.FaForcingTrader.Defs
import Cleanroom.Fa.FaForcingTrader.Schedule
import Cleanroom.Fa.FaForcingTrader.A
import Cleanroom.Fa.FaForcingTrader.B
import Cleanroom.Fa.FaForcingTrader.Compat
import Cleanroom.Fa.FaForcingTrader.Bridge
import Cleanroom.Fa.FaForcingTrader.TheoremSS
import Cleanroom.Fa.FaForcingTrader.Violation
import Cleanroom.Fa.FaForcingTrader.Analysis
import Cleanroom.Fa.FaForcingTrader.Open
import Cleanroom.Fa.FaForcingTrader.Witnesses

/-!
# `fa-forcing-trader` — criterion-to-forcing: the scheduled Theorem SS / v3 Theorem 1 with a real
trader (reconciled root)

Root module of the dual package `Cleanroom.Fa.FaForcingTrader` ([[fa-forcing-trader-mandate]]),
reconciled from two independent angles kept unchanged as evidence: **A** (`A/`, the trader route:
FAF's Kelly round-trip trader `feedbackTrader` on the interleaved schedule gives the `H`-side
bridge at grade (a); the `A` side is fa-theorem-a's limit-point unbiasedness) and **B** (`B/`, the
citation route: both sides by FAF's corrected 4.8.16 `luv_wubexp_ofComputation` under timing
certificates, full limits). The **main modules** state each target once in the package namespace
over the definitions of record, proved by the angle named in each docstring (`:= A.…` /
`:= B.…`) or by the reconciler, and re-export the attempts' supporting declarations (`export`).
Deliverables: `run/wp/fa-forcing-trader/fa-forcing-trader-report.md` (with its "Two attempts"
section), `-findings.md`, `-ledger.md`, `-open.txt`.

Definitions of record (shared, written by angle A, imported by B's headlines through `Compat`):
`Defs` — `LegibleOn` (the package's one (c)-shape, the corpus's (L)), `scheduleIndicator`/`schedInd`,
`WindowDisjoint`, `schedGate`/`schedGateBelow`, `bundle`, `violW`; `Schedule` — `interleave`,
`linearSchedule`. Angle B's duplicated copies are related to them in `Compat` (syntactically
identical for `LegibleOn`/`WindowDisjoint`; equal denotations for the indicator and the gates).

Main modules:
* `Bridge` — T4 `hSideBridge` (the microscope: no `hbias`/`hbdd`/`hNoExp`/`hMirror`), T5.
* `TheoremSS` — Theorem SS at three grades: `theoremSS_limitPoint` (A; (c) `pkg.reflected`, `hL`),
  **`theoremSS_fullLimit_gridCert`** (the full-limit row of record since repair round 1: B's
  `A`-side engine on the computable grid truth + A's `H`-side trader; (c) `pkg.reflected`, `hL`;
  (b) the grid certificate `C` only), with `theoremSS_fullLimit_oneCert` as the FAF-verbatim
  certificate variant, and `theoremSS_fullLimit_twoCert` (B; (b) `CA`, `CH`, `hq`); T7
  `schedThresholdAbove_of_theoremSS`
  (`∃ᶠ`, of record) and `schedThresholdAboveEv_oneCert`/`_twoCert` (`∀ᶠ`); T12 (a).
* `Violation` — T3 `v3Theorem1_of_jointLegible` (two-way, `partial: over the OPEN pair`).
* `Analysis` — T10 (⟹ proved; ⇐ refuted for the successor lookahead, for root-fa-2-003 (ii)'s
  own class (`tower_converse_fails`) and for the strict `2^n`-window class
  (`tower_converse_fails_strict`, repair round 2); `ChasingSchedule`, the FAF corollaries), T8,
  T9, T12 (b)/(c); the note's finite-mass remark (`unnormBias_bounded_of_summable`, repair round 2).
* `Open` — T11 `exists_twoMarket_legible_pair` and `exists_gridCertificate_of_marketComputation`
  (both `:=` the attempts' `sorry`s; listed), T11's strengthened form
  `exists_twoMarket_legible_pair_genuine` (repair round 1; listed), and the sorry-free
  `twoMarket_legible_pair_of_genuine` (the strengthened form implies the record; repair round 2).
* `Witnesses` (repair round 1) — full-package inhabitants of T6/T7 at the same market:
  `hdiv` discharged at every sub-zero threshold (`schedGate_divergent_of_le_neg`) and at every
  content threshold `t + δ < 1` on `X ≡ 𝟙(⊤)` (`schedGate_divergent_of_realized_tendsto_one`,
  `theoremSS_paper_self_top`, `schedThresholdAbove_paper_self_top`); repair round 2 adds what
  those instances test (§D: `h → 1` alone gives T7's conclusion, not T6's) and that the T4
  witness's return vanishes with no trader (§E, `hSideBridge_w2_return_tendsto_zero`).

Nothing in this package redefines `TotalTrust`, `ThresholdIneqAbove`, `Expert`, `WeightedApprox`,
`Dominates`, `CrossQuotePackage` or `rampAbove`.
-/
