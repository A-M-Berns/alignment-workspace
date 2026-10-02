import Cleanroom.Deference.DefObstruction.Core
import Cleanroom.Deference.DefObstruction.Carrier
import Cleanroom.Deference.DefObstruction.Tracking
import Cleanroom.Deference.DefObstruction.Witness
import Cleanroom.Deference.DefObstruction.TwoFaces
import Cleanroom.Deference.DefObstruction.Tower
import Cleanroom.Deference.DefObstruction.TowerWitness
import Cleanroom.Deference.DefObstruction.Fragment
import Cleanroom.Deference.DefObstruction.FragmentWitness
import Cleanroom.Deference.DefObstruction.Blind
import Cleanroom.Deference.DefObstruction.BlindWitness
import Cleanroom.Deference.DefObstruction.Cost
import Cleanroom.Deference.DefObstruction.SelfTrust
import Cleanroom.Deference.DefObstruction.ChiParadox
import Cleanroom.Deference.DefObstruction.Open

/-!
# `def-obstruction`: the obstruction — 2a, 2b and the dichotomy

Root module ([[def-obstruction-mandate]]). A dependent imports this one name and gets:

* **T1** (`Core`): `rho`, `defect_eq_max` (`|a − ρ(a)| = max a (1 − a)` on all of `ℝ`),
  `defect_ge_half`, `defect_eq_half_iff`, `defect_isGLB`, `rounding_robust`, the `<` twin
  `rhoStrict` with `defect_strict_ge_half`, and the bridges `side_eq_rho`, `invSide_eq_rho`.
* **The carrier** (`Carrier`): `TablePair` (one reader over `ledgerProcess DPH a e`, any `[0,1]`
  table; `OneWayPair` minus the publisher), `TablePair.ofOneWay`, `TablePair.Y`/`Yprice`, and
  `li-diagonal`'s `gDiag_decided`/`gDiag_truth_iff`/`lemmaB`/`lemmaB_expect` re-proved over it
  (`gDiag_truth_iff_table`, `lemmaB_table`, `lemmaB_expect_table`) — with no publication-schedule
  hypothesis.
* **T2, 2a** (`Tracking`): `exact_defect_table` (`½ ≤ |a 0 n − s_n|`, every table, every day),
  **`tracking_fails`** (`∀ ε > 0, ∀ᶠ n, ½ − ε ≤ |a 0 n − 𝔼^H_{F n}(𝟙 g_n)|` under the cost-model
  certificates), `tracking_fails_price`, `not_tracking`, `tracking_liminf`, and the corollaries
  `tracking_fails_oneWay`, `tracking_fails_diagonalPair` (two-way, `partial: over the OPEN pair`).
* **T6** (`Tracking`): `defect_tendsto` (`|a − Y| → max L (1 − L)` when `a → L`),
  `limit_agreement_fails` (`½ ≤ |lim a − lim Y|`), `limit_agreement_impossible`, `Y_limit_mem`.
* **T3** (`Witness`): `TablePair.ofLIA` (FAF's LIA over any computable table), the alternating
  table `aAlt` with every certificate discharged (`padTrueSide_aAlt_codes`,
  `padFalseSide_aAlt_codes`), **`altPair_tracking_fails`** (hypothesis-free 2a, N+),
  `altPair_defect_tendsto_one`, `altPair_not_tracking`; the constant best response `aHalf`
  (`halfPair_Y_tendsto_one`, `halfPair_defect_tendsto_half`, N−;
  `halfPair_no_limit_agreement_at_half`, the hypothesis-free refutation of the §6 example); the
  late-publication pair `latePair` with `latePair_tracking_fails` (the schedule does not enter 2a).
* **T5** (`TwoFaces`): `altPair_two_faces` (pointwise defect `→ 1`, uniform-weight bias `→ 0`
  on one coupled FAF instance), `cesaro_aAlt_sub_side`, `halfPair_weightedBias_tendsto`
  (`→ −½`: both faces can die); v6's high-side gate on the alternating pair is biased by `1`
  (`altPair_highGate_bias_tendsto_one`; `altPair_rampGate_bias_tendsto_one` at FAF's `ctsInd`,
  every width `δ > 0`, via `ctsInd_aAlt_eq_smul` and `weightedAverage_smul_weight`).
* **T4** (`Tower`, `TowerWitness`): `tower_imp_tracking`, `pointwise_tower_fails`,
  `tower_iff_present` over FAF's `≈ₙ`; `expect_asympEq_of_determinedVia_generable` (expectation
  provability induction at a generable approximant; FAF API request); `padLedger`,
  `readoff_deferred` (`𝔼^H_{F n}(α_{0,n}) ≈ₙ a 0 n`); **`tower_fails_diagonal`** (deferred day),
  `not_tower_diagonal`, `lemmaB_sameDay`, `tower_fails_diagonal_sameDay` (the notes' day-`n`
  form, no publication hypothesis); hypothesis-free on the alternating pair:
  `altPair_tower_fails`, `altPair_tower_fails_sameDay`.
* **T7** (`Fragment`, `FragmentWitness`): `DecidedTrueAt`/`DecidedFalseAt`/`Decided`/`Undecided`;
  **`decided_fragment_trusts`** (both readers' limiting belief `1`/`0`, no hypothesis on the
  table; the base's satisfiable stages now come from the carrier, `TablePair.hworld_base`),
  `undecided_fragment_confined` (`(0,1)`), `limitingBelief_extreme_iff_decided(_base)`
  (anson-040's iff), `adjoinAtom`, `freshAtom_undecided`,
  **`criterion_not_monotone_in_process`** (no market is an inductor over both a process and its
  atom extension); over FAF's LIA: `obsAtom_undecided`, `lia_adjoin_not_inductor_base`,
  `lia_base_not_inductor_adjoin`, **`criterion_not_monotone_either_direction`** (an inductor on
  each side: the two-sided statement), `altPair_obsAtom_confined`, `adjPair_obsAtom_trusts`.
* **T8** (`Blind`, `BlindWitness`): `BlindSentence`/`Blind` of record (truth-value blindness),
  **`blind_of_tagFree`** (a tag-free family is truth-value blind — the quote-free-family half of
  headline 4, *not* §4.3's "the autonomous target is blind"), `gDiag_not_blind` (instantiated:
  `gDiag_not_blind_paper`), `blind_avoids_diagonal`, `TracksFamily`, `QuoteRef` (syntactic,
  index-aligned), **`dichotomy_2a_half`**, `predictable_imp_uninfluenced` (plumbing: 2a half from
  `dichotomy_2a_half`, 2b half over the named `h2b`); the gap between `¬ QuoteRef` and `Blind`
  inhabited by the positive ledger literal (`posLit`, `gap_inhabited`); the source's
  settlement-map blindness of record, `SettlementBlind`, with §4.3's autonomous target
  (`autonomousTarget`, `autonomousTarget_settlementBlind`: blind by construction); over FAF's LIA
  (`BlindWitness`): tracking is satisfiable on the benign family (`obsFamily`,
  `adjPair_tracks_obsFamily`, N+ — the alternating table tracks the alternately decided family),
  and the diagonal's credence is table-dependent (`gDiag_credence_table_dependent`).
* **T9–T11** (`Cost`): `regress`, `cost_circularity(_deferral)`, `cost_setup_realizable`,
  `blind_cost_realizable`, `Schedule` of record with `Schedule.ofRecord`, `horizon_cap`;
  `no_bridge_axiom(_iff)`; `gap`, `ResolvedLate`, `NeverDecided`, `pull_th4(_gap)`, `pull_th9`.
* **T12** (`SelfTrust`): `resale_lb`, `resale_lb_ramp`, `externalized_self_trust(_of_packages)`
  (kind L over disclosed (c) packages; `partial: product-LUV package`).
* **S1** (`ChiParadox`): `paperLIA_half_diagonal_inductor` (satisfiable stages, a `½`-diagonal
  quote, an inductor — FAF's paper market), **`chiParadox_refuted`** (the settlement-level
  `<`-diagonal is not an exploitation theorem: the universal over processes *with satisfiable
  stages* is refuted by that witness), `chiParadox_price_tendsto_half`; and why the guard:
  `unsatDP` (every stage unsatisfiable, every computable market an inductor by `thm:scon`) proves
  the unguarded round-1 statement with no `thm:lp` (`chiParadox_unguarded_degenerate`).
* **Open** (`Open`): `tracking_bound_fails_some_table` (the certificates are necessary),
  `le_diagonal_inductor_exists` (the `≤`-convention diagonal admits an inductor).

Not built: S2 (Gödel rebuilds the quote diagonal), S3 (`PredictorExpert`/`MartHA`), S4 (uniform
non-dogmatism margin), S5 (the waiting-arbitrage trader), S6 (the source-shaped `g_n`); T13's
regime split is a finding (F-Regimes) — see `run/wp/def-obstruction/def-obstruction-report.md`.
-/
