# Countermodels and fixtures A–O

All exact (`fractions.Fraction`), run by `tests/run.py` (68 tests, under three seconds).
Environments in `src/envs.py`; the auction in `src/bria.py`.  Rewards of the
decision-theory-bill process divided by 3: work `1/3`, invest `0`, benefit `1`.

| fixture | test | what it shows | class |
|---|---|---|---|
| **A** myopic amendment failure | `test_fixed_horizon.A_OneStep` (5 tests) | On the one-step fixture the one-step auction invests and keeps the benefit; the learner that loses `2H−3` is not a BRIA (the criterion-level analysis, sticky versus revocable, is `test_final.B`/`C`).  With a three-step investment the auction stays myopic (a continuation hypothesis's capital is drained by isolated one-step tests; no two consecutive wins).  With a renewable benefit the auction is myopic by the attention bound: at most `3𝒜_K + 1` investing actions in `K` rounds. | FIX; DERIVED for the bound |
| **B** fixed-horizon rescue | `B_FixedHorizonRescue` | `m = 2` learns the persistent amendment (average 1) and the renewable cycle at exactly `2/3` with contextual promises `1/2, 1/2, 1`, each kept. | FIX |
| **C** minimal horizon | `C_MinimalHorizon` | invest's `m`-block value from `base` is `(m−d)/m`; minimal `m = ⌊3d/2⌋+1`; existing fixture: 2.  Renewable `d=2,e=4`: values `0, 1/3, 1/2` at `m = 2, 3, 4` (`m = 3` ties). | FIX |
| **D** horizon too short / one-step pseudo-test | `D_HorizonTooShort`; `test_lease.D_PseudoTest` | `m = 2` misses a `d = 2` benefit (average below 0.37), `m = 4` learns it (exactly `2/3`).  A sound promise `1/2` is scored below `1/2` by every early withdrawal of control (`5/18` after one step), and at most `1/3` for any prefix shorter than the investment, whatever follows. | FIX |
| **E** anti-corrigible hard commitment | `test_lease.E_HardCommitment` | Ungated lease executes three prohibited actions after a revocation at `t = 3`, return `5/6`; gated lease refuses them, return `1/3`. | FIX |
| **F** gated lease | `test_lease.F_GatedLease` | Legitimate controller: gated = ungated (transparency).  Hacking controller: every step refused, return 0, promise refuted without a violation.  Same controller and lease, principal revoking at `2`, `5`, or never: returns `1/6`, `2/3`, `5/6`, each the sound contextual promise. | FIX; LEAN `trajGated_eq_traj_of_admitted` |
| **G** biased policy testing | `test_lease.G_BiasedTesting` | `a` beats `b` in both contexts; testing `a` on hard and `b` on easy steps records `3/10` vs `9/10`. | FIX (PAPER App. D, dynamic form) |
| **H** contextual-promise repair | `test_lease.H_ContextualPromiseRepair` | Contextual promises compare within the context; `a` outpromises `b` every step, both records 0, average `13/20`; a context-free promise for `a` loses `7/10` per hard step. | FIX |
| **I** long-test monopoly | `test_weighted.I_Monopoly` | Unweighted macro-BRIA on `m_k = 2^{⌊√k⌋}`: a waiting liar is covered and refuted, macro overestimation below `0.08`, and holds `0.31, 0.375, 0.43` of primitive time at `K_0 = 100, 256, 625` (tends to 1).  Duration charge: never wins, overestimation `≤ 0`, average `3/4`. | FIX; DERIVED asymptotics |
| **J** allowance too slow | `test_weighted.J_Starvation` | `m_k = k`, paper's allowance: liar rejected 400 times, tested never, `A_2(400) < 2`.  Replenishing allowance: tested at `1, 2, 4, 12, 44, 171`, record below `−200`, weighted overestimation below `1/100`. | FIX |
| **K** feasible schedule | `test_weighted.K_FeasibleSchedule` | `m_k = ⌊log₂k⌋+1`, `A = i^{-2}⌊√k⌋^{-1}`: `A_1(K) − m_K` increasing, proof bounds hold, ratio below `1/1000` at `10⁵`. | FIX; DERIVED asymptotics |
| dominance | `test_weighted.Dominance` | `m_k = 2^k`: at every liar test the weighted overestimation exceeds `1/5` and the block is at least half of all time. | FIX; LEAN `dominant_block_lower_bound` |
| algebra | `test_weighted.Algebra` | wealth identity exact under both charges, wealths nonnegative; macro vs primitive averages differ (`0` vs `→ δ`); bounded horizons rescale to the ordinary criterion. | FIX; LEAN `wealth_sum_eq`, `wealth_nonneg` |
| **L** history-shift impossibility (foreclosure) | `test_frontier.L_IrreversibleBranch` | Blind prior at the mutually exclusive branch; learner takes `A`, environment makes `B` good; continuation competence exact (every promise kept, learning error 0); regret `(2/3)(T−1)`, all history-shift but 2 units of slack at the branch block.  No deterministic learner escapes. | FIX |
| decomposition | `test_frontier.RegretDecomposition` | `V(π) − V(α) = SHIFT + SLACK + LEARN` exact on a generic run (external terms with `Ĝ`; see pressure fixture H for the typing). | FIX; LEAN `regret_decomposition` |
| **M** recoverable environment | `test_frontier.M_Recoverable` | Episodic reset: the two block values coincide.  Mixing: they differ by exactly one step per block, `Δ/T ≤ 1/m`.  Foreclosing branch: differ by `(2/3)m`. | FIX |
| **N** controller code vs promise code | `test_frontier.N_EasyPolicyHardValue` | Controller paying the `t`-th bit of `√2`; promise `2/5` unrefuted over 4000 steps (record above 300).  A type distinction only; no complexity separation is claimed (pressure pass §9). | FIX (PAPER Thm 4's class), conceptual |
| **O** learning hypothesis | `test_frontier.O_LearningHypothesis` | Min-observed-minus-margin promise; must start optimistic to be tested; refuted once (record `−1`), then promises `2/3 − 1/10` from `base` and keeps it; the pessimistic prior is never tested. | FIX |
| reduction | `test_fixed_horizon.Reduction` | `m ≡ 1` with single-action controllers: duration and block weighting give identical runs; equal-block average identity. | FIX; LEAN `blockAverage_eq` |

Fixtures A, D, I and L are the negative results the round rests on; B, F, H, J
(replenishing), K, M and O are the positive witnesses.  The dispatch's A ("one-step
BRIA can rationally remain myopic") is established for the criterion in every case
(density-zero excursions) and for the construction in the three-step and renewable
cases, and is *false* for the construction on the existing one-step fixture.

## Pressure-pass fixtures (`test_pressure.py`, 16 tests)

| fixture | test | what it shows | class |
|---|---|---|---|
| **A** effectivity gap | `A_EffectivityGap` | The prefix rule `s(k) = ⌊√(S_k/M_k)⌋`, `A(k,i) = ΔM_k + 1/k` (opening timing) on a spiky non-dominant schedule (spikes at `4^j` of share `1/(j+1)`) and on log / constant / linear ones: total subsidy within `2√(S_K M_K) + √S_K(1 + ln K)`, share of time decreasing, `A_1(K) − m_K` increasing; the liar tested repeatedly (record below −30) with weighted overestimation within `𝒜_K/S_K`. | FIX; LEAN `sum_support_jump_le` |
| **B** explicit effective schedule | `B_ExplicitSchedule` | `m_k = ⌊log₂k⌋+1` under the prefix rule: liar tested at 32 and 1024, overestimation below `1/500`, `s(K)² M_K ≤ S_K`. | FIX |
| **C** criterion vs construction | `C_CriterionVersusConstruction` | The auction on the revocable one-step amendment requests twice (an artefact of wealths) and stays; the arithmetic `α^e = 1` on `base` rounds of density `p` costs overestimation `2p/3`.  *The conclusion drawn from it in the pressure pass — that positive `base` density is forbidden — was wrong; see `test_final.B`.* | FIX |
| **D** promise vs value | `D_PromiseVersusValue` | Controller worth 1, promise 0: never followed, learner obtains `1/3`, `LEARN ≤ 0` trivially. | FIX |
| **E** vanishing slack | `E_VanishingSlack` | Same controller, promise `1 − 1/(k+1)`: followed from the first round, tail average exactly 1, slack `o(S_K)`. | FIX |
| **F** finite overpromise | `F_FiniteOverpromise` | Promise 1 on three early tests of a controller worth `2/3` (record `−3`, rejected only while wealth-bound), then sound and followed at exactly `2/3`. | FIX |
| **G** sublinear overpromise | `G_SublinearOverpromise` | Overpromise `1/k` per test on a density-zero test set with divergent harmonic sum: coverage satisfied, no overestimation, average reward below `1/14` while the controller is worth `1/2` — the criterion gives nothing. | FIX (negative) |
| **H** counterfactual typing | `H_CounterfactualTyping` | Comparator executed on fewer than 6 of 60 blocks; `G^obs` exists only there and equals `Ĝ` there; `Regret = SHIFT + SLACK + LEARN` exact with `Ĝ`. | FIX; LEAN `regret_decomposition` |
| **I** distinct continuations | `I_DistinctContinuations` | `c_full` (the whole plan) and `c_prefix` (one step, then `work`) are different continuations with block values `1/2` and `5/18`; an outcome of the latter is no test of a claim about the former (`valid_test` false). | FIX |
| **J** claim about the other continuation | `J_ClaimAboutAnotherContinuation` | A hypothesis whose continuation is "one step, then work" with claim `5/18` is exactly kept by executing it; record 0. | FIX |
| **K** discounted finite block | `K_DiscountedFiniteBlock` | Truncated discount weights `≤ 1/(1−γ)`; weighted overestimation is `W` times the rescaled unweighted one. | FIX |
| **L** infinite discounted claim | `L_InfiniteDiscountedClaim` | Two environments agreeing on the first `m` rewards differ in discounted value by `γ^m Δ`; no finite test settles the claim. | FIX; OPEN |
| **M** recoverable amendment | `M_RecoverableAmendment` | Per-block history shift of the investor between `base` and `expanded` is exactly `d` for every `m ≥ d`: the catch-up cost. | FIX |
| **N** foreclosing branch | `N_IrreversibleBranch` | Shift `(2/3) m` per block; unchanged impossibility. | FIX |

## Final-correctness-pass fixtures (`test_final.py`, 9 tests)

| fixture | test | what it shows | class |
|---|---|---|---|
| **A** condition (R) vacuity | `A_RecordCondition` | A sound hypothesis followed from the first round has no rejection round, so the old (R) has no witness; (BR) holds with `ℓ ≡ 0`.  Finite tested overpromise bounds the record below (`ℓ ≥ −Σ m (e − G)_+`). | FIX; LEAN `record_ge_neg_overpromise` |
| **B** sparse-test myopic BRIA | `B_SparseTestMyopicBRIA` | On the revocable amendment the agent "auction at `base`, `work` with estimate 1 at `expanded`" is at `base` with density `0.977`, rejects `request` on almost every `base` round, tests it 92 times at growing gaps, record `−92`, never rejects `stay`, overestimation `0.023`, average `0.326`.  On the exact original (sticky) fixture the same agent is stuck at `expanded` with overestimation `2/3`: not a BRIA there. | FIX; DERIVED (BRIA-ness from the paper's Theorem 1 on the `base` subsequence) |
| **C** auction contrast | `C_AuctionContrast` | The published auction reaches `expanded` and stays on both variants (one request on sticky, two on revocable), tail average 1. | FIX |
| **D** non-monotone support | `D_NonmonotoneSupport` | Spike `m_16 = 15` drops `s` from 3 to 1; hypothesis 3, activated at round 9, gets no allowance at 16 and still bids and wins it; the frontier is monotone and finite. | FIX |
| **E** catch-up without reversibility | `E_CatchUpWithoutReversibility` | Sticky amendment: no path back, per-block shift exactly `d` for all `m ≥ d`. | FIX |
| **F** foreclosure | `F_Foreclosure` | Mutually exclusive branches: only `go` from either state; shift `(2/3) m`. | FIX |

## Allowance-timing fixtures (`test_timing.py`, 6 tests)

| fixture | test | what it shows | class |
|---|---|---|---|
| surprise spike, settlement timing | `SurpriseSpike.test_settlement_timing_never_tests_the_spike_liar` | Fixture-A schedule; a liar claiming 1 only at the spikes `4^j`; under the paper's timing (subsidy credited after the round) it bids at most `0.30` at every spike, is rejected at every spike, tested at none, record 0 — coverage fails. | FIX (negative) |
| surprise spike, opening timing | `SurpriseSpike.test_opening_timing_makes_the_current_spike_biddable` | Same schedule and liar; tested at spike 256 (bid `0.93`, record −71); rejected at 1024 with bid `0.68` — permitted, since the sharp bound holds there and `A_i − m` grows.  Coverage asks for divergence along rejections, not a win at every spike. | FIX |
| sharp record bound | `SurpriseSpike.test_sharp_record_bound_at_every_rejection` | `ℓ_K < w_K − A_i(K)` at every rejection round of the spike liar, including the round it wins while wealth-constrained. | FIX; LEAN `record_succ_lt_of_rejected_opening` |
| reindexing | `Reindexing` | Opening timing with `A` equals settlement timing with `A'(k) = A(k+1)` and initial wealth `A(1,i)`: every bid, winner and estimate identical over 300 rounds. | FIX |
| bounds | `Bounds.test_overestimation_and_attention_with_opening_subsidy` | Weighted overestimation `≤ 𝒜_K/S_K` and per-hypothesis shortfall `≤ A_i(K)`, both with the subsidy through `K` inclusive. | FIX; LEAN `overestimation_le_allowance_opening`, `chargedRecord_ge_neg_allowance` |
| capital adequacy | `Bounds.test_capital_adequacy_at_the_spikes` | `A_1(K) − m_K` increasing at the spikes under the prefix rule; under the paper's own allowance on `m_k = k` it is below −390 at K = 400. | FIX |
