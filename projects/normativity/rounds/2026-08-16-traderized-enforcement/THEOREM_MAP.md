# Theorem map

Every numbered result, its hypotheses, where it is checked, and its evidence
class. Nothing here is registered in `CLAIMS.md`.

## Classes used

`lean-proved` — kernel-checked in `lean/Workspace/Normativity/Contrib/TraderizedEnforcement.lean`,
axiom-clean, **unregistered**. `derived` — proved on paper from source lemmas
taken as hypotheses, no machine check. `test-supported` — exact-rational fixtures
under `tests/`. `witness` — a single displayed instance. `conjecture`.

## Results

| # | statement | hypotheses | evidence | class |
|---|---|---|---|---|
| 1 | `max_W ⟪ζ, W-P⟫ = ∑_φ [ζ_φ⁺(1-P_φ) + ζ_φ⁻P_φ]` | day-`n` strategy's cash term | `test_enforcement.ExtremalPinning`; `max_gain` checked against cube enumeration | test-supported |
| 2 | `⟪ζ_E(P), x-P⟫ ≥ ∑_j β_j g_j(P)²` for every `x` meeting every row | `β_j ≥ 0` | `weighted_square_le_pair`, with `enforcement_inequality_is_nonvacuous` | lean-proved |
| 3 | contract at slack `0` against `E` alone, `K_n ≠ ∅`, `β_j > 0` ⟹ `P_n ∈ K_n` | as stated | `le_pair_of_contract_zero`; `test_enforcement.ExactEnforcement` in one and two dimensions | lean-proved |
| 4 | contract at slack `ε_n`, `‖τ‖₁ ≤ M_n` ⟹ `∑_j β_j g_j² ≤ ε_n + M_n` | `K_n ≠ ∅`, `β_j ≥ 0` | `weighted_square_le_slack_add_volume`; swept over prices × adversarial `τ` in `test_enforcement.MasterInequality` | lean-proved |
| 5 | exact enforcement fails for `ε_n > 0` | — | `test_enforcement.PositiveSlackBreaksExactness`; escape set `{1/3, 5/12, 5/6}` at denominator 12 | witness |
| 6 | opposing volume defeats exactness at slack `0` | `M > 0` | `test_safety.SupportCoverageFailure`; violation exactly `M/β` | witness |
| 7 | `⟪ζ_E(P), W-P⟫ = ∑_j β_j g_j(P)[(⟪c_j,W⟫-r_j) + g_j(P)]` | — | `test_deduction.LiabilityIdentity`, 2000 exact instances | test-supported |
| 8 | world-inclusive `K_n` ⟹ enforcement value `≥ 0` in every plausible world | `β_j ≥ 0` | `pair_nonneg_of_mem`; swept in `test_safety.PlausibleValueIsNonnegative` | lean-proved |
| 9 | enforcement liability `≤ B` ⟹ no efficiently computable trader exploits, with bound `1+B` | `lem:mm` and `lem:tfdom` as hypotheses; the modification prices `TF + E` | derivation in `FUNDING_AND_SAFETY.md` §3 | derived |
| 10 | world-inclusive presentation ⟹ `B = 0` and bound `1` | 8 and 9; stages nested | `test_safety.SafeCase` | derived |
| 11 | losing world-inclusivity persistently produces an exploiting trader | one fixture: settled `φ`, contrary row, opposing mass `1/2` | `test_safety.SupportCoverageFailure`; worth `18/5` over 8 dates against bound `14/5` | witness |
| 12 | coordinate-rotating enforcement diverges under a constant per-date exposure | — | `test_safety.LiabilityLaundering` | witness |
| 13 | the support-function presentation is world-inclusive and equals the coherence polytope at coefficient bound one on a four-sentence Boolean fragment | fragment as displayed | `test_deduction.SupportPresentation`, point-by-point against exact hull membership | test-supported |
| 14 | the affine-relation presentation admits incoherent prices | same fragment | `test_deduction.AffineRelationsAreNotEnough`; 24 escapes, `(0,1/3,1/3,0)` named | witness |
| 15 | intensity does not set position size; opposing volume does | the §4 fixture | `test_safety.IntensityIsNotFunding`; position `-1/2` across `β ∈ {10,100,1000}` | witness |
| 16 | the enforcement position does not enter an ordinary trader's net worth | — | `test_safety.SubsidyHarvesting` | test-supported |
| 17 | enforcement leaves no residue at the next date; settlement does | — | `test_deduction.SettlementIsNotEnforcement` | witness |
| 7b | the liability bound with deficits: value `>= sum beta g^2 - sum beta g d(W)` | `beta_j >= 0` | `weighted_square_sub_deficit_le_pair`, with `liability_bound_is_nonvacuous` at a nonzero deficit | lean-proved |
| 11b | the liability ceiling `C_t * max_j d_j(W)` is intensity-free | the certified declaration | `test_contract.LiabilityCeiling`, three tolerances, same rational | test-supported |
| 12b | a region excluding a live world at every date, enforced forever, with bounded cumulative liability | the displayed trajectory | `test_contract.SafeWithoutWorldInclusiveness`; bound `2 - (N+2)/2^N < 2` | witness |
| 12c | fixed-depth exclusion against growing volume diverges | — | `test_contract.UnsafeWhenDepthDoesNotDecay` | witness |
| 18 | the disturbance's optimal cancellation is greedy | — | `test_exactness.DisturbanceOptimum`, against brute force | test-supported |
| 19 | the interior-anchored position enforces exactly against a positive disturbance budget | `K` has a strictly interior point | `test_exactness.GaugeTraderIsExact`, one and two dimensions | test-supported |
| 20 | exactness costs the safety property | world-inclusive full-dimensional `K` | `test_exactness.ExactnessCostsSafety`; value `-1/2` at a price *inside* `K` with every violation zero | witness |
| 21 | exactness is impossible for a one-sentence region with empty interior | `C > 0`, `zeta_E` continuous | proof in `ENFORCEMENT.md` §5; ingredients in `test_exactness.ExactnessImpossibleWithoutAnInterior` | derived |
| 22 | settlement equalities and coherence polytopes have no interior | — | `test_exactness`, both cases | test-supported |
| 23 | the `theta`-admissible polytope compiles to a legal trader, and enforcement delivers core-admissible prices | endorsement priceable | `test_core`; agrees with `NL-SI-A5`'s closed form and with the definition pointwise | test-supported |
| 24 | an unpriceable endorsement is detected and refused | — | `test_core.Priceability` | test-supported |
| 25 | a market maker constrained to display `P in K` can have no solution | the displayed date | `test_contract.ConstrainedMakerNeedsAnExistenceTheorem` | witness |
| 26 | row violations bound the interface's incoherence, at the net's resolution | net presentation | `test_contract.IncoherenceBridge`; recovers `NL-SI-C5`'s `4/15`, and coarser nets see nothing | test-supported |
| — | unbounded enforcement liability always produces an exploiting efficiently computable trader | — | none | conjecture |
| — | the interior-anchored construction generalises to every full-dimensional region | — | two dimensions only | conjecture |
| — | the modified algorithm is a computable belief sequence for every effectively presented region | — | argued in `MODEL.md` §5 | conjecture |

## What carries the weight

Results 2, 3, 4, 7b and 8 are one inequality and four of its readings, and they
are the only things in the round that are kernel-checked. 7b is the general form
and 8 is its `d = 0` corollary. Result 9 is the round's
central claim about safety and is **not** in Lean: it composes two source lemmas
about objects — the market maker and the trading firm — that this round does not
formalize, and formalizing it means formalizing the modified algorithm inside the
pinned dependency's own types.

## Named future port target

`Workspace.Normativity.Contrib.TraderizedEnforcement` currently states the
inequality over an abstract pairing. The port that would be worth doing next is
result 9 against the dependency's actual `Trader`, `MarketMaker` and
`TradingFirm`: define the modified history
`MarketMaker (TradingFirm DP + E) …`, and prove
`¬ Tr.Exploits (modified history) DP` from a hypothesis bounding the enforcement
trader's plausible cumulative value. The step it must reproduce is
`liaTrader_not_exploited` (`Construction/LIA.lean:96`), which is the exact place
the modification breaks. That is a substantial piece of work against the
dependency's construction layer and is filed rather than attempted.

Doing a Lean port of the fixtures instead would formalize a toy while the
load-bearing composition stayed on paper, and is not done.
