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
| 11b | ~~the liability ceiling `C_t * max_j d_j(W)` is intensity-free~~ | — | **FALSE**; `test_regressions.IntensityFreeCeilingIsFalse` | withdrawn |
| 11c | `L_t(W) <= sum_j beta_j g_j d_j(W) <= (eps_t + C_t)·‖d_t(W)‖_1/delta_t` | the certified declaration | derived from result 7b; `test_contract.LiabilityCeiling`, `test_regressions` | derived |
| 12b | a region excluding a live world at every date, enforced forever, with bounded cumulative liability | the displayed trajectory | `test_contract.SafeWithoutWorldInclusiveness`; bound `2 - (N+2)/2^N < 2` | witness |
| 12c | fixed-depth exclusion against growing volume diverges | — | `test_contract.UnsafeWhenDepthDoesNotDecay` | witness |
| 18 | the disturbance's optimal cancellation is greedy | — | `test_exactness.DisturbanceOptimum`, against brute force | test-supported |
| 19 | the interior-anchored position enforces exactly against a positive disturbance budget | `K` has a strictly interior point | `test_exactness.GaugeTraderIsExact`, one and two dimensions | test-supported |
| 20 | exactness costs the safety property | world-inclusive full-dimensional `K` | `test_exactness.ExactnessCostsSafety`; value `-1/2` at a price *inside* `K` with every violation zero | witness |
| 21 | exactness needs an interior **for `K` strictly inside `(0,1)`** | `C > 0`, `zeta_E` continuous, `K ⊆ (0,1)` | proof in `ENFORCEMENT.md` §5 | derived |
| 21b | ~~exactness is impossible whenever `K` has empty interior~~ | — | **FALSE**; `K = {0}` is enforced exactly by a constant trader, `test_regressions.EmptyInteriorDoesNotImplyImpossibility` | withdrawn |
| 21c | a settlement pinning is a cube face and is enforced exactly, in one and two dimensions | `lambda > C` | `test_regressions` | witness |
| 21d | a coherence relation cuts a segment in no proper face, and a cancellable band survives every intensity | — | `test_regressions.CoherenceSegmentIsStillHard`, half-width `C/(2 beta)` | witness |
| 21e | face-solidity: exactness is available iff `K` has nonempty interior relative to the smallest cube face containing it | — | theorem in one dimension for convex `K`; delimited by 21c/21d above | conjecture |
| 22 | ~~settlement equalities and coherence polytopes both have no interior, hence both hard~~ | — | **misleading**: the interior claim is true, the inference is not — see 21b/21c | withdrawn |
| 27 | `Omega^live = PC(D_t)` for `K^D = pi(Delta(PC(D_t)))`, both directions | fragment as displayed | `test_semantics.DeductiveRecoveryUnderSupport`, stages of sizes 4/2/2/1 | derived |
| 28 | the source construction lifts to any nested, effectively presented, nonempty live-world process | reading of `lem:budgeter`.1–3 and `lem:tfdom` | `PAPER_RECONCILIATION.md` §2; hypotheses in `test_semantics.LiftHypotheses` | derived |
| 29 | ~~live worlds derived from `K_t` alone make the liability identically zero~~ | — | **FALSE**, the definition was Dirac rather than support; `test_regressions.DiracLiveWorldsAreNotLiveWorlds` | withdrawn |
| 30 | `theta_t(omega) = max { mu(omega) : mu in C_t }` is computed exactly by vertex enumeration, and liveness is `theta > 0` | finite world space | `test_semantics`; `K = {p(A)=1/2}` gives capacities `1/2, 1/2` where the Dirac reading gives none | test-supported |
| 31 | `E_mu[E_t] >= sum_j beta_j g_j^2` for every admitted credence, while a live world can have negative value | — | `test_semantics.ExpectationIsNotWorldwise`; expectation `1/40`, worldwise `-9/40` | derived |
| 32 | support bridge: `E_t(omega) >= (a - (1-theta) U)/theta` with `U = max_gain` | `theta > 0`, `U` an upper bound at the other worlds | `test_semantics.TheSupportBridge`, over a price grid | derived |
| 33 | small support capacity coexists with large worldwise loss under nonnegative expectation | — | `test_semantics.SmallSupportHidesLargeLoss`, capacities `1/4`, `1/20`, `1/100` | witness |
| 34 | `C_{t+1} subset C_t` implies live-set nesting; an enlarging revision breaks both | — | `test_semantics.Nesting` | derived |
| 35 | total removal `theta_t(omega) = 0` is distinct from small support | — | `test_semantics.GenuineRemoval` | witness |
| 23 | the `theta`-admissible polytope compiles to a legal trader, and enforcement delivers core-admissible prices | endorsement priceable | `test_core`; agrees with `NL-SI-A5`'s closed form and with the definition pointwise | test-supported |
| 24 | an unpriceable endorsement is detected and refused | — | `test_core.Priceability` | test-supported |
| 25 | a market maker constrained to display `P in K` can have no solution | the displayed date | `test_contract.ConstrainedMakerNeedsAnExistenceTheorem` | witness |
| 26 | row violations bound the interface's incoherence, at the net's resolution | net presentation | `test_contract.IncoherenceBridge`; recovers `NL-SI-C5`'s `4/15`, and coarser nets see nothing | test-supported |
| — | unbounded enforcement liability always produces an exploiting efficiently computable trader | — | none | conjecture |
| — | the interior-anchored construction generalises to every full-dimensional region | — | two dimensions only | conjecture |
| — | the modified algorithm is a computable belief sequence for every effectively presented region | — | argued in `MODEL.md` §5 | conjecture |

## The paper's intended theorem spine

Against the generalized-Logical-Induction outline this round was asked to
reconcile with, restated after the support-semantic repair.
`PAPER_RECONCILIATION.md` carries the reasoning.

| # | step | status | note |
|---|---|---|---|
| 1 | generalized credal semantics — `C_t = π_t⁻¹(K_t)` over `Δ(Ω_t)` | **derived** | types kept apart: world, credence, price vector, pricing map |
| 2 | support-live-world definition — `ω` live iff some `μ ∈ C_t` has `μ(ω) > 0` | **derived** | the definition an earlier draft got wrong; regression pinned |
| 3 | nesting lemma — `C_{t+1} ⊆ C_t ⟹ Ω_{t+1}^live ⊆ Ω_t^live` | **derived** | immediate; revisable constraints that enlarge `K_t` break the hypothesis, verified |
| 4 | live-world TradingFirm lift, under nested / effective / nonempty | **derived** | read off `lem:budgeter`.1–3 and `lem:tfdom`; not formalized |
| 5 | deductive recovery `Ω_t^live = PC(D_t)`, both directions | **derived** | `test_semantics.DeductiveRecoveryUnderSupport`; reverse direction needs `K^D` as an image, not a row system |
| 6 | `LIC` recovery from 5 | **derived** | immediate |
| 7 | two-channel necessity | **derived** | three independent obstructions; the sharpest is that the collapsed mechanism can fail to exist |
| 8 | constraint-to-trade compiler | **test-supported** | expressibility and legality argued, not proved |
| 9 | conformance theorem `∑_j β_j g_j² ≤ ε_t + C_t` | **proved** | `weighted_square_le_slack_add_volume`, kernel-checked |
| 10 | exactness case analysis | **proved (one dimension) + conjecture (face-solidity)** | `le_pair_of_contract_zero` kernel-checked for the slack-free case; `ENFORCEMENT.md` §5 for the case split |
| 11 | bounded-liability preservation, bound `1 + B` | **derived** | composes `lem:mm` and `lem:tfdom`, both taken as hypotheses |
| 12 | quantitative support bridge `E_t(ω) ≥ −(1−θ)U_t/θ` | **derived** | `U_t` named as the cube maximum gain, not smuggled; `test_semantics.TheSupportBridge` |
| 13 | Coverage–Liability synthesis | **open** | not attempted as an equivalence; Coverage is one sufficient route among two |
| 14 | converse / necessity of either bridge | **open** | item 40 |
| 15 | deductive safety as a strong special case | **derived** | zero deficit, zero liability |
| 16 | normative-static instantiation | **open** | item 39 |

Sixteen steps: **10 derived, 2 proved, 1 test-supported, 3 open** — which sums to
sixteen. Step 10 additionally carries a higher-dimensional conjecture alongside its
one-dimensional theorem; that conjecture is not counted again. Nothing on this
table is registered, and the three open steps are items 39, 40 and the synthesis.

**Withdrawn since the previous draft of this table:** the vertex/Dirac reading
of step 2, and with it the claim that step 11 is vacuous under the generalized
semantics. Both are regressions in `tests/test_regressions.py`.

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
