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

## The paper's theorem spine

Rebuilt after the semantic repair. Statements are in
`PAPER_RECONCILIATION.md` and `SEMANTIC_PROJECTION.md`; this table is the
evidence ledger. **Nothing here is registered.**

| # | statement | evidence class | source | paper depends |
|---|---|---|---|---|
| 1 | generalized semantic state: `C_t ⊆ Δ(Ω_t)`, primitive | **derived** | `semantics.CredalSet`; `MODEL.md` §7a | yes |
| 2 | support-live worlds `Ω_t^live = { ω : ∃ μ ∈ C_t, μ(ω) > 0 }` | **derived** | definition; `test_semantics` | yes |
| 3 | projection `K_t = π_t(C_t)`, and `C ⊆ π⁻¹(π(C))` with equality iff `C` is fibre-saturated | **derived** | `SEMANTIC_PROJECTION.md` §2, Props 1–3 | yes |
| 4 | the saturation is strict: `Δ({00,11})` vs the anticorrelated mixture | **witness** | `test_semantics.ProjectionLosesSupport` | yes |
| 5 | world separation does not imply credal-set separation | **witness** | `test_semantics.FibreSaturation`; `π` injective on four worlds, saturation still strict | yes |
| 6 | two credal sets, same projection, different live worlds and capacities | **witness** | `test_semantics.SamePriceProjectionDifferentLiveWorlds` | yes |
| 7 | nesting: `C_{t+1} ⊆ C_t ⟹ Ω_{t+1}^live ⊆ Ω_t^live`; live-set nesting is strictly weaker | **derived** | `test_semantics.Nesting` | yes |
| 8 | live-world TradingFirm lift, under nested / effectively presented / nonempty | **derived** | reading of `lem:budgeter`.1–3 and `lem:tfdom`; **not formalized** | yes — load-bearing |
| 9 | deductive semantic recovery `C_t^D = Δ(PC(D_t)) ⟹ Ω_t^live = PC(D_t)`, both directions, no hypothesis on `π` | **derived** | `test_semantics.DeductiveSemanticRecovery` | yes |
| 10 | criterion recovery to `LIC_D` | **derived** | immediate from 9 | yes |
| 11 | constraint-to-trade compiler is a legal expressible strategy | **test-supported** | `enforcement.py`; expressibility argued, not proved | yes |
| 12 | conformance: `Σ_j β_j g_j² ≤ ε_t + C_t` | **lean-proved** | `weighted_square_le_slack_add_volume` | yes |
| 13 | enforcement inequality and its nonnegativity reading | **lean-proved** | `weighted_square_le_pair`, `pair_nonneg_of_mem` | yes |
| 14 | liability identity with deficits | **lean-proved** | `weighted_square_sub_deficit_le_pair`, witness at nonzero deficit | yes |
| 15 | exactness at slack zero | **lean-proved** | `le_pair_of_contract_zero` | yes |
| 16 | exactness case analysis: interior, cube face, empty interior inside the cube | **derived + witness** | `ENFORCEMENT.md` §5; `test_regressions` | yes |
| 17 | face-solidity as the general exactness condition | **conjecture** | one-dimensional theorem; witnesses on both sides | no |
| 18 | constrained market maker can have no solution | **witness** | `test_contract.ConstrainedMakerNeedsAnExistenceTheorem` | yes |
| 19 | bounded-liability preservation, bound `1 + B` | **derived** | composes `lem:mm` and `lem:tfdom`, taken as hypotheses | yes — load-bearing |
| 20 | declared-quantity liability bound `(ε_t + C_t)‖d_t(ω)‖₁/δ_t` | **derived** | from 14; `test_contract.LiabilityCeiling` | yes |
| 21 | support bridge `E_t(ω) ≥ (a − (1−θ)U)/θ`, `U` named | **derived** | `test_semantics.SupportBridge` | yes |
| 22 | expectation control coexists with large worldwise loss at small capacity | **witness** | `test_semantics.SmallSupportHidesLargeLoss` | yes |
| 23 | a region excluding a live world at every date, enforced forever, safely | **witness** | `test_contract.SafeWithoutWorldInclusiveness` | no |
| 24 | necessity of either liability bridge | **open** | item 45 | no |
| 25 | what governs removing a world from support | **open** | item 44 | no |
| 26 | normative-static instantiation: a source producing `C_t` or `K_t` | **open** | item 39 | no |

26 entries: 10 derived, 6 witness, 4 lean-proved, 3 open, 1 conjecture, 1 derived + witness, 1 test-supported. The counts sum to 26.

**Four rows are kernel-checked** — 12 through 15, carrying five Lean theorems and
two inhabitation witnesses between them — and all four are force algebra. **Two are load-bearing and unformalized**: the live-world
TradingFirm lift (8) and bounded-liability preservation (19). If one thing is
formalized next it should be 8 — it is the step that makes the generalized
criterion a theorem rather than an analogy, and it is read off source proofs
rather than proved here.

**No conjecture is hidden inside a derived row.** Entry 17 is the only
conjecture and is labelled as one; entry 16 is split into its derived and
witnessed halves.

**Withdrawn across the round, each with a regression:** the intensity-free
liability ceiling; exactness impossibility for every empty-interior region;
the Dirac live-world reading and its laundering conclusion; and the
preimage reading of deductive recovery. `tests/test_regressions.py`.

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
