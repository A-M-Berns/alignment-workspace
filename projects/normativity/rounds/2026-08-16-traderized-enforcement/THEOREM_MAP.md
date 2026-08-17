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
| 27 | ~~`Omega^live = PC(D_t)` derived from the price region `pi(Delta(PC(D_t)))`~~ | — | — | **withdrawn**: the projection obstruction (Prop. 4, `SEMANTIC_PROJECTION.md`) makes the price-region route false, not merely unproved. The repaired theorem goes through the semantic object and is row 27a. |
| 27a | `Omega^live = PC(D_t)` for the **semantic** set `C^D = Delta(PC(D_t))`, both directions, no hypothesis on the pricing map | fragment as displayed | `test_semantics.DeductiveRecoveryUnderSupport`, stages of sizes 4/2/2/1 | derived |
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

Rebuilt after the semantic repair and the construction correction. Statements are
in `PAPER_RECONCILIATION.md`, `SEMANTIC_PROJECTION.md` and `ENFORCEMENT.md`; this
table is the evidence ledger. **Nothing here is registered.**

| # | statement | hypotheses | class | source | paper | API |
|---|---|---|---|---|---|---|
| 1 | semantic state `C_t ⊆ Δ(Ω_t)`, primitive | — | **derived** | `semantics.CredalSet`; `MODEL.md` §7a | yes | yes |
| 2 | `Ω_t^live = { ω : ∃ μ ∈ C_t, μ(ω) > 0 }` | — | **derived** | definition; `test_semantics` | yes | yes |
| 3 | `C ⊆ π⁻¹(π(C))`, equality iff `C` is fibre-saturated | — | **derived** | `SEMANTIC_PROJECTION.md` Props 1–3 | yes | no |
| 4 | the saturation is strict: `Δ({00,11})` and the anticorrelated mixture | two priced sentences | **witness** | `test_semantics.ProjectionLosesSupport` | yes | no |
| 5 | world separation does not imply credal-set separation | same fixture | **witness** | `test_semantics.FibreSaturation` | yes | no |
| 6 | same projection, different live worlds and capacities | same fixture | **witness** | `test_semantics.SamePriceProjectionDifferentLiveWorlds` | yes | no |
| 7 | `C_{t+1} ⊆ C_t ⟹ Ω_{t+1}^live ⊆ Ω_t^live`; live-set nesting is strictly weaker | — | **derived** | `test_semantics.Nesting` | yes | no |
| 8 | **live-world Budgeter/TradingFirm lift**: under (L1) nesting, (L2) uniformly effective restriction, (L3) nonemptiness, the source construction runs over `L_t` | (L1)–(L3) | **derived** | `PAPER_RECONCILIATION.md` §2; **not formalized** | **yes — the paper's one conditional** | yes |
| 9 | the generalized Budgeter is a different function: scaling `1/5` vs `1` on a displayed fixture | — | **witness** | `test_budgeter.TheWorldProcessChangesTheScaling` | yes | no |
| 10 | deductive specialization: `Ω^live = PC(D_t)` ⟹ generalized Budgeter = ordinary Budgeter | `C_t = Δ(PC(D_t))` | **test-supported** | `test_budgeter.DeductiveSpecialization` | yes | no |
| 11 | deductive semantic recovery `C_t^D = Δ(PC(D_t)) ⟹ Ω_t^live = PC(D_t)`, both directions, no hypothesis on `π` | — | **derived** | `test_semantics.DeductiveSemanticRecovery` | yes | no |
| 12 | criterion recovery to `LIC_D` | 11 and 10 | **derived** | immediate | yes | no |
| 13 | the compiled position is a source-side `Strategy n` | rows computable at date `t` | **derived** | `MODEL.md` §5; grammar exhibited, term not written | yes | yes |
| 14 | conformance `Σ_j β_j g_j² ≤ ε_t + C_t` | market-maker contract | **lean-proved** | `weighted_square_le_slack_add_volume` | yes | yes |
| 15 | enforcement inequality and its nonnegativity reading | `β_j ≥ 0` | **lean-proved** | `weighted_square_le_pair`, `pair_nonneg_of_mem` | yes | no |
| 16 | liability identity with deficits | — | **lean-proved** | `weighted_square_sub_deficit_le_pair` + witness at nonzero deficit | yes | yes |
| 17 | exactness at zero slack, no opposing volume | `K ≠ ∅`, `β_j > 0` | **lean-proved** | `le_pair_of_contract_zero` | no | no |
| 18 | interior-anchored exactness against a positive disturbance budget | interior anchor | **test-supported** | one and two dimensions only | no | no |
| 19 | impossibility for a one-sentence region strictly inside `(0,1)` | `C > 0`, continuous strategy | **derived** | `ENFORCEMENT.md` §5 | no | no |
| 20 | cube-face settlement pinning is enforced exactly | `λ > C` | **witness** | `test_regressions`, one and two dimensions | no | no |
| 21 | `face-solidity` as the general exactness condition | — | **conjecture** | one-dimensional theorem; witnesses both sides | no | no |
| 22 | a constrained market maker can have no solution | displayed date | **witness** | `test_contract.ConstrainedMakerNeedsAnExistenceTheorem` | yes | no |
| 23 | **enforcement preservation**: liability `≥ −B` over `Ω^live` ⟹ no efficient exploitation, bound `1 + B` | **conditional on 8** | **derived** | `FUNDING_AND_SAFETY.md` §3 | **yes** | yes |
| 24 | declared-quantity liability bound `(ε_t + C_t)‖d_t(ω)‖₁/δ_t` | the certified declaration | **derived** | from 16; `test_contract.LiabilityCeiling` | yes | yes |
| 25 | support bridge `E_t(ω) ≥ (a − (1−θ)U)/θ`, `U` named | `θ > 0` | **derived** | `test_semantics.SupportBridge` | yes | yes |
| 26 | expectation control coexists with large worldwise loss at small capacity | — | **witness** | `test_semantics.SmallSupportHidesLargeLoss` | yes | no |
| 27 | a region excluding a live world at every date, enforced forever, safely | displayed trajectory | **witness** | `test_contract.SafeWithoutWorldInclusiveness` | no | no |
| 27b | the motivating region splits into settlement rows with zero deficit and core rows carrying `max(0, r − m_c)`, independent of `θ` | the settlement/core statics | derived | `test_normative.TheTwoRowFamiliesDiffer` | yes | no |
| 27c | settlement monotonicity makes the exclusion depth non-increasing | `NL-SI-C4`, `NL-SI-P1` | derived | `test_normative.SettlementDrivesTheGapDown` | yes | no |
| 27d | a safe motivating trajectory: bound `135/8`, constant across horizons | endorsement vindicated after finitely many dates | witness | `test_normative.SafeMotivatingTrajectory` | yes | no |
| 27e | a **bounded-liability failure**: the declared certificate diverges (`52.3 → 182.5 → 392.5`) *and* the realized cumulative value at one followed world diverges quadratically, against contract-satisfying prices | endorsement never vindicated, `C_t = t` | witness | `test_normative.UnsafeContrastTrajectory`, `test_outflow.PersistentDeficitDefeatsTheCertificate` | yes | no |
| 27g | per-endorsement finite caps do **not** bound lifetime outflow, under finite gating with one live row per date | — | witness | `test_outflow.PerEndorsementCapsDoNotAggregate` | yes | no |
| 27h | finite gating alone does not bound lifetime outflow | — | witness | `test_outflow.GatingIsNotALifetimeBound` | yes | no |
| 27i | a global account with checked allocation gives `sum_e B_e <= B`, and the certificate is additive over rows and zero on settlement rows | — | derived | `test_outflow.SummableAllocationsGiveAFiniteCertificate`, `.ChargeIsAdditiveOverRowsAndConservativeOverWorlds` | yes | no |
| 27j | affordable tolerance: `delta_t >= (eps_t + C_t)*‖d_t‖₁ / b_t`, inverting the charge exactly | — | derived | `test_outflow.AffordableTolerance` | yes | no |
| 27k | **no finite account** funds meaningful force at infinitely many dates when the exclusion deficit stays above a positive floor — against every protocol, not one policy | `delta_t <= 1` for a nonvacuous promise | derived | `test_outflow.NoAccountSubsidizesAPersistentDeficit` | yes | no |
| 27l | a forever-unvindicated endorsement receives nonvacuous force at every date within finite capital when its deficit decays geometrically against linearly growing volume; closed-form bound `17/2` | deficit `2^-t`, `C_t = t+1`, `delta = 1/2` | witness | `test_outflow.ForeverUnvindicatedAndSafe` | yes | no |
| 27m | the liability certificate is **invariant** under row rescaling and duplication at a fixed actual conformance target; a fixed *declared* tolerance is presentation-dependent | — | derived | `test_outflow.LiabilityIsInvariantUnderRowPresentation` | yes | no |
| 27n | weakening the declared core minimum does not reduce the charge | `max(0, r − m_c)` has no `theta` in it | derived | `test_outflow.ExhaustionBehaviour` | yes | no |
| 27f | `P2` does not cover enforcement liability: its declared means are refusal and bounded participant budgets, both of which the enforcement trader is exempt from | — | derived | `NORMATIVE_SAFETY.md` §5 | yes | no |
| 28 | necessity of either liability bridge | — | **open** | item 45 | no | no |
| 29 | what governs removing a world from support | — | **open** | item 44 | no | no |
| 30 | normative statics producing `C_t` or `K_t` | — | **open** | item 39 | no | no |

30 entries: 12 derived, 8 witness, 4 lean-proved, 3 open, 2 test-supported, 1 conjecture. The counts sum to 30.

**Four rows are kernel-checked** — 14 through 17, carrying five Lean theorems and
two inhabitation witnesses — and all four are force algebra.

**One row is the paper's conditional.** Entry 8, the live-world lift, is `derived`
and unformalized, and entry 23 depends on it. Formalizing 8 is the single
highest-value next piece of work: it is what makes the generalized criterion a
theorem rather than an analogy, and `PAPER_RECONCILIATION.md` §2 states it with
its three hypotheses and what each pays for, so a formalization round has an
unambiguous target.

**No conjecture is hidden in a derived row.** Entry 21 is the only conjecture.
Exactness is split across 17–21 at four different evidence levels rather than
summarised as one claim.

**Withdrawn across the round, each with a regression in `tests/test_regressions.py`:**
the intensity-free liability ceiling; exactness impossibility for every
empty-interior region; the Dirac live-world reading and its laundering
conclusion; the preimage reading of deductive recovery; and the claim that the
generalized construction is the ordinary one under a different criterion.
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
