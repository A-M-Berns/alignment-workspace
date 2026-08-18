# Theorem map

The evidence ledger, sorted by what a reader needs to know first: what is settled,
what is conditional and on exactly what, what is open, and what was refuted.
`PROOF_CLOSURE.md` is the same content as an argument; this is the index.

**Nothing here is registered in `CLAIMS.md`.**

## Classes

`lean-proved` — kernel-checked in `lean/Workspace/Normativity/Contrib/`, sorry-free,
axioms `[propext, Classical.choice, Quot.sound]`, **unregistered**. `source-exact` — a
declaration of the pinned dependency, used as its theorem. `derived` — proved on paper
from named results above this line. `exhaustive-finite` — checked at every point of a
stated finite rational domain. `test-supported` — exact-rational fixtures.
`witness` — one displayed instance. `blocked` — a named transcription obligation, not
a mathematical gap. `open`. `false`.

`lean/Workspace/Normativity/Contrib/` holds `TraderizedEnforcement`,
`AssessmentProcess`, `AssessmentFirm`, `AssessmentProperties`, `EnforcementStrategy`,
`EnforcementPreservation`, `DeductiveEnforcement`, `CoherenceModulus` and
`IntrinsicCoherence`.

---

## Settled

### The source's factorization

| # | statement | class | where |
|---|---|---|---|
| S1 | the criterion assesses in `PC(D_n)`; `Budgeter` reads it twice; `TradingFirm` only through `Budgeter` | source-exact | `Criterion.lean:1450`, `Budgeter.lean:918`, `TradingFirm.lean:432` |
| S2 | **`MarketMaker`'s bound `netWorth < 1` is uniform over every propositionally consistent world**, so no assessment process needs anything of it | source-exact | `marketMaker_netWorth_lt_one`, `MarketMaker.lean:1434` |
| S3 | the source's plausible-world enumeration is over **atom tables**, `PC(D_n)` being a cylinder over `atoms(D_n)` | source-exact | `finiteAtomAssignments`, `Budgeter.lean:124` |
| S4 | the scaling infimum over no plausible world is `1`; the floor theorem is then vacuous | source-exact | `EF.listMin`, `Budgeter.lean:263` |

### The live-world lift

| # | statement | class | declaration |
|---|---|---|---|
| L1 | net worth reads a world only through its payouts on the traded support | lean-proved | `netWorth_congr_on_support` |
| L2 | `lem:budgeter`.1 over an assessment process | lean-proved | `BudgeterAt_value_eq_of_safe` |
| L3 | `lem:budgeter`.2 over an assessment process | lean-proved | `budgetedTrader_netWorth_floor` |
| L4 | `lem:budgeter`.3 over an assessment process | lean-proved | `exists_budgetedTrader_exploits` |
| L5 | `lem:tfdom` over an assessment process | lean-proved | `AssessmentFirm.trading_firm_dominance` |
| L6 | **`MarketMaker(TF^L)` satisfies `LIC_L`** | lean-proved | `AssessmentFirm.no_efficient_trader_exploits` |
| L7 | nonemptiness is not a hypothesis of the lift | lean-proved by omission; `witness` for the vacuity | `test_assessment.NonemptinessIsNotAPrecondition` |
| L8 | global nesting is not a hypothesis: an assessment process with `Live 1 ⊄ Live 0` | witness | `lateAllTrueLive_not_globally_nested` |
| L9 | the two nestings coincide for finitely-determined families, and `PC(D)` is one | lean-proved | `Assessment.live_subset_of_finiteDetermined`, `finiteDetermined_consistentWith` |
| L10 | resurrecting a world breaks the floor at the resurrected world | witness | `test_assessment.ResurrectionBreaksTheFloor` |
| L11 | deductive specialization: the generalized Budgeter's value equals the source's at every date and world | lean-proved | `BudgeterAt_ofDeductiveProcess_value` |
| L12 | `LIC_L` at `L = PC(D)` **is** `LIC_D` | lean-proved | `exploits_ofDeductiveProcess` |
| L13 | **the generalization is proper**: an assessment process that is `PC(D_n)` for no deductive process | lean-proved | `allTrueLive_not_deductive` |
| L14 | the generalized Budgeter is a different function when `L` differs | witness | `test_budgeter.TheWorldProcessChangesTheScaling` |
| L15 | support-local nesting is what the construction queries, and is weaker on the queried supports | witness | `test_assessment.SupportLocalNestingIsWeakerThanGlobal` |

### Force

| # | statement | class | declaration |
|---|---|---|---|
| F1 | extremal pinning `max_W ⟪ζ,W−P⟫ = Σ_φ[ζ_φ⁺(1−P_φ)+ζ_φ⁻P_φ]` | exhaustive-finite | `test_enforcement.ExtremalPinning` |
| F2 | the enforcement inequality `Σ_j β_j g_j² ≤ ⟪ζ_E,x−P⟫` at any region point | lean-proved | `weighted_square_le_pair` |
| F3 | conformance `Σ_j β_j g_j² ≤ ε + M` at the market maker's contract | lean-proved | `weighted_square_le_slack_add_volume` |
| F4 | **per-row tolerance: `β_j ≥ (ε+M)/δ²` *and* `0 < ε+M` give `g_j ≤ δ`** | lean-proved | `rowViolation_le_of_intensity_ge` |
| F5 | the compiled position is a `Strategy n` with legal rank, finite support and continuous coefficients | lean-proved | `enforcementStrategy`, `coefficientFeature_rank_le`, `enforcementStrategy_support`, `coefficientFeature_continuous` |
| F6 | **its exact rational value is the quantity F2–F4 bound** | lean-proved | `marketValueRat_enforcementStrategy` |
| F7 | intensities are `EF.const` leaves of a term with no history argument, so they cannot answer the realized violation | lean-proved (rank) + witness | `coefficientFeature_rank_le`, `test_regressions.IntensityIsFixedBeforeThePrice` |
| F8 | exact enforcement at zero slack and no opposing volume | lean-proved | `le_pair_of_contract_zero` |

### Coherence measure

| # | statement | class | where |
|---|---|---|---|
| C1 | `dist_∞(p,K) = sup_{‖c‖₁≤1}(inf_{x∈K}⟪c,x⟫ − ⟪c,p⟫)₊`, and `inf` over `conv V` is `min` over `V` | derived | `PROOF_CLOSURE.md` §V |
| C2 | soundness: no support-function row reports more than the distance | lean-proved | `CoherenceModulus.gap_le_of_mixture` |
| C3 | net modulus `δ + mesh`, with Lipschitz constant `1` | lean-proved | `CoherenceModulus.gap_le_of_net_cover` |
| C4 | the constant `1` is attained, so `δ + mesh` is sharp | witness | `test_coherence.TheLipschitzConstantIsOne` |
| C5 | **arbitrary presentations are not intrinsic**: ratio `1/e`, unbounded, with both presentations cutting out the same region | witness | `test_coherence.ArbitraryPresentationsAreNotIntrinsic` |
| C6 | **the exact dual-distance presentation**: a finite rational family, independent of the price, with `max_j g_j(p) = dist_∞(p,K)` for every `p` | derived + exhaustive-finite | `PROOF_CLOSURE.md` §V; `test_coherence.ExactDualDistancePresentation` |
| C7 | the exact family is world-inclusive by construction | lean-proved | `IntrinsicCoherence.rhss_le_pair_at_world` |
| C8 | the exact family depends on `K`, not on the generators | exhaustive-finite | `test_coherence.TheExactFamilyIsCanonical` |
| C9 | a coarse net under-reports, sometimes to zero at distance `1/3` | witness | `test_coherence.TheNetIsAnApproximationAndTheExactFamilyIsNot` |
| C10 | affine logical equalities do not cut out full coherence | witness | `test_deduction.AffineRelationsAreNotEnough` |

### Safety and preservation

| # | statement | class | declaration |
|---|---|---|---|
| P1 | the realized aggregate splits into ordinary firm plus added trader | lean-proved | `EnforcementPreservation.realizedAggregate_netWorth` |
| P2 | assessed liability `−B` gives the ordinary aggregate upside `1 + B` | lean-proved | `EnforcementPreservation.realizedFirm_netWorth_le` |
| P3 | **bounded assessed liability ⟹ `LIC_L` preserved** | lean-proved | `EnforcementPreservation.no_efficient_trader_exploits` |
| P4 | the liability identity with deficits | lean-proved | `weighted_square_sub_deficit_le_pair` |
| P5 | world-inclusive presentation ⟹ nonnegative value at every plausible world | lean-proved | `pair_nonneg_of_mem` |
| P6 | per-date nonnegativity sums to cumulative nonnegativity | lean-proved | `EnforcementPreservation.netWorth_nonneg_of_day_nonneg` |
| P7 | nonnegative expectation under `C` does not give nonnegative value at each live world | derived | `test_semantics.ExpectationIsNotWorldwise` |
| P8 | the support-capacity bridge `E_t(ω) ≥ (a − (1−θ)U)/θ`, `U = max_gain` | derived | `test_semantics.SupportBridge` |
| P9 | small capacity coexists with large worldwise loss | witness | `test_semantics.SmallSupportHidesLargeLoss` |
| P10 | a region excluding a live world at every date can be enforced forever, safely | witness | `test_contract.SafeWithoutWorldInclusiveness` |
| P11 | fixed-depth persistent exclusion against growing volume diverges | witness | `test_contract.UnsafeWhenDepthDoesNotDecay` |
| P12 | losing world-inclusivity persistently produces an exploiting trader | witness | `test_safety.SupportCoverageFailure` |

### Traderized deduction

| # | statement | class | declaration |
|---|---|---|---|
| D1 | `Live(Δ(PC(D_t))) = PC(D_t)`, both directions, no hypothesis on `π` | derived | `test_semantics.DeductiveSemanticRecovery` |
| D2 | `K_t^D = conv(PC(D_t)|_{Φ_t})` is the coherence polytope | derived | `test_deduction.SupportPresentation` |
| D3 | **zero liability at every date and every plausible world** | lean-proved | `DeductiveEnforcement.enforcement_day_value_nonneg`, `enforcement_netWorth_nonneg` |
| D4 | **the modified market satisfies the ORIGINAL `LIC_D`**, via the source's own dominance theorem | lean-proved | `DeductiveEnforcement.no_efficient_trader_exploits_of_worldInclusive` |
| D5 | the criterion form, as the dependency's own `IsLogicalInductor` | lean-proved | `DeductiveEnforcement.isLogicalInductor_of_computableMarket` |
| D6 | the deductive presentation is computable from the finite atom context | exhaustive-finite | `test_coherence.TheDeductivePresentationIsComputable` |
| D7 | traderized deduction changes finite prices somewhere | witness | `ENFORCEMENT.md` §4 |
| D8 | settlement leaves residue at the next date; enforcement does not | witness | `test_deduction.SettlementIsNotEnforcement` |

### Architecture

| # | statement | class | where |
|---|---|---|---|
| A1 | `C ⊆ π⁻¹(π(C))`, equality iff fibre-saturated | derived | `SEMANTIC_PROJECTION.md` Props 1–3 |
| A2 | the inclusion is strict: `Δ({00,11})` and its saturation | witness | `test_semantics.ProjectionLosesSupport` |
| A3 | same projection, different live worlds and capacities | witness | `test_semantics.SamePriceProjectionDifferentLiveWorlds` |
| A4 | support cannot encode `μ(φ) ≥ ½` against `μ(φ) ≥ ¾` | witness | `test_semantics.SmallSupportHidesLargeLoss` |
| A5 | `C_{t+1} ⊆ C_t ⟹ L_{t+1} ⊆ L_t`; the converse fails | derived | `test_semantics.Nesting` |
| A6 | `θ_t(ω) = max{μ(ω) : μ ∈ C_t}` by vertex enumeration; liveness is `θ > 0` | test-supported | `test_semantics` |
| A7 | a market maker constrained to display `P ∈ K` can have no solution | witness | `test_contract.ConstrainedMakerNeedsAnExistenceTheorem` |

A7 earns exactly this and no more: adding a strategy to the priced aggregate changes
the input to a total function, whereas constraining the maker changes the function and
the new one has no existence theorem and can be infeasible. It is not a universal
impossibility theorem.

### Cost of force

| # | statement | class | where |
|---|---|---|---|
| Q1 | the declared-quantity ceiling `(ε_t+M_t)·‖d_t(W)‖₁/δ_t` | derived | `test_contract.LiabilityCeiling` |
| Q2 | a global account with checked allocation gives `Σ_e B_e ≤ B`; the charge is additive over rows and zero on settlement rows | derived | `test_outflow.SummableAllocationsGiveAFiniteCertificate` |
| Q3 | affordable tolerance `δ_t ≥ (ε_t+M_t)·D_t/b_t`, inverting the charge exactly | derived | `test_outflow.AffordableTolerance` |
| Q4 | floors on depth *and* pressure plus a tolerance ceiling bound the funded dates by `B·δ̄/(cd)` | derived | `test_outflow.PositiveFloorsOnTwoFactorsDoBound` |
| Q5 | persistent depth at pinned tolerance is affordable forever against summable pressure | witness | `test_outflow.PersistentDepthAgainstDecayingPressure` |
| Q6 | a forever-unvindicated endorsement receives nonvacuous force within finite capital; bound `17/2` | witness | `test_outflow.ForeverUnvindicatedAndSafe` |
| Q7 | a certificate binds to date, support, row multiset **and live-world set** — all four | derived | `test_outflow.CertificateSubstitution` |
| Q8 | row permutation moves nothing; the presentation identity is the multiset of exact rational rows | derived | `test_outflow.RowPermutationIsInvariant` |
| Q9 | duplication scales position and charge by `k`; rescaling is neutral at a matched target | derived | `test_outflow.PresentationChangesTheInstalledCompiler` |
| Q10 | the global affine endorsement `c = ½B + ¼C + Σ_j 2^{-(j+2)}A_j` at `r = ¾`: closed forms `m_t = ¾ − 2^{-(t+2)}`, `D_t = 2^{-(t+2)}`, cost series `9/8` | derived | `test_normative.StaticsGenerateAForeverUnvindicatedTrajectory` |
| Q11 | both motivating trajectories run end to end through `compile_safe_force` | witness | `test_normative.MotivatingTrajectoriesRunThroughTheSafeAPI` |

**In the deductive case `Q1`–`Q6` do not bind at all.** The liability is zero for any
nonnegative intensity, so there is no affordability side-condition and `δ_t` may be
any computable positive schedule. The cost of force is a general-`C_t` problem.

### Which LI property families generalize

| # | statement | class | declaration |
|---|---|---|---|
| G1 | provability induction over an assessment process | lean-proved | `AssessmentProperties.lic_affirmed_tendsto_one` |
| G2 | the refutation half of coherence over an assessment process | lean-proved | `AssessmentProperties.lic_refuted_tendsto_zero` |
| G3 | the source's syntactic hypotheses are recovered at the deductive instance | lean-proved | `AssessmentProperties.affirmed_of_mem_stage`, `refuted_of_neg_mem_stage` |
| G4 | every `lic_*` theorem's DP-dependence factors into criterion, stagewise nonemptiness, and a world condition | derived, by hypothesis-shape audit | `PROOF_CLOSURE.md` |
| G5 | affine coherence and the Gaifman-measure support need `⋂_n L_n` nonempty, i.e. closedness | derived | `PROOF_CLOSURE.md` |

---

## Conditional, with the remaining premise visible

| # | statement | the one premise |
|---|---|---|
| X1 | the modified market is a computable belief sequence | the erasure: a first-order presentation of the recursion, as `Construction/LIACompiler.lean` builds for its own aggregate. `blocked`, not a mathematical gap — see `PROOF_CLOSURE.md` §VII for the three pieces that are present |
| X2 | intrinsic finite-time coherence `dist_∞(P_t,K_t) ≤ δ_t` | `DistanceComplete` for the exact dual-distance family: convex duality for a finite rational polytope. `derived` + `exhaustive-finite`, not kernel-checked. The composition is `IntrinsicCoherence.exists_credence_of_contract` |
| X3 | the general `C_t` theorem of `PROOF_CLOSURE.md` §VII | X1, plus a finite rational polyhedral interface for `K_t`, plus a liability bound `B` |

---

## Open

| # | statement | item |
|---|---|---|
| O1 | necessity: unbounded enforcement liability ⟹ efficient exploitation. The forward proof discards information and the enforcement trader is not in the class that could witness a converse | `PRIORITIES.md` 40 |
| O2 | a normative record yielding `C_t` | 39 |
| O3 | a general characterization of exact enforcement (`face solidity`). Nothing in the arc depends on it | — |
| O4 | what governs removing a world from support | 44 |
| O5 | presentation semantics beyond the canonicality of C8 | 46 |
| O6 | a tight size bound for the exact dual-distance family | — |
| O7 | the universal-semimeasure property family was not audited | — |

---

## Refuted, with the counterexample kept

Each has a regression in `tests/test_regressions.py` or as noted, because a withdrawn
claim that leaves no executable trace is one a later pass will make again.

| statement | why it is false |
|---|---|
| ~~the liability ceiling `M_t·max_j d_j(W)` is intensity-free~~ | positive market-maker slack breaks the offsetting the argument assumed. `test_regressions.IntensityFreeCeilingIsFalse` |
| ~~exactness is impossible whenever `K` has empty interior~~ | `K = {0}` is enforced exactly by a constant trader. `test_regressions.EmptyInteriorDoesNotImplyImpossibility` |
| ~~live worlds read off `K_t` by Dirac admissibility~~ | the definition is support, not Dirac. `test_regressions.DiracLiveWorldsAreNotLiveWorlds` |
| ~~`Ω^live = PC(D_t)` from the price region `π(Δ(PC(D_t)))`~~ | the projection obstruction makes the preimage reading false. Repaired through the semantic object, D1 |
| ~~the generalized construction is the ordinary one under a different criterion~~ | the Budgeter is a different function when `L` differs. L14 |
| ~~no finite account funds meaningful force at infinitely many dates when the depth stays above a floor~~ | the step dropped the `(ε_t+M_t)` factor. `test_outflow.DepthOnlyImpossibilityIsWithdrawn`; repaired as Q4 |
| ~~the liability certificate is invariant under row rescaling and duplication~~ | tested a compiler retuned by `1/k`. Repaired as Q8, Q9 |
| ~~`β_j ≥ (ε+M)/δ²` gives `g_j ≤ δ`~~ | at `ε+M = 0` it is met by `β_j = 0`. Narrowed by adding `0 < ε+M`, F4. `test_regressions.PerRowToleranceNeedsPositiveDisturbance` |
| ~~row conformance at `δ` gives `dist(p,K) ≤ δ`~~ | ratio `1/e`, unbounded. Repaired by C3 and C6. `test_coherence.ArbitraryPresentationsAreNotIntrinsic` |
| ~~an empty assessment process leaves the Budgeter's infimum undefined~~ | the source's `EF.listMin []` is `EF.const 1`. Corrected in `src/budgeter.py`; `test_budgeter.Preconditions` |

---

## What carries the weight

Nine Lean files, sorry-free, 438 audited results across the library. The load-bearing
declarations are L2–L6 (the lift), F4–F6 (the trader is a strategy and the algebra is
about it), P3 (preservation), D3–D5 (traderized deduction), and C2/C3 (the coherence
measure).

Two things are not kernel-checked and are named: X1 and X2.

Counts of tests are not maintained here; `tests/run.py` is what certifies the
fixtures.
