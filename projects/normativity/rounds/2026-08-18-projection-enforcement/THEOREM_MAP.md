# Theorem map — projection enforcement

Paper statement on the left, statement of record on the right. Every Lean declaration
listed is in `lean/Workspace/Normativity/Contrib/`, builds with no `sorry`, and prints
axioms `[propext, Classical.choice, Quot.sound]` (some print a subset). The `#print
axioms` lines are at the foot of each file and are re-run by `tests/audit_axioms.py`.

Section numbers refer to the draft of 2026-08-18. Where this pass recommends a change
to the paper's statement, the recommended form is what is mapped, and `PAPER_AUDIT.md`
says why.

## `ProjectionForce.lean` — the algebra, presentation-free

Nothing in this file mentions a market, a trader, a row or a presentation. It is the
variational inequality and four consequences.

| paper | Lean |
| --- | --- |
| the fragment inner product and Euclidean distance | `ip`, `sqDist`, `dist2` |
| `q` is the nearest point of `K` to `p` — the only property used | `IsNearestPoint` |
| the enforcement position `ζ = λ(q − p)` | `shares` |
| §6.3 force inequality, intrinsic form: `λ‖q−p‖² ≤ ⟨ζ, y−p⟩` for `y ∈ K` | `force_inequality` |
| §8.1 the day's value is nonnegative at an admitted point | `value_nonneg_of_mem` |
| §8.3 liability at an arbitrary point | `liability_inequality` |
| §8.3 liability once the price conforms to `δ`: `≥ −λδ d₂(w,K)` | `liability_calibrated` |
| §10.6 the `ℓ^∞` conclusion, from the Euclidean one at the same `δ` | `sup_conformance_of_dist2` |

Supporting: `sqDist_nonneg`, `dist2_nonneg`, `sq_dist2`, `sqDist_comm`, `dist2_comm`,
`ip_self`, `ip_add_right`, `ip_smul_left`, `abs_ip_le` (Cauchy–Schwarz),
`sqDist_le_ip_of_mem`, `abs_sub_le_dist2`.

## `ProjectionMarket.lean` — the bridge to the market Logical Induction builds

| paper | Lean |
| --- | --- |
| **(correction)** the market maker's daily contract holds at every cube point, not only at worlds | `value_le_of_forall_bitWorld`, `marketMaker_day_value_le_cube` |
| the market's own prices lie in `[0,1]` | `marketMakerHistory_mem_Icc` |
| a strategy *plays* the projection position | `Realizes`, `value_eq_ip`, `realizes_of_shares` |
| §6.4 with `M` eliminated: `λ‖q−P_n‖² ≤ ε_n + absBound(τ_n)` | `sqDist_le_slack_add_absBound` |
| §6.4 the intensity that buys the tolerance: `λ ≥ ρ_n/δ² ⟹ d₂(P_n,K) ≤ δ` | `dist2_le_of_intensity` |
| §8.3 the day's assessed loss | `day_value_ge` |
| §8.1 the day's assessed loss at an admitted world is nonnegative | `day_value_nonneg` |

The first row is the one the paper is currently missing; see `PAPER_AUDIT.md`.

## `ProjectionCompiler.lean` — legality, with the boundary stated

The two external facts are hypotheses and data, never axioms. See `DECISION_MEMO.md §C`
for the exact statements and `COMPUTABILITY.md §1` for the active-set derivation.

| paper | Lean |
| --- | --- |
| the fragment, as computable data | `Fragment`, `Fragment.toFinset`, `Fragment.sum_eq`, `Fragment.sum_eqQ` |
| a rational affine form on the fragment | `AffineForm`, `AffineForm.evalR`, `AffineForm.evalQ` |
| it compiles to an expressible feature of rank `≤ n` | `affineEF`, `affineEF_rank_le`, `affineEF_denote` |
| a max–min representation, as data | `Group`, `Rep`, `groupEF`, `repEF`, `groupEval`, `repEval` |
| the compiled max–min term is legal and denotes the represented value | `groupEF_rank_le`, `repEF_rank_le`, `groupEF_denote`, `repEF_denote` |
| exact rational semantics, matching the real one | `affineEF_denoteRat`, `groupEF_denoteRat`, `repEF_denoteRat` |
| the compiled enforcement coefficient | `coefEF`, `coefEF_rank_le`, `coefEF_denote` |
| §6.2 the enforcement strategy, as executable code | `projectionStrategy` (a `def`) |
| its traded support is exactly the fragment | `projectionStrategy_support` |
| its coefficients are continuous, which the fixed point needs | `coefEF_continuous` |
| it realizes the projection position | `projectionStrategy_realizes` |

## `ProjectionBudget.lean` — the budget, and deduction

| paper | Lean |
| --- | --- |
| cumulative value at an arbitrary point; net worth is the case of a world | `cumValue`, `netWorth_eq_cumValue` |
| per-date bounds sum | `cumValue_ge_of_dayBounds` |
| §8.3 **(recommended form)** the intrinsic trader budget, no nesting hypothesis | `cumValue_ge_of_projection` |
| §8.1 **(recommended form)** per-date admission gives zero risk capital | `cumValue_nonneg_of_forall_mem` |
| §8.1 **(new, negative)** admission at the final date does *not* bound the budget | `late_admission_is_not_enough` |
| §10.3 the day's deductive enforcement value is nonnegative | `deductive_day_value_nonneg` |
| §10.5 traderized deduction preserves the original criterion | `no_efficient_trader_exploits_of_projection` |
| §10.6 finite-time Euclidean coherence | `deductive_dist2_le_of_intensity` |
| §10.6 **the headline**: both, plus the paper's `ℓ^∞` form | `deductive_projection_end_to_end` |

The witness objects for the negative result are `wAtom`, `wFrag`, `wHistory`, `wWorld`,
`wRegion`, `wProj`, `wLam`, `wTrader` with `wRealizes`, `wLam_nonneg`, `wNearest`.

## `ProjectionCalibrated.lean` — the cube extension and the calibrated construction

| paper | Lean |
| --- | --- |
| a region constrains only the fragment's coordinates | `FragmentLocal` |
| the fragment target extended off the fragment by the displayed prices — a device for one inequality, **not** a credence | `extend`, `extend_of_mem`, `extend_of_not_mem` |
| the extension changes neither the distance nor what the trader trades | `sqDist_extend`, `dist2_extend`, `ip_extend`, `realizes_extend` |
| the extension is a legal cube point, so the cube hypothesis is discharged | `extend_mem_cube` |
| extending a nearest point leaves it a nearest point | `isNearestPoint_extend` |
| §6.4 market resistance `ρ_n = ε_n + A_n` | `resistance`, `resistance_pos` |
| the calibrated intensity `λ_n = ρ_n/δ_n²` | `calibratedIntensity`, `calibratedIntensity_pos` |
| the day charge identity `λ_n δ_n = ρ_n/δ_n` — **only at the calibrated value** | `calibratedIntensity_mul` |
| §6.4/§10.6 the calibrated tolerance theorem, cube hypothesis discharged | `dist2_le_of_calibrated` |
| §8.3 **(the paper-facing budget)** `−Σ_{k≤n}(ρ_k/δ_k)·d₂(w,K_k)` | `cumValue_ge_of_calibrated` |
| §8.1 zero risk capital, calibrated | `cumValue_nonneg_of_calibrated` |

## `ProjectionCore.lean` — the homothetic-core refinement

The preservation hierarchy, in order of strength of hypothesis:

1. **Preservation under bounded plausible downside** — the abstract criterion
   (`DeductiveEnforcement.no_efficient_trader_exploits`, merged).
2. **Generic projection liability** — arbitrary convex `K_n`, calibrated enforcement, charge
   `(ρ_n/δ_n)·d₂(w, K_n)` (`ProjectionCalibrated.cumValue_ge_of_calibrated`).
3. **Homothetic-core refinement** — `K_n` retains an `α_n`-fraction of every live
   direction, charge `((1−α_n)/α_n)·ρ_n`, **no tolerance penalty** (below).
4. **World-inclusive / deductive** — every live restriction lies in `K_n`, liability
   exactly zero (`ProjectionBudget.cumValue_nonneg_of_forall_mem`). This is the `α = 1`
   case of 3.

| paper | Lean |
| --- | --- |
| the affine interpolation step, with no Logical Induction machinery | `interpolated_lower_bound` |
| a strategy's value is affine along the segment | `ip_interpolate`, `value_interpolate` |
| the anchor's value is capped by market resistance, for *any* joined strategy | `value_le_resistance` |
| `K` retains an `α`-fraction of every live direction from the anchor `c` | `HomotheticCore` |
| at `α = 1` the condition is exactly world-inclusivity | `homotheticCore_one_iff` |
| **the homothetic-core liability theorem**, `Val_w ≥ −((1−α)/α)ρ_n`, no `δ_n` | `core_day_value_ge` |
| the same with the anchor's cube-membership discharged and the charge against `ρ_n` | `core_day_value_ge_calibrated` |
| the cumulative sum of core charges | `core_cumValue_ge` |
| preservation **from a uniform bound on the partial sums**, which a positive core does not supply | `core_netWorth_ge_of_summable` |
| `μ(φ) ≥ 1/2` has a `1/2`-core against `P = [0,1]`, so the charge is `ρ_n` | `halfSpace_hasCore`, `halfSpace_core_factor` |
| `μ(φ) = 1/2` has **no** positive core against the same `P` | `equalityRegion_hasNoCore` |

Four conditions the theorem deliberately keeps apart, since they are not equivalent: a
pointwise core at each live world (what `core_day_value_ge` consumes, and the weakest); a
core relative to the convex hull of the live restrictions (implied by the pointwise one on
extreme points when `K` is convex); an ambient interior condition (neither implies nor is
implied by either); and a cumulative bounded-liability condition (strictly more than any of
them — `core_netWorth_ge_of_summable` takes it as a hypothesis).

## `EnforcedComputation.lean` — Debt B, reduced to the source's own boundary

| paper | Lean |
| --- | --- |
| an enforcer presented as finite syntax | `EffectiveEnforcer`, `EffectiveEnforcer.strategy` |
| the same enforcer as an `AdaptiveTrader`, so the preservation chain applies unchanged | `EffectiveEnforcer.adaptive` |
| the day's aggregate from a decoded stage table | `enfAggregateFromStages`, `enfAggregateFromStages_eq_aggregateAt` |
| the modified bounded recurrence | `enfPrefixFromStagesAtFuel`, `enfPrefixAtFuel` |
| more fuel never loses a successful run | `enfPrefixFromStagesAtFuel_mono_success`, `enfPrefixAtFuel_mono_success` |
| some fuel always suffices | `exists_enfPrefixFromStagesAtFuel`, `exists_enfPrefixAtFuel` |
| every successful bounded run **is** the semantic construction | `enfPrefixFromStagesAtFuel_sound`, `enfPrefixAtFuel_sound` |
| the bounded exact rational quote evaluator | `enfEncodedQuote`, `enfEncodedQuoteAtFuel`, `enfEncodedQuoteAtFuel_sound` |
| **the one remaining boundary** | `EnforcedBoundedEvaluatorCompiler` |
| minimization over the fuel clock | `EnforcedBoundedEvaluatorCompiler.quote_computable`, `exists_quote_code` |
| §12 Debt B: **the modified market is computable** | `EnforcedBoundedEvaluatorCompiler.toComputableMarket` |
| §10.5 the criterion with no computability premise | `isLogicalInductor_of_compiler`, `isLogicalInductor_of_compiler_of_worldInclusive` |

## `ProjectionEnforcer.lean` — the effective input interface

| paper | Lean |
| --- | --- |
| an affine form as finite data | `FinAffine` (`List ℚ × ℚ`), `FinGroup`, `FinRep` |
| reading finite data against a coordinate list | `FinAffine.toAffineForm`, `FinGroup.toGroup`, `FinRep.toRep`, `repAt` |
| §10.6's effective inputs: fragment schedule, tolerance schedule, representation schedule | `ProjectionSchedule` |
| the effectiveness requirement, and the whole of it | `ProjectionScheduleComputation` |
| the calibrated intensity, read off the ordinary aggregate's syntax | `ProjectionSchedule.intensity` |
| §6.2 **the enforcement trader, as effective data** | `ProjectionSchedule.enforcer` |
| its support is the day's fragment | `ProjectionSchedule.enforcer_support` |
| the compiled trades are the projection position | `ProjectionSchedule.enforcer_realizes` |
| §10.6 per-date Euclidean conformance for the schedule's market | `ProjectionSchedule.dist2_le_tol` |
| §10.6 **the theorem of record** — source-original LIC, Euclidean conformance, `ℓ^∞` form | `ProjectionSchedule.end_to_end` |
| the same with the representation hypothesis made definitional | `ProjectionSchedule.end_to_end_canonical` |
| §13 eventual coherence on every fixed finite set | `ProjectionSchedule.eventual_coherence` |

## What is reused unchanged from the merged row work

`no_efficient_trader_exploits_of_projection` is
`DeductiveEnforcement.no_efficient_trader_exploits_of_worldInclusive` instantiated. That
chain — `realizedFirm_netWorth_le`, `no_efficient_trader_exploits`,
`isLogicalInductor_of_computableMarket`, `enforcement_netWorth_nonneg` — is generic in
the added trader and was not modified by this pass. Neither were
`TraderizedEnforcement`, `AssessmentProcess`, `AssessmentFirm`, `AssessmentProperties`,
`EnforcementStrategy`, `EnforcementPreservation`, `CoherenceModulus` or
`IntrinsicCoherence`.

## Python, for what Lean does not carry

`src/projection.py` and `tests/test_projection.py`, exact `Fraction` arithmetic
throughout, twelve tests:

| what | test |
| --- | --- |
| the projector is certified by its variational inequality | `test_variational_inequality_certifies_every_case` |
| and no grid point of the region is closer | `test_no_grid_point_is_closer` |
| admitted points are their own projections | `test_projection_fixes_admitted_points` |
| the force inequality, at displayed data | `test_force_inequality` |
| nonnegative value at admitted points | `test_value_nonnegative_at_admitted_points` |
| the liability bound, checked squared so no root is taken | `test_liability_is_calibrated` |
| the intensity step | `test_intensity_buys_the_tolerance` |
| `ℓ^∞ ≤ ℓ²` | `test_sup_distance_never_exceeds_euclidean` |
| rows are the single-halfspace projection | `test_single_halfspace_positions_agree` |
| §9.1 presentation dependence, exactly | `test_rescaled_rows_shrink_the_violation_without_moving_the_region` |
| the intensity is presentation-free | `test_projection_intensity_is_presentation_free` |
| the late-admission counterexample, numerically | `test_cumulative_value_is_negative` |
