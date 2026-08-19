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
