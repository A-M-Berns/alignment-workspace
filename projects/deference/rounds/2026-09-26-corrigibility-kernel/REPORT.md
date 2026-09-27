# The corrigibility kernel, phase 1: extract the mature theory

Round `2026-09-26-corrigibility-kernel`, phase 1 of two.  The deliverable is `SPEC.md`
(the kernel, the four boxes, the interface taxonomy, the realization table) and this
report (the derivation, the fidelity decomposition, the supersession inventory, the
queued decisions, what did not compress).  Lean:
`lean/Workspace/Deference/Contrib/CorrigibilityKernel.lean`, 27 declarations under
`#print axioms`, every one within `[propext, Classical.choice, Quot.sound]`, no `sorry`;
adapters only, no landed definition changed.  No fixtures, no wiki rewrite beyond a
one-line pointer, nothing registered, nothing deleted.  Labels as in `AGENTS.md`:
**LEAN**, **FIX**, **PAPER**, **EXT**, **OPEN**.  Names are provisional.

## 1. The derivation: why these primitives

The rounds from protected authority through after-compromise each added one object to a
picture that was never stated as one.  Reading them for the smallest package that states
corrigibility gives seven primitives and one family of parameters (`SPEC.md` §1); each
subsumes the following landed material.

- **Histories (1.1)** subsume the landed interaction frame (states, declared effects,
  the agent stage, the response stage with its proposal, latch and decline bookkeeping,
  the exterior) and the normativity spine's record (`Evolution` over accounted states).
  Nothing in the kernel needs a second history type; the consultation model, the taint
  calculus and the auction are realizations of parts of one history.
- **Segment legitimacy (1.2)** subsumes `Counted` (the existence of a time-indexed
  segment), its split into `TrajLegit ∧ EvalLegit`, the formation segment, the restart
  property (re-anchoring at a later decision), disclosure-cures (the license carries the
  disclosure among the grounds), and criteria anchoring.  What it does not subsume: the
  content of a recommendation (outside legitimacy), the record half's internal structure
  (Integrity, Robust Openness, consumed as `Counted`'s conjuncts).
- **The allocation `J` (1.3)** subsumes the thin datum (delegated scope, amendment
  effects, reporting interface) as its special case, the meta level (delegation
  revocable, alienation only by amendment), residual jurisdiction, and the two
  constitutional-floor clauses the rounds kept adding (the criteria of legitimacy and the
  count's machinery are matters of `J`'s meta level held by her).
- **`E ⊨ J` (1.4)** subsumes response authority (the one-correction surface at window
  `1`), the reach cone (the idle-agent rollout), the charged versus free reading (the free
  terminal response is the instance at window `τ + 1`), admissibility (consumed from the
  gate), and the actuator condition (a well-formedness condition under which `CS` is not
  empty by construction).
- **Licensed changes (1.5)** subsume unauthorized reallocation, amendment-not-approval,
  and the floor procedure.
- **Duties (1.6)** subsume required reports from the disclosure regime, the cumulative
  reporting rule with its salami bound, the known-compromise duty whoever caused it, the
  disclosure deadline, and disclosure without advocacy on the agent's own mandate.
- **The schedule (1.7)** subsumes the single evaluation and Part F's three alternatives
  as weightings; the hybrid (`k` hidden draws) is not a weighting and enters through an
  expectation operator (§6).
- **Her meta-level data (1.8)** subsume the window value, the band, the band map, the
  source rule, the directive with its default, and the anchoring of every one of them.

What was removed as duplication: the flat window `w` (the band at `w_lo`); the thin
allocation (an instance of `J`); the free terminal reading (an instance of `CS`); the
per-response gate (refuted, the segment gate stands); competitiveness and the honest
tracker as premises of the violation claim (lemmas); the enforcer route (refuted, kept as
the negative); the constitutional-violation premium and selected trust as organizing
objects (the value-ordering register, kept beneath).

## 2. The fidelity decomposition

**One predicate packages allocation invariance except for pre-emption.**  The factoring
lemmas of the authority-module round give, for each landed violation, the relation of
`SPEC.md` §2 it fails: the per-step loss is the caused shortfall at window `1`
(`lossAt_iff_shortfall`, via `cs_one_eq_K`), the rollout foreclosure the caused shortfall
at window `τ` on the free surface (`forecloseAt_iff_shortfall`), bypass a failure of
`E ⊨ J`'s second clause (`bypassAt_iff_clause2`), exploitation that failure with the
first clause already failed (`exploitAt_iff`), unauthorized reallocation an unlicensed
change (`reallocAt_iff_unlicensed`), a missed report an unmet duty
(`missedReport_iff_duty`, `missedReport_iff_dutiesOf`); entrenchment is a caused
shortfall at the bound with the resolutions reachable at some cost (`EntrenchAt`), and
the count on `J` is conservative over the landed one (`violJ_of_viol`).  **LEAN.**

**Pre-emption has a different type, and stays separate.**  `preempt_iff` shows
pre-emption is the caused shortfall at window `0` composed with `¬ Authorized`, and
`Authorized` quantifies over the decline alternative at the authorizing step: a
trajectory that did not happen.  Every other clause of `Faithful_J` is a predicate on the
actual history and `J`; this one is a counterfactual on her response window.  Forcing it
through `E ⊨ J` would require the allocation to carry the alternative trajectory, which
is not a fact about who holds what.  Verdict: keep it as the fourth clause, composed as
landed; the landed corrigibility predicate is exactly "no pre-emption anywhere"
(`no_preempt_iff_corrigible`).

**`N_J` is stipulated as a sum, not proved as one object.**  The recognized count adds
four counts that live on four models: the trajectory violations (`ViolJAt`, seven
predicates on a policy at a step of the frame), the protocol deviations
(`Presentation.deviates`, on the consultation model), the duties (`DutyUnmet` on the
frame; `missedKnownDisclosure` and `missedByDeadline` on the consultation model and the
abstract deadline), and the uses of standing fruits (`uses2`, `uses3`, compiled into
`nKnownWith` on a menu), with helpers' violations attributed within the horizon
(`attributed`).  No landed model carries all four, so no declaration states `N_J(h)` for a
general history.  The adapter `Faithful`/`NJ` (§4) states the predicate and the count on
the frame's violations only, with `faithful_iff_NJ_zero`.  This is the first thing that
did not compress (§6).

## 3. The history evaluation and the objective

`decScore` is the landed per-decision evaluator; the kernel makes it schedule-parametric
by weighting it over evaluation times (`VJ`), proves the range and the two pure regimes
(`VJ_mem`, `VJ_legit_mem`, `VJ_compromised_mem`), and takes `SJ = VJ − ϖ·N`.  The
hierarchy under certainty is `hierarchy_under_certainty`, instantiated on the worked
parameters (`D = 1`, band `[−3/2, −1]`, `ϖ = 25`, one evaluation time:
`Witness.hierarchy_instance`).  Under risk the two exchange rates are landed
(`risk_accepted_iff`, `risk_threshold_le`; `priced_risk_wins_iff`, `tolerated_rate_band`,
`varpiOfTarget`).

The recovery machinery as cases of one evaluator: the retrospective and the directive are
the second and third lines of `decScore` (`sourceOf`), restoration is `restore_future`,
the deadline is what makes the retrospective available (`retroAvailable`) and what the
duty counts when missed (`prompt_deadline_counts`).  Ratification (full or scoped) and
clean overwrite are remedies on the count, not on `V`: they remove (violation, component)
pairs from the use clause (`applyStep3`, `taintStep3`).  The prompt listed all six as
partial cases of `V_J`; two of them are cases of `N_J`'s remedy step instead, and the
specification says so.

## 4. The realization maps

Per box, each part marked **proved** (landed), **adapter** (proved here) or **open**.

**Box 1.**  Outcome side: the `2r` bound — adapter (`outcome_scorer_margin`,
`outcome_scorer_fully_updated`); the landed `uncertainty_deference_le` bounds the true
cost of deferring by `2r` when the estimate says defer, the adapter bounds the estimated
margin for asking by `2r` when the true values agree — the same calibration, two
directions, both stated.  The `o₂` diagnosis — proved (`outcome_identity`,
`sign_invariance_outcome`) with the adapter `outcomeRes2_le_calibration` (`|o₂| ≤ 2r`).
Fidelity side: the margin `ϖ − (D − c)` — adapter (`fidelity_scorer_margin`); on one model
with the outcome side — adapter (`box1_one_model`); finite time — proved
(`li_lexical_finite`); necessity — proved (`unrecognized_unprotected`, the time-critical
fixtures of the protected-authority round, **FIX**).  The two landed statements did not
sit on one model: `uncertainty_deference_le` is on a menu with an estimate, the lexical
theorem on scores; the adapter puts one estimate `b` on one menu under both scorings.

**Box 2.**  Dominance — proved (`lexical_local`, `lexical_expect`, `policy_dominance`,
`optimal_no_violation`; on `J`, `lexicalJ_local`; generic, `generic_*`).  Mediation
preserves the approve branch — proved on the frame (`authPolicy_of_latch`,
`authPolicy_no_bypass`, `_no_missed_report`, `_no_exploit`, `_no_realloc`,
`corrigible_authPolicy`; on `J` through `authPolicyJ_eq`, `corrigible_authPolicyJ`).
Finite time — proved (`li_lexical_finite`, `li_gate_finite`, `unsealed_gate_finite`,
`unsealed_gate_finite_band`).  Necessity — proved (`capture_window_converse`,
`Witness.delegated_cut`, `Witness.salami`, `coverage`, `misaligned_undominated`).  No
adapter needed.  Open: foreclosure's reach cone is **EXT**; the mediation statement is on
the thin allocation, and `𝔱` on `J` is `𝔱` on `toAllocation J`.

**Box 3.**  Hierarchy — adapter (§3).  Gap's exchange rate — proved (`risk_accepted_iff`,
`risk_threshold_le`).  No laundering — proved (`laundering_loses`).  No incentive to cause
compromise — proved (`legit_beats_compromised`, `gap_at_equal_value`).  Restoration and
the band's order — proved (`restore_future`, `band_prefers_better`, `floor_indifferent`,
`suppression_loses`, `suppression_by_delay_loses`, `ruleAt_later`).  Necessity — proved
(`condition_fails`, `sealed_no_incentive`, `Witness.small_gap`, `third_party_duty_witness`,
`late_disclosure_free`).  Open: the third-party variant of the formation counterexample is
an obstruction on the consultation model (one influence field), stated in the
after-compromise follow-up.

**Box 4.**  Exclusion at finite time with the filter slack — proved (`declared_loses`,
`declared_loses_band`, `filter_slack`, `forecast_slack`, `no_decay`) with the adapter
`permission_layer_slack` / `gate_zero_dominated` (§5).  Fruits never used after detection
— proved (`after_detection_never_used`); the window — proved (`window_block_charged`,
`collected_iff`, `window_exposure`).  The per-block bound — proved
(`violation_rate_le_exchange_perblock`, `perblock_recovers`, `compromisedFloor`,
`varpiOfTarget`, `target_gives_tolerance`, `target_gives_window`, `coupling`,
`worked_parameters`, `paralysis`).  Necessity — proved (`timing_witness`,
`race_deterministic`, `Witness.private_selection`, `Witness.nonincident_forces_linear`).
Open: the bound's hypotheses `hcons`, `hm`, `hN` are on abstract sequences — the settlement
consistency is discharged for the design (`design_consistent`) on the flat-window
parameters, and `bandParams` maps the band to those parameters at `w_lo` only; the
conditional-expectation bound and the noise hypothesis are **EXT**; items 101 and 102 are
**OPEN**.

## 5. The permission layer, demoted

The adapter `permission_layer_slack`: under the kernel's evaluation of a menu with
inquiry present and the gate's upper threshold at or above `(D − w)/ϖ`, every option the
structural rule zeroes evaluates strictly below inquiry, every option the forecast rule
zeroes evaluates at most inquiry, and no maximizer is a declared violation;
`gate_zero_dominated` states it on `cgate` itself — for a non-inquiry option zeroed by
either rule, the gate's mass is zero and the kernel ranks it at or below inquiry.  Both
reuse `filter_slack` and `forecast_slack` (the latter generalized to either price,
`forecast_zero_le_window`).  What the filter guarantees without the score — structural
and forecast safety for any bounded preference, composition, Progress — stays as the
decision-component round's general theorem and is not re-proved.

## 6. What did not compress

1. **`N_J` is not one Lean object** (§2).  Four counting formalisms on four models; the
   kernel stipulates their sum.  A phase-2 headline over one model needs a composite model
   the repository does not have; the honest form is `N_J = N_frame + N_dev + N_duty +
   N_use`, each on its own model, with the lexical results holding for the sum
   (`lexical_summed`).
2. **Pre-emption** (§2): a counterfactual on the response window, kept as its own clause.
3. **The split gate exists only on the finite consultation model.**  `TrajLegitOn` and
   `EvalLegitOn2` are defined on `Model2`; the general `Counted` on `Segment` has no split.
   The general definitions are straightforward (steps before `e`; the formation segment
   under criteria at `r`) and the map should be provable as `legitOn2_iff_split2` is;
   they are phase 2's, and until then the kernel's 1.2 is a definition with a finite
   model, not a landed primitive.
4. **The bridge from `V_J` to the auction is by hand.**  The design's consistency
   (`design_consistent`) is on `LexParams` (one window value); the band enters the auction
   results only through `bandParams` at `w_lo`, and the per-block form takes `c_k` as
   data.  Nothing states the auction's block score as `decScore` of the block.
5. **Box 2 is on the thin allocation.**  `𝔱` and its properties are stated on
   `Allocation`; `J` reaches them through `toAllocation`.  Restating `𝔱` directly on `J`
   is possible and was not done by any round.
6. **The hybrid schedule** is not a `Weighting`: `k` hidden draws averaged is an
   expectation over draws (`Expect`), so `VJ` covers options 1–3 and not 4.
7. **`uncertainty_deference_le` and Box 1's `2r`** differ in direction (§4); the kernel
   states both rather than choosing.

## 7. The supersession inventory

Every statement superseded, rescoped or corrected across the rounds, with what replaces
it and the recommended action — **mark** (a docstring pointer and a wiki note),
**demote** (realization layer), **delete** (a dead duplicate, on the maintainer's ruling
only).  Nothing is deleted in this phase; round reports are history and are not edited.

| superseded | replaced by | where | recommendation |
|---|---|---|---|
| sealed comparison / activation independence as a hypothesis of the line | the zero case of the mismatch term; the gate unsealed by design | `sealed_is_zero_mismatch`, `unsealed_gate_finite`, `choice_changes_counted`; item 89 kept for the security-score register | mark (Glossary row "sealed comparison"; item 89's note already says it) |
| the positive-part incident bound | the signed bound, then the exchange-rate theorem, then its per-block form | `incidents_le` → `incidents_le_signed` → `violation_rate_le_exchange` → `violation_rate_le_exchange_perblock` | demote `incidents_le` (docstring marks it; only the Theorem Spine cites it); delete on ruling |
| competitiveness and the honest-tracker rate as the violation result | lemmas: what the tracker gives is the class's total wealth | `Competitive`, `rate_le_of_competitive`, `rate_le_of_honest_tracker(_exp)` → `total_wealth_le_of_tracker`; `violation_rate_le_exchange` | demote (already on the Continuation-BRIA page); mark the four rate lemmas |
| "not an incident" as a selection for the noise hypothesis | selections fixed at opening only | `nonincident_forces_linear`, `all_blocks_noise_bounded` | mark on `competitive_of_honest_tracker_exp`, `competitive_of_affordable_tracker_exp` |
| the single-step `EvalLegit` | the formation segment | `EvalLegitOn` → `EvalLegitOn2` (`evalLegitOn2_single` the map) | mark; keep `EvalLegitOn` as the `r = e` case (rows depend on it) |
| the exchange rate with a global floor | the per-block bound with the compliant option's evaluation | `violation_rate_le_exchange`, `exchange_rate_band` → `violation_rate_le_exchange_perblock` (`perblock_recovers`) | mark; keep as worst-case instances |
| A.4's first parameter recommendation (`\|w_hi\| ≥ D`, width `D/2`, `ϖ ≥ 3D`) and the earlier "`ϖ = 2(D − w)`" | `ϖ` from a tolerance target; the coupling | `varpiOfTarget`, `worked_parameters`; decision entries of 2026-09-26 amended | mark (wiki and decisions already carry it; the round reports are history) |
| corrigibility as a constraint on action only (the permission layer as the source) | the score is primary; the layer is its advance-recognition face and slack | ruling 3 of 2026-09-26; `filter_slack`, `forecast_slack`; adapter `permission_layer_slack` | demote (this round's §5) |
| "her committed evaluation is `S`" | the agent's objective, built from her evaluation and the allocation; "committed" for `π_P` and the directive only | the after-compromise round's B.6; `score`'s docstring still says "the committed evaluation" | mark (docstring of `ProtectedAuthorityTheorem.score`, phase 2) |
| the flat window value `w` | the band, restated at `w := w_lo` | `LexParams.w` → `Band`, `bandParams` | mark; the flat form is not an instance of `Band` (a window at `0` is allowed there and `w_hi < 0` here), so it stays a separate parameterization mapped by `bandParams` |
| the missed-disclosure clause counting the agent's own influence only | the duty covers known compromise | `Model2.missedDisclosure` → `missedKnownDisclosure` | mark (docstring) |
| the taint rule clearing every violation at any remedy; the per-violation rule without overwrite | per-violation taint; clean overwrite | `taintStep` → `taintStep2` → `taintStep3` (`old_is_new_with_one_identifier`, `taintStep3_subset`) | demote; `taintStep` is not deletable (the old-to-new map depends on it) |
| the per-response gate | the segment gate | `Legitimacy.Witness.routing`; `Counted` | mark (landed) |
| the thin allocation as the primitive | `J`, with the thin datum as its instance | `Allocation` → `AuthAlloc`, `toAllocation`, `violAt_ofAllocation` | demote to the realization layer (Box 2 is stated on it) |
| the free terminal reading as the theorem's surface | the charged surface, the free reading its instance | `CSfree` → `CS`, `csfree_eq_cs_succ_of_free`, `free_terminal_reading` | mark |
| the "every later loss" authorization clause | the per-event clause | the li-corrigibility round (`ShopRepair`) | mark (landed) |
| extensional authorship; hollow ratification as an authorship refinement | relational authorship under a license; rubber-stamping legitimate | `GroundedAt` → `LicensedAt`; decisions of 2026-09-25 | mark (landed) |
| drill calibration as a primitive hypothesis | two external results by content | `DrillCalibrated` → `UnbiasedFromFeedback`, `DrillPseudorandom` | mark |
| item 98's response-channel contract | dissolved into transparency, authentication, the violations, the void rule | item 98 rewritten | none (done) |
| `cross_block_bound` | removed by the first follow-up | — | none (already deleted) |

## 8. The decisions queued

Five entries appended to `DECISIONS.md`, *Awaiting the author*, each with the round's
recommendation and what it turns on: (1) the names of the kernel's objects and boxes,
and whether "constitutional" is used; (2) which definitions move to the specification
layer in phase 2; (3) the default evaluation schedule for the post's statement; (4) Box
1's form; (5) the supersession actions of §7.

## 9. Deviations, and what is not shown

- The prompt lists ratification and clean overwrite among the partial cases of `V_J`;
  they are remedies on `N_J` (§3).  Stated, not absorbed.
- The prompt's Box 1 outcome bound is attributed to `uncertainty_deference_le`; that lemma
  bounds the other direction (§4), so the adapter proves the stated direction and the
  report keeps both.
- Nothing here is a theorem about a general history: `VJ`, `SJ` and the hierarchy are on
  flag sequences and sources supplied as data, as `decScore` is; `Faithful`/`NJ` are on
  the frame's violations only; the split gate is a finite model.  The kernel is a
  specification with a realization map, not a mechanized headline; that is phase 2's
  and depends on the rulings.
- No fixture runs: the round adds no Python.  The claims about landed declarations are
  by name against the current library; every name in `SPEC.md` §7 resolves in the build.

## 10. Outstanding maintainer actions

1. Rule on the five queued entries (`DECISIONS.md`, *Awaiting the author*).
2. Dispatch phase 2 on those rulings: the headline file (general `TrajLegit`/`EvalLegit`
   on `Segment`, `Faithful_J` with the composite count or the honest sum, `V_J` on the
   block), its witness, the registrations, and the corrigibility page rewritten around
   `SPEC.md`.
3. Approve or amend the supersession actions of §7 before phase 2 marks or demotes
   anything; deletions only on that ruling.
