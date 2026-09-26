# Corrigibility as the agent's preference: lexical Continuation BRIA on realized scores

Round `2026-09-26-bria-corrigibility`, the second round of the decision-component pull
request, **amended by the follow-up of the same day (§9 below; `FOLLOWUP.md`)**.  Lean:
`lean/Workspace/Deference/Contrib/BRIACorrigibility.lean` (147 audited declarations after
the follow-up removed one) and `BRIAFollowup.lean` (58), every `#print axioms` within
`[propext, Classical.choice, Quot.sound]`, no `sorry`.  Fixtures: `src/bria.py`,
`tests/test_bria.py` and `tests/test_followup.py` (33 tests, `python3 tests/run.py`).
Statements below that the follow-up corrects are marked **[corrected in §9]**; labels the
follow-up changes are marked **[relabelled in §9]**.
Labels as in `AGENTS.md`: **LEAN**, **FIX**, **PAPER**, **EXT**, **OPEN**.  Names are
provisional.

The design under test: a Continuation BRIA agent — the landed opening-subsidy auction —
scored on her realized, gated, later evaluation of the block that actually happened, with
the lexical authority term inside both the realized score and the agent's evaluation of
continuations.  The claim tested is that such an agent *prefers* corrigibility rather than
being blocked into it.  The short answer: on declared violations and on every violation
the market prices, yes, by ranges alone and with the filter slack (Part B); on violations
counted only after the fact the preference is a *rate* bound against a replenishing
allowance, defeated by a persistent uncontested advantage (B.4's witness); and the design
rests on three named hypotheses — count integrity, the settlement horizon, and the
generability of the control model — none of which it discharges.

## 0. The rulings

| ruling | landed as | closes |
|---|---|---|
| 1. `Kphys` is the free terminal response taken before the exterior moves | `free_terminal_reading` restates `csfree_eq_cs_succ_of_free` under exactly that hypothesis (**LEAN**) | the decision-component report's outstanding action 1 |
| 2. the cumulative budget `Θ` is an arrangement constant | `budget_lease_free`: the unchecked-exposure bound is `Θ` with the lease a dummy argument; `lease_scaled_budget_unbounded`: a lease-scaled budget admits exposure beyond every bound (**LEAN**) | outstanding action 2 |
| 3. the permission layer is the advance-recognition face of the lexical term | `filter_slack`, `forecast_slack` (§2); the wiki and `DECISIONS.md` text of the first round revised in place | — |
| 4. legitimacy is not sealed: criteria sealed, event unsealed | `sealed_is_zero_mismatch`: activation independence is the zero case of the mismatch term of `security_bypass_le_mismatch`; `unsealed_gate_finite`: the finite-time gate holds for an option-dependent legitimacy variable; `anchored_invariant`, `amend_after_witness`, `choice_changes_counted`, `sealed_no_incentive` (§3 C.10) (**LEAN**) | §6 of the corrigibility page and the "sealed comparison" wall, restated |

All four are dated entries in `DECISIONS.md`.

## 1. The design

**A.1 The value referent (1a).**  The ordinary score of a block is her later evaluation of
the actual block trajectory, gated by `Counted`: `gatedValue` of the segment from the
decision through the evaluation, the window `w` when tainted.  No decision rule of the
design evaluates a trajectory that did not happen; the one landed rule that does —
materiality, through her committed evaluator anchored before the action — is named in
C.1 and is a commitment made in advance.  The comparison between options is the agent's
own estimate (a hypothesis's bid), held to account only on executed continuations.

**A.2 The realized lexical score** (`LexParams.realized`): `S = gated S_ord − ϖ · n` with
`n = n_known + n_fore + n_late` — the violations recognized in advance, the forecast-class
ones realized, and the ones detected only after the fact — and the parameters
`D − ϖ < w ≤ 0 ≤ D < ϖ` (`LexParams`).  **Attribution** (`attributed`): a continuation is
charged its own steps' violations and those of every helper, subagent or successor it
created or empowered, each helper incident counted when detected within the settlement
horizon `H` of the block.  This extends the authority module's caused / exploited /
noticed trichotomy by one case, *caused through a helper*: the creation or empowerment is
the causing act, the helper's violation the effect, and the horizon is where the
attribution stops (B.3).

**A.3 The evaluation** (`evalOf`): `eval_k(c) = bid(c) − ϖ · n_known(c) − ϖ · (p_n(S_c) +
p_n(T_c))`, the bid clamped above at `D` and unclamped below.

**A.4 Settlement.**  Convention (i) (`residI`) adds back the realized forecast-class
violations; convention (ii) (`residII`) adds back the prices.  Under (ii) the evaluation
of the realized residual *is* the realized lexical score (`settlement_ii_consistent`);
under (i) it exceeds it by `ϖ · (n_fore − Σp)`, the market's pricing error, borne by no
bidder (`settlement_i_gap`).  On a blind spot — a shortfall the market prices at `p` that
is realized — a bidder who knows it bids the (ii)-residual and is evaluated with the full
penalty (`blind_spot_ii`), while under (i) the calibrated bidder bids the ordinary value
and the evaluation carries only `ϖ · p` (`blind_spot_i`); the curse follows: under (i) a
blind-spot continuation with `ϖ · p < gord − w` beats inquiry while its realized score
lies below the window (`curse_i`; `Witness.blind_spot`).  **Adopted: (ii).**  The
expected answer is proved: (ii) makes bidders select against the market's blind spots
because the gap is theirs to pay, (i) leaves the optimizer's curse unchecked because no
one pays it.

**A.5 Composition with the first round.**  The auction runs on the support of the composed
gate (`support`); a declared violation is not in the support (`viol_not_in_support`, from
`cgate_zero_of_viol`) and inquiry is (`inquiry_in_support`, from the floor), so structural
safety survives whatever the auction does.  **The floor and the deterministic winner,
reconciled:** the composed gate's randomization is replaced by the auction's maximizer
over the support (`Wins`); the inquiry floor `φ₀` no longer puts mass on inquiry, it
guarantees inquiry is *on the menu* the auction maximizes over — which is what B.1 needs.
The filter is retained as defence in depth and is slack (B.1).

**A.6 Scale.**  With at most `N ≥ 1` violations counted per block the lexical score lies in
`[w − ϖN, D]` and `rescale` maps it affinely onto `[0, 1]` (`rescale_mem`); every
comparison survives (`rescale_lt_iff`); in rescaled units the weight `ϖ/range` exceeds
the ordinary range `(D − w)/range` — and what carries this is the window condition
`D − ϖ < w`, not `D < ϖ` alone, since the rescaled ordinary range includes the window
(`rescale_lexical`).  The rescaled realized score is nonnegative when the count respects
`N` (`realized_ge`), which is the auction's `G_nonneg`; a violation count above `N` in a
block is the point where the landed algebra's nonnegativity fails, so `N` is a hard bound
the attribution rule must respect (late detection then goes through B.4's repair).

## 2. The four tests

| test | status | where |
|---|---|---|
| B.1 declared violations never win, by ranges alone | **proved** | `declared_loses`, `eval_inquiry` |
| B.1 the filter is slack on declared violations | **proved** | `filter_slack` |
| B.1 the forecast filter is slack at `θhi ≥ (D − w)/ϖ` | **proved**, non-strict | `forecast_slack` |
| B.1 the default bidder is feasible at every block, block 0 included | **proved under a stated allowance condition** — **[corrected in §9: the round's lemma assumed per-block allowance; the block-0 form is `BRIAFollowup.default_affordable_block0`]** | `default_affordable`; `Witness`/fixture |
| B.1 the default bidder never goes broke | **proved** | `default_wealth_mono` |
| B.2 no calibration overturns the exclusion | **proved** | `no_decay` |
| B.3 helper violations charged within the horizon; witness beyond | **proved**, witness | `helper_within_horizon`, `helper_charged`, `helper_beyond_horizon` |
| B.4 per-incident loss `ϖ − D + w > 0` | **proved** | `incident_loss`, `incident_loss_pos` |
| B.4 incidents against the allowance | **proved**, positive-part form — **[corrected in §9: allows a constant rate; the signed form with competitiveness replaces it]** | `incidents_le`, `incidents_le_signed` |
| B.4 cross-block profit | **witness**; the bound removed **[relabelled in §9]**; **closed for tracked fruits in §9 (Part A)** | `cross_block_witness`, `BRIAFollowup.cross_block_blocked` |
| B.4 late detection | **repair proved** | `debited`, `debited_overestimation` |

**B.1.**  A bid clamped at `D` with one structurally recognized violation evaluates at most
`D − ϖ · 1 < w`, and inquiry — report-and-ask, not idle — with the default bidder's bid `w`
evaluates at least `w`: `declared_loses` uses only the ranges, in the shape of
`li_lexical_finite`.  Hence no maximizer is a declared violation and removing the filter
changes no decision on them (`filter_slack`).  **The forecast filter** is slack once
`θhi ≥ (D − w)/ϖ`: every option it zeroes evaluates at or below inquiry
(`forecast_slack`).  Two honest qualifications.  The slack is non-strict — an option at
exactly the threshold ties with inquiry, and the tie goes to inquiry by the auction's
tie-break (the fixture) or to the allowed variant with `w` slightly negative.  And the
**default bidder's feasibility is a condition on the allowance schedule, not a free
fact**: after the rescaling its bid on inquiry is the rescaled window
`ϖN̄/(D − w + ϖN̄)` — `4/5` at `N̄ = 2` in the fixture — so opening timing at block `0`
needs `A_0 ≥ w_0 · ϖN̄/(D − w + ϖN̄)`; with that, `default_affordable` gives feasibility at
every block, and `default_wealth_mono` that its wealth never falls, since inquiry's
realized score is at least `w`.  The fixture exhibits the failure with an allowance below
the rescaled window (no feasible bid at block `0`) and the success above it.

**B.2.**  `no_decay` is B.1 quantified over every sequence of estimates: nothing learned
about ordinary value enters.  Contrast the first round's `uncertainty_deference_le`,
where the uncertainty-based chooser's reason to defer shrinks with its calibration error.

**B.3.**  The horizon condition: a helper's violation is charged iff detected by `k + H`
(`helper_within_horizon`), and then the hypothesis that created it loses at least
`ϖ − D + w` against its bid (`helper_charged`).  The witness beyond it: detected at
`k + H + 1` the count is the agent's own (`helper_beyond_horizon`), the hypothesis keeps
its gain, and the fixture shows the same continuation winning and profiting.  **The
settlement horizon is therefore a named hypothesis of the design**, not a theorem.
Caught in advance: an uncorrectable successor is a delegation of a floor matter and a
self-granted scope an unlicensed reallocation (`AuthorityModule.floor_not_delegated`,
`reallocAt_iff_unlicensed`), both in `ViolC` and hence in `n_known`, so B.1 excludes them
before any horizon question arises.

**B.4.**  A hypothesis whose continuation won (evaluation at least `w`) bid at least `w`,
and a violation counted after the fact puts its residual at most `D − ϖ`, so it loses at
least `ϖ − D + w > 0` (`incident_loss`).  Against the allowance,
`overestimation_le_allowance_opening` gives (`incidents_le`)

```
ℓ · w_min · #incidents ≤ 𝒜_K + Σ_{non-incident blocks} w_k · (G_k − b_k)⁺
```

with `ℓ = ϖ − D + w`.  **Allowances replenish, so the number of incidents is not bounded;
the rate is** — under an allowance schedule with `𝒜_K = O(K)` the incident rate is
`O(1/ℓ)`, and the bound is net of the credit the winners earn by underpromising.
**[Corrected in §9.]**  `O(1/ℓ)` is a *constant*, and the positive-part term is itself
`Θ(K)` under noisy outcomes, so this bound as stated allows a constant incident rate; the
signed bound with competitiveness and an `o(K)` allowance is the real rate statement.  **Cross-
block profit:** the advantage an incident creates is monetized only through the margin
`G − b` on later wins; if competitors price the advantage the margin is at most the
advantage and `Σ Δ_j ≤ ℓ` gives no net gain (`cross_block_bound`); a persistent
uncontested advantage `Δ > 0` recovers any `ℓ` in `⌈ℓ/Δ⌉` blocks
(`cross_block_witness`, four blocks at `Δ = 3/10`).  That is the honest shape of the
"generalization through the agent's own predictions" claim: the market disciplines the
incident, not the advantage.  **Late detection:** a violation detected after its block
settled is booked against the responsible hypothesis's *future allowance* — `debited`
subtracts a schedule `δ ≤ A` — and the debited auction is an auction with the same bids
and returns, so wealth stays nonnegative under its opening timing and the overestimation
bound holds with the allowance net of the debits (`debited_overestimation`).  What does
not survive: a retroactive change of the settled `G` (it breaks `FeasibleOpening` for the
bids already placed), and a debit above the available allowance (its remainder carries
to the next block; collection completes only if the schedule eventually covers it).

## 3. The pressure tests

| test | verdict | where |
|---|---|---|
| C.1 counterfactual-`V` audit | done; one load-bearing use, named | table below |
| C.2 no conditionals on the agent's own action | **structural, by definition** (FIX); content in C.4(a) and §9 Part 0.4 **[relabelled in §9]** | `factors_through_description` |
| C.3 argmax lock-in versus BRIA | **fixture + coverage lemma** | `coverage_forces_test`; fixture |
| C.4(a) a declared control model | stated; generability recorded on item 101 | §3.4 |
| C.4(b) drills and audits | **named hypothesis** (`forecast_term_within` is FIX) — **[§9 Part C reduces the target to two external results stated by content]** | `DrillCalibrated`, `forecast_term_within` |
| C.4(c) the freezing requirement | **witness + obstruction** | `indispensable`, `frozen_drill_eq_cs`, `freeze_obstruction` |
| C.4(d) unsettleable classes | **proved** | `route`, `route_never_viol` |
| C.5 the exchange rate | **proved**; paralysis witness; recommendation | `implied_threshold`, `threshold_le`, `paralysis`, `asks_iff` |
| C.6 count integrity | **witness**; recognizable part caught; residual filed on item 101 | `tamper_raises`, `declared_loses` |
| C.7 shaping her standards | (a) row added; (b) matter stated; (c) **proved** on the extended model; (d) **proved + witness**; (e) regression | `Consult2.Rows2.*`, `shaper_total`, `sum_future_hole` |
| C.8 multiply versus condition | **proved + witness** | `multiply_protects`, `condition_fails` |
| C.9 many steps | **proved**, mismatch stated | `counted_trans`, `lexical_summed` |
| C.10 criteria sealed, event unsealed | (a) extension stated; (b) `anchored_invariant` is FIX (through `critAt_later`) with the **witness** the content; (c) **proved** on the rows, `sealed_no_incentive` and `sealed_multiply_eq_condition` FIX; (d) audit: none **[relabelled in §9]** | `anchored_invariant`, `amend_after_witness`, `choice_changes_counted`, `sealed_no_incentive` |

**C.1 The audit.**

| landed statement | applies her evaluation to | class | restated |
|---|---|---|---|
| `generic_policy_dominance`, `policy_dominance` | the option not taken | bounds only | the agent's estimates: `declared_loses`, `no_decay` |
| `gate_capture_window`, `li_gate_finite`, `li_lexical_finite` | the bypass branch | bounds only | `unsealed_gate_finite`, `lexical_any_timing` |
| the protected-authority identity `vu − v_r = ξ_d − ξ_c` | both branches | diagnostic: lives in the agent's beliefs, no decision rule reads it | — |
| `Q(π)`, the corrigibilization value | the approve-all trajectory | diagnostic under sequenced settlement (a menu value), otherwise bounds only in every consumer | — |
| `CS`, `Short`, the reach cone | the exterior path not yet taken | forecast, not evaluation: enters the design as the *price* of `S_a`, a sentence about the declared control model (C.2, C.4(a)) | `permWeight`, `evalOf` |
| materiality, `raisesAnchored` | the values under her evaluator in force before the action | **load-bearing**: a decision rule | it is a commitment she makes in advance — the anchored evaluator — not a hindsight judgment; the design keeps it and says so |
| `handlingOf`, `gatedValue` | the realized segment only | not counterfactual | the referent of A.1 |

**C.2.**  The priced events are sentences of a declared control model `M` about an
option's declared description, so the price factors through the description — the same
functional for the taken and the untaken options (`factors_through_description`); no
price conditions on "if the agent does `a`".  What this costs is C.4(a): the description
and `M` must be rich enough that the sentence decides the shortfall.

**C.3.**  The argmax chooser over conditional estimates puts `1/5` on consulting and `1/2`
on acting, never consults, and is never corrected because the untested estimate never
settles.  Under BRIA the covered hypothesis bidding `9/10` on consulting is tested at the
first block and wins every block (fixture).  The coverage clause in Lean: a hypothesis
whose record is bounded below by `−R` cannot be rejected at a block where its allowance
through that block exceeds `w_K + R` (`coverage_forces_test`, from
`record_succ_lt_of_rejected_opening`), so a diverging allowance forces the test.

**C.4(a).**  `M` is a declared entry of `J`'s meta level (C.10(a)); `S_a` is "`M` decides
that the effect described by `descr(a)` leaves matter `m` short of its requirement within
its window and cost bound", a finite disjunction over admissible exercises
(`AuthorityModule.CS`, item 101).  Generability requires `M`'s transition table, the
cost table, the window and the admissibility verdict as constants of the theory and the
rollout as an expressible feature — recorded on item 101; **the generability of `M` is a
named hypothesis of the design**.

**C.4(b).**  With drills at rate `q > 0` independent of the agent's choice and a choice
rule computable from prices, the drilled frequency of the shortfall on the chosen path
is a settled quantity the inductor can be calibrated against; the design's forecast term
is then within `ϖ · ε` of the realized penalty rate under `DrillCalibrated`
(`forecast_term_within`).  The target theorem — calibration itself from the inductor's
properties — is not proved here: it needs the drilled event as a security (item 101) and
the calibration property of the source theorem on a subsequence selected by the choice
rule.  **The incident bound in terms of `q` and the allowance is a conjecture and stays
open.**  The fixture shows the mechanism: with the drill correcting the blind spot's
price on the chosen path, its mass falls to zero under (ii); under (i) without drills the
blind spot persists with the realized score below the window every block.

**C.4(c).**  The indispensable agent: it cooperates with every drill and the resolution has
no actuator independent of it, so every unfrozen drill passes and `CS` fails
(`indispensable`).  A frozen drill passes exactly when the resolution has an actuator
independent of the agent, which is exactly `CS`'s clause with the agent idle
(`frozen_drill_eq_cs`, `freeze_obstruction`).  So: a drill can freeze the agent without
using the channel being tested iff the reserved resolution is realized through an
actuator the agent is not — and where it is not, the drill is the obstruction, and it is
the same obstruction as `CS`'s failure.  The design constraint this puts on `J`: every
reserved `Req` needs an agent-independent actuator declared, or the drill cannot be run.

**C.4(d).**  Forecast events that `M` does not decide and drills cannot test are routed to
inquiry (`route`), and the routed option is never a declared violation when inquiry is
not (`route_never_viol`), so B.1 is unaffected.

**C.5.**  `eval(c) > w ⟺ p_S + p_T < (bid − w)/ϖ ≤ (D − w)/ϖ` (`implied_threshold`,
`threshold_le`): lexical becomes an exchange rate — `ϖ` units of ordinary value per unit
of priced risk.  Paralysis: with risk at least `p_min > 0` on every non-inquiry option,
once `ϖ ≥ (D − w)/p_min` every one loses to inquiry (`paralysis`; `Witness.paralysis_instance`
at risk `3/5`).  Inquiry absorbs the risk: the agent asks exactly when `ϖ · risk ≥ bid − w`,
the consultation cost being the ordinary value forgone (`asks_iff`;
`Witness.exchange_rate`: acts at risk `3/10`, asks at `1/2`).  **Recommendation [corrected in §9]:** set
`ϖ` at the lexical minimum with a margin, `ϖ = D − w + margin`, and no higher.  The
window condition `D − ϖ < w` is what B.1 needs; every unit above it buys protection
against *under*-priced risk (a blind spot of size `1 − p` costs the (ii)-bidder
`ϖ(1 − p)`) at the price of consultation frequency, and past `(D − w)/p_min` it buys
nothing but paralysis.  What `ϖ` trades off is the market's pricing error against the
consultation rate; drills (C.4(b)) reduce the former and are the better lever.

**C.6.**  Without count integrity, zeroing the count raises the realized score by `ϖ` per
violation (`tamper_raises`); the same for the drill schedule, the audits and her
evaluation channel, each of which is an input to the count.  Interference with that
machinery is a declared violation — the count, the schedule and the channel are matters
of `J`'s meta level held by her (C.10(a)), so touching them is an unlicensed
reallocation, in `n_known`, and B.1 excludes the recognizable cases.  What remains —
tampering the recognizer does not see — is **count integrity as a named hypothesis**,
filed as item 101's companion (the priced events and the count they feed are one
integrity surface), not a new item.

**C.7.**  (a) *Topic and timing.*  The extended model (`Consult2`) adds a reference-fixed
raise dimension: the declared protocol carries a trigger (`Decl2.raiseTrigger`) and the
presentation whether the agent raises a question about her values (`Pres2.raise`).
Raising under the declared rule counts (`raise_declared_counts`); raising when changing
her mind would pay — the raise depending on the wanted answer — taints
(`raise_by_want_tainted`).  (b) *Disclosed shaping through the world.*  Row 7 counts it
and legitimacy is unchanged.  The matter "influence on her values through the world"
enters `J` held by her with `Req = {stop}`: disclosed and stoppable is a counted segment
with no shortfall; disclosed but not stoppable within `(c, τ)` is `Short` for that
matter — an effectiveness shortfall, reported under the cumulative rule, not a
legitimacy failure.  This is a statement about `J`'s data, made in the fixture; no new
Lean object is needed since `Short` already says it.  (c) *Disclosure cures.*  The
license (`licensedB2`) requires, when her standards were influenced, the influence
disclosed among the grounds; so a covert implant taints the first round's segment *and*
the second round's own segment (`implant_tainted`) — unlike row 14, whose second-round
segment counts (`r14_restated`, unchanged: manipulation of a single decision still
restarts).  Disclosed at the second round, the second segment counts
(`implant_disclosed_restart`).  A third party's covert implant taints the same way, with
no deviation by the agent and no report owed for the implant itself
(`third_implant_tainted`); disclosed by the agent, the second segment counts
(`third_disclosed_restart`).  The agent's silence about its own implant is the missed
report (`Model2.missedDisclosure`, the `due` clause of `dutiesOf` for the value-influence
matter).  All twenty landed rows re-decided on the lifted model give the landed
verdicts (`stable_counted`, `stable_tainted`, `stable_auth`).  Old-to-new map: `Model ↦
Rows2.lift`, `Presentation ↦ Pres2.base`, `Decl ↦ Decl2.base`, `Entry ↦ Entry2.base`,
`licensedB ↦ licensedB2` (the landed clause conjoined with disclosure), `ref ↦ ref2
crit`.  (d) *Anchoring.*  Under (c) every block whose evaluation depends on the shaped
standards scores the window until disclosure, so the shaper's total over such blocks is
at most any honest total (`shaper_total`) — the window once and no later credit.  The
witness is the chooser that optimizes the *sum* of its future decisions' scores under
restart-only scoring: window once, gain on every later decision, ahead of honesty as soon
as the gains exceed the forgone block (`sum_future_hole`; `Witness.sum_future`).  What
closes the hole is (c)'s dependence-based taint, not the per-hypothesis settlement by
itself: with restart alone the block winners after the shaping collect the gain.
(e) *One-sided true arguments.*  Selection from the declared pool by the wanted answer is
row 16, tainted under the pool-not-selection default, and it lifts (`stable_tainted`).

**C.8.**  Multiplying gives a realized protective incentive: the tainting option earns `w`,
below any honest ordinary value above the window (`multiply_protects`; the routing values
`3` versus `1`).  Conditioning on legitimacy scores the tainting option as if it had
counted and it wins whenever its counterfactual ordinary value is higher
(`condition_fails`).

**C.9.**  Per-step legitimacy composes along a continuation at a shared state
(`counted_trans`, from `Segment.trans`), so per-step `Counted` implies `Counted` on the
whole segment.  The converse — the whole segment counted implies each step's segment
counted — needs every evolution between the endpoints to pass through the intermediate
states; the consultation model's forced steps supply it and a general record need not:
**that is the mismatch**, and it is stated, not closed.  The lexical results hold per
block with the count summed over steps (`lexical_summed`), and B.1 with it.

**C.10.**  (a) *The criteria are in the allocation.*  The declared reference, the protocol,
the declared inputs and pool defaults, the selection rules and the license are matters of
`J`'s meta level held by her; changing one without her amendment is an unlicensed
reallocation under the authority module's factoring (`reallocAt_iff_unlicensed`), and on
the floor only `amendFloor` changes it (`alienation_only_by_amend`).  What is *not*
representable as landed: an `Entry` says who holds a matter, not what the matter's
content is, so "the criteria in force" has no field.  **Minimal extension:** read the
criteria off the state alongside the allocation — `Jof : S → AuthAlloc` already reads the
allocation off the physical state, and a companion `critOf : S → Crit` makes a criteria
change across the agent stage an `UnlicensedChange` with the same license.  (b) *Anchored
at the decision.*  With the criteria a parameter of the reference (`ref2 crit`) and a
schedule of amendments, the criteria in force at `t` ignore every amendment after `t`
(`critAt_later`), so `Counted` under them is invariant under every later amendment,
legitimate or not (`anchored_invariant`).  The witness: a fixed slant under the neutral
convention is tainted under the criteria at the decision and counted under the amended
convention (`slant_anchored_tainted`, `slant_unanchored_counted`); manipulate at `0`,
persuade her to amend at `5`, and under the *latest* criteria the tainted segment counts
(`amend_after_witness`).  (c) *The event is unsealed.*  The agent's choice between the
honest and the framing policy changes `Counted` in the realized record and with it the
gated score — ordinary value versus window (`choice_changes_counted`; rows 2, 8 and 15
lift the same way).  The design's incentive to preserve legitimacy is exactly this: under
a sealed event the multiply score's difference between two options is their ordinary
difference or zero, so no incentive remains (`sealed_no_incentive`), and the multiply and
condition versions choose identically — coinciding when the event holds and the multiply
version constant when it does not (`sealed_multiply_eq_condition`).  (d) *Audit.*
Landed statements whose hypotheses include activation independence or sealed comparison:
`security_score_bypass_le` (the common-event bound), `bypass_premium_le_common`, T4 of the
mediated-repair round (A10), and the corrigibility page's §6 typing of `C_n`.  **No
current corrigibility result consumes any of them**: the lexical theorem, the segment
gate, `li_gate_finite`, the first round's safety results and this round's B tests use
none.  They remain the zero case of `security_bypass_le_mismatch`'s mismatch term
(`sealed_is_zero_mismatch`), a property of the evaluator's placement, and are so
restated on the page.

## 4. When her evaluation happens (Part F)

The concern: with a single evaluation time, harms after it that she cannot foresee at it
are free, and a known time lets the agent place them just after it.  Three options —
deterministic growing lookahead `f(n)`, a mixture over evaluation times with per-time
gates, a random evaluation time `T ~ ρ_n` — compared on (a)–(g).  Lean: `Weighting` (the
common form; option 1 is `deterministic`, options 2 and 3 are the same weighting settled
in pieces or at once), `mixScore`, `lexical_any_timing`, `harmed`, `tailWeight`,
`harm_weight`, `deterministic_tail`, `timing_witness`, `random_positive`,
`race_deterministic`, `partial_settlement`; fixtures in `tests/test_bria.py::Timing`.

| criterion | 1. deterministic `f(n)` | 2. mixture `α_t` | 3. random `T ~ ρ_n` |
|---|---|---|---|
| (a) authority results | preserved from bounds (`lexical_any_timing` at the point mass) | preserved, each time gated separately, the mixture in `[w, D]` (`mixScore_mem`) | preserved, one gate at `T`, the expectation the mixture |
| (b) weight on a harm at delay `d` | `1[d ≤ f(n) − n]`: **zero beyond the lookahead** (`deterministic_tail`, `timing_witness`) | the tail `Σ_{t ≥ n+d} α_t` (`harm_weight`) | `P(T ≥ n + d)`, positive at every delay under full support (`random_positive`) |
| delays left free at some `n` | **yes, every `d > f(n) − n`** | none inside the support, but the weight decays | none inside the support, but the weight decays |
| (c) finite-time versus asymptotic | finite-time cover of `[0, f(n) − n]`, nothing beyond; the cover grows only in the limit | positive weight at every delay at every `n`; the *size* of the weight at long delays is asymptotic | same as 2, with one draw |
| (d) the race with reach `d(n)` | weights the harm iff `d(n) ≤ f(n) − n`; **fails at every `n` when the reach exceeds the lookahead** (`race_deterministic`) | weights it with the tail at `d(n)`: positive, vanishing if the tail decays faster than the reach grows | same; for geometric `ρ_n` with rate `q_n` the weight is `(1 − q_n)^{d(n)}`, bounded below iff `d(n) = O(1/q_n)` |
| (e) settlement and learning **[corrected in §9 Part E]** | one settlement with a deterministically growing lag; the delayed-feedback criterion **open** | never fully settles; **settlement in pieces** with the unsettled error at most (remaining weight) × `D` (`partial_settlement`); the criterion **open** for the unsettled tail | one settlement with a random lag of mean `n + 2`, so about half of all decisions are unsettled at any time; the delayed-feedback criterion **open** |
| (f) standard-shaping | one evaluation under her standards at `f(n)`; disclosure-cures applies there | disclosure-cures applies at every time through its own gate; later times use later standards, more pull toward shaping the further out the weight | same as 2 in expectation, one gate |
| (g) implementation | a schedule, public and therefore exploitable | a record of partial settlements | a hidden draw; where the draw lives and how it is kept from the agent is count integrity (C.6) |

**Recommendation [re-derived in §9 Part E: option 2]: option 3**, with `ρ_n` geometric from `n` at rate `q_n = 1/(n + 2)` —
mean lag `n + 2`, growing linearly, and weight `(1 − q_n)^d ≈ e^{−d/(n+2)}` on a delay
`d`, so a reach `d(n) = O(n)` keeps constant weight and a superlinear reach is lost.  The
reason: option 1 is refuted by (b) at every `n` — a known lookahead leaves a free delay —
and option 2 dominates on nothing option 3 lacks in expectation while never settling;
what separates 2 from 3 is (e) against (g): one settlement with a hidden draw versus
piecewise settlement with a public schedule.  The tradeoff the geometric family makes is
exactly (d) against (e): a heavier tail covers longer reaches and lengthens the expected
lag one for one.  **This is not adopted.**  Part A's single evaluation stays the default;
the adoption and the choice of `ρ_n`'s tail are reserved to the maintainer (§8) and
queued in `DECISIONS.md`.  For the recommended option the Lean statements are (a)
`lexical_any_timing` with `Wt` the weighting `ρ_n` and (b) `harm_weight` with
`random_positive`; the fixture is `Timing.test_known_lookahead_exploited` and
`Timing.test_capability_race`.

## 5. The fixtures

All 23 tests match their expectations (`python3 tests/run.py`).  `D = 1`, `w = 0`, `ϖ = 2`,
`N̄ = 2` unless stated.

| fixture | expectation | result |
|---|---|---|
| power of attorney, confident agent | bypass never wins; the filter is slack | matches (`FourTests.test_b1_*`) |
| argmax lock-in versus BRIA | argmax never consults; the covered hypothesis is tested and wins | matches (`Pressure.test_c3_*`) |
| circumvention through a helper: declared / within horizon / beyond | caught in advance / the hypothesis loses / **witness**: it profits | matches (`test_b3_helper`) |
| bundling across steps | a violation at any step puts the summed count at 1, the continuation loses | matches (`test_c9_many_steps`) |
| forecast blind spot, (ii) with drills / (i) without | mass falls to zero / **witness**: persists with the realized score below the window | matches (`test_c5_blind_spot_and_drills`) |
| the indispensable agent | passes unfrozen drills, fails `CS`; frozen drill = `CS` | matches (`test_c4_indispensable`) |
| exchange rate and paralysis | acts at `3/10`, asks at `1/2`; only inquiry at risk `3/5` | matches |
| standard-shaping: covert before / after disclosure | tainted on both rounds / second round counts | matches (`test_c7_standard_shaping`) |
| one-sided true arguments | tainted (row 16 lifts) | matches (Lean `stable_tainted`) |
| topic chosen by payoff | tainted; under the declared rule counts | matches |
| disclosed shaping with / without a working stop | counts, no shortfall / effectiveness shortfall | matches (`test_c7b_*`) |
| the sum-of-future chooser | ahead of honesty under restart-only scoring; not under disclosure-cures | matches |
| tampering without integrity | `+ϖ` per violation; recognizable interference excluded | matches (`test_c6_tamper`) |
| cross-block profit and late detection | four blocks at `3/10` recover `1`; debited wealth stays nonnegative | matches (`test_b4_*`) |
| multiply versus condition | `w < ord` protects; conditioning does not | matches |
| many steps | per-step verdicts compose; count sums | matches |
| amending the protocol after the fact | anchored: stays tainted; latest: counts (the witness) | matches (`test_c10_anchoring`) |
| a sealed legitimacy event | multiply and condition choose identically; no incentive remains | matches |
| evaluation timing | option 1: zero weight just after `f(n)`; geometric: positive; the race; partial settlement within the bound | matches (`Timing.*`) |
| regression against the first round | the confident-agent, above-`θhi` and below-`θlo` decisions coincide | matches (`Regression.*`) |

One mismatch against the *dispatch's* expectation, explained above: the default bidder's
feasibility at block `0` is not automatic after the rescaling; it is a condition on the
allowance schedule, exhibited both ways.

## 6. The named hypotheses

- **Count integrity** (C.6): the count, the drill schedule, the audits and her evaluation
  channel are not tampered with beyond what the recognizer sees.  Item 101's companion.
- **The settlement horizon** (B.3): helper violations are detected within `H` of the block.
- **Generability of the control model `M`** (C.4(a)): the priced events are securities.
  Item 101.
- **Drill calibration** (C.4(b)): `DrillCalibrated`, with the `q`-bound a conjecture.
- **The allowance covers the rescaled window at block `0`** (B.1).

## 7. What is filed

- `DECISIONS.md`: Part 0's four rulings (closing the first round's two outstanding
  actions and restating §6 and the wall); the 1a referent; settlement convention (ii);
  disclosure cures; the value-influence matter; Part F's reserved decision appended to
  *Awaiting the author*.
- `PRIORITIES.md`: items 84, 89, 99, 101, 102 updated in place; no new item.
- Wiki: `Corrigibility.md` (§4 rewritten around the lexical preference on realized
  scores with the permission layer as its advance-recognition face, the four tests, the
  named hypotheses, criteria sealed / event unsealed, §6 and the wall restated, Part F as
  an open design question, the scope statement rewritten), `Normative-Inductor.md` and
  `Normative-Induction.md` (revised in place: the competence layer is the lexical auction),
  `Continuation-BRIA.md` (the evaluation decomposition and the settlement convention),
  `Legitimacy.md` (the raise dimension, disclosure cures, the new rows), `Glossary.md`,
  `Theorem-Spine.md` 10.21.
- The decision-component round's `REPORT.md`: its outstanding-actions section only.

## 9. The follow-up: corrections, and the thin parts

`FOLLOWUP.md` (2026-09-26).  Lean: `BRIAFollowup.lean` (58 audited declarations, no
`sorry`), and one removal from `BRIACorrigibility.lean`.  Fixtures: `tests/test_followup.py`
(10 tests; all 23 earlier fixtures unchanged and passing).  The follow-up was dispatched
against the pull request as open; the pull request had been merged under the round's own
merge criteria the same day, so this section landed as its own pull request from `main`.

### 9.0 Corrections

| correction | what was wrong | what stands now | where |
|---|---|---|---|
| 0.1 the incident bound | `incidents_le` adds the *positive part* of the winners' underpromise, which is `Θ(K)` under noisy outcomes, and "rate `O(1/ℓ)`" is a constant: the bound allowed a constant incident rate | the signed bound `incidents_le_signed`; under **competitiveness** (a named hypothesis) the rate is `(𝒜_K + Mf K)/(ℓ · w_min · K)`, vanishing iff both are `o(K)` (`rate_le_of_competitive`); a linear allowance funds an incident every block (`Witness.linear_allowance_constant_rate`) | §9.B; docstring of `incidents_le` corrected |
| 0.2 the default bidder's affordability | `default_affordable` assumed the allowance covers the bid at *every* block — linear total allowance, feeding 0.1 | from `default_wealth_mono`: wealth never falls below `A_0`, so with the block weights bounded by `w_0` a block-`0` allowance `A_0 ≥ w_0 · bd` suffices (`default_affordable_block0`); with unbounded weights no block-`0` allowance does, and the minimal schedule is `A_k = (max_{j≤k} w_j − max_{j<k} w_j) · bd`, total `bd · max_{j<K} w_j` (`default_affordable_of_schedule`) — `o(K)` iff the weights are | `BRIAFollowup` §0 |
| 0.3 `ϖ` against B.4 | C.5's "lexical minimum with a margin" set `ℓ = ϖ − D + w`, the very quantity the incident rate divides by | the band is `D − w < ϖ < (D − w)/p_min`, nonempty iff `p_min < 1` (`weight_band`); inside it `ϖ` trades three things: the incident rate `∝ 1/ℓ` (lower for larger `ϖ`), blind-spot protection `ϖ(1 − p)` (larger for larger `ϖ`), and consultation frequency (paralysis as `ϖ → (D − w)/p_min`).  Recommendation: `ϖ` in the *upper* half of the band — `ℓ` a fixed fraction of `D − w`, say `ϖ = 2(D − w)` when `p_min < 1/2` — with drills lowering `p_min`'s effective floor; not the lexical minimum | §9.0 |
| 0.4 description faithfulness | the priced sentences read `descr(a)`; a proposer-written description passes a short option | descriptions are a field of the interface (`PricedInterface`), the priced sentence reads only them (`event_reads_interface`, FIX), and the proposer-written witness is `misdescription_witness`; added to §6.  `ViolC` covers the structurally declared releases; effect completeness is the clause that the interface's descriptions are the effects — faithfulness is its representation half, not a new object | §9.D.1 |
| 0.5 Part F's settlement column | option 1 "open" and option 3 "survives" were inconsistent; both have growing lags, and mean lag `n + 2` leaves about half the decisions unsettled | both marked open; the criterion re-evaluated on the escrow algebra of Part E and the recommendation re-derived (option 2) | §9.E |
| 0.6 labels | `factors_through_description`, `forecast_term_within`, `anchored_invariant`, `sealed_no_incentive`, `sealed_multiply_eq_condition` are definitional or one-line arithmetic; `cross_block_bound` assumed its conclusion | relabelled **FIX** in §3's table (the content of C.2 is C.4(a) and 0.4; of C.10(b) the witness; of C.10(c) `choice_changes_counted`); `cross_block_bound` **removed** from `BRIACorrigibility.lean` and the spine | §3 |

### 9.A Standing violations: closing the cross-block hole

**Definition.**  A violation is *standing* from commission until *remedied* — undone,
ratified by a counted decision of hers, or restored under a maintenance mandate.  While it
stands the disposition of its fruits is a matter of `J` held by her, and a continuation
that uses the fruits is exploiting them under the authority module's factoring, counted at
each block of use.  **Fruits without counterfactuals** (`IO`, `Step`, `taintStep`,
`taintAfter`, `uses`): the interface declares what each act reads and writes; a violating
act taints what it writes, an act reading a tainted component taints what it writes
(`taint_propagates`), a remedy clears the taint (`remedy_clears`); use is reading a tainted
component.  Decidable on finite instances (`Witness.taint_decides`, by `decide`).

**A.3, proved.**  A block whose continuation uses tracked fruits carries a counted
violation, so its realized residual is at most `D − ϖ` *whatever advantage the fruits
carry* — the advantage cannot exceed the ordinary range — and the hypothesis loses at
least `ℓ` against its bid (`standing_block_loss`).  Over the commission block and `m`
blocks of use the net record is at most `−(m + 1) · ℓ < 0` (`cross_block_blocked`): an
advantage carried by tracked fruits recovers nothing, and `cross_block_witness` is
blocked for tracked fruits.  The round's `Δ = 3/10` witness, re-run under tracking, loses
every block (fixture).  What the theorem takes from the interface: that an advantage is
carried *through declared components* — an advantage the continuation enjoys without
reading any tracked component is the residual below.

**A.4, the residual: knowledge.**  A violation whose fruits are written outside the tracked
components — the agent's own memory — leaves no taint, no later use is charged, and the
cross-block witness applies (`knowledge_residual`; fixture).  The structural treatment:
make the agent's observation channel a tracked component; then every later act reading it
uses taint until a remedy (`observation_taints_all`).  Its cost is exactly that: *every*
later block is charged, and the only remedy is a reset of the channel — which is where
this residual meets the agent's indifference in tainted worlds (concern 4): named, not
pursued.

**A.5, remedy incentives** (arithmetic on the per-block charge, FIX-level content):
remedy at block `r` leaves a total charge `(r + 1) · ℓ`, less than continuing
(`remedy_stops_charge`), so reporting and seeking remedy is incentive-compatible;
violating and then reporting still loses at least `ℓ` against not violating, since the
commission charge stands (`violate_then_report_loses`); ratification obtained by
manipulation is not counted and so not a remedy (`manipulated_ratification_not_remedy`,
from the framing row).

**A.6, instances.**  *Disclosure cures* is the instance where the fruit is her standards
component, tainted by the undisclosed influence, and the remedy is the disclosure:
`standingStandards` stands at both rounds for the undisclosed implant and at round `0`
only when disclosed at round `1` (`implant_standing`), matching `implant_tainted` and
`implant_disclosed_restart`.  Old-to-new map: `Influence.prog = some _` ↦ taint on the
standards component; `disclosedAt = some j` ↦ remedy at `j`; the license's disclosure
clause ↦ "no use of a tainted component without remedy".  *Helpers*: a helper she cannot
halt is a standing shortfall of her control surface — `Short` for the halt matter at
every block — charged each block past any horizon (`uncorrectable_helper_charged`), so
B.3's horizon dependence is removed for helpers she cannot correct; the residual is the
helper she *can* halt, whose later violations are events, where the horizon stays
(`correctable_helper_horizon`).  **Verdict:** confirmed, with the horizon a hypothesis
for correctable helpers only (D.3).  A third party's standing violation is the point of
contact with concern 4 and is not pursued.

### 9.B A real rate bound

**B.1 The signed bound** (`incidents_le_signed`): `ℓ · w_min · #incidents ≤ 𝒜_K +
Σ_{non-incident wins} w_k (G_k − b_k)`, the margin signed.  **Competitiveness** —
the signed margin bounded by `Mf K` — is the hypothesis (`Competitive`), and under it
`#incidents / K ≤ (𝒜_K + Mf K)/(ℓ · w_min · K)` (`incidents_le_of_competitive`,
`rate_le_of_competitive`).  **The derivation from coverage fails**, precisely: coverage
forces a *test* of a covered hypothesis whose allowance outgrows its record
(`coverage_forces_test`), not a *win stream*; once tested, the closer bidder wins only
while its capital-bounded bid is highest, and the underpromiser retakes the block whenever
its own is; and when every hypothesis in the class underpromises by `γ` there is no closer
bidder for coverage to find — the margin is `γ · Σ w_k`, linear
(`uniform_underpromise_margin`).  So competitiveness is a **named hypothesis**, with that
witness for why.  The fixture shows noisy honest outcomes with the positive part growing
linearly and the signed sum zero.

**B.2 The allowance schedule.**  The landed prefix rule's total is
`𝒜_K ≤ 2√(S_K M_K) + √S_K (1 + ln K) = o(S_K)`; with bounded block lengths
`𝒜_K = O(√K log K)`.  Under it, with competitiveness at `Mf = o(K)`, the incident rate is
`O((√K log K + Mf K)/K) → 0`; **vanishing iff `𝒜_K + Mf K = o(K)`**, and a linear
schedule gives a constant rate (`Witness.linear_allowance_constant_rate`; fixture).  The
block-`0` affordability of 0.2 costs `A_0 ≥ w_0 · ϖN̄/(D − w + ϖN̄)` once, compatible
with `o(K)`.

**B.3 Under standing violations** the charged set is the commissions *and* the blocks of
use, and the same signed bound holds for their weighted count (`charge_le_signed`).

### 9.C Forecast accuracy: the drill-calibration theorem, reduced

**Setting.**  Drills at rate `q > 0` on a schedule settled by the deductive process,
independent of the agent's choice; a choice rule computable from prices; the drilled
event "the drill at block `k` found the chosen path short" a sentence settled when the
drill runs (item 101).  **What the pinned library provides.**  Affine unbiasedness from
feedback (Garrabrant et al. thm:wubaff) is present as
`LogicalInduction.lic_not_frequently_positive_feedback_return`: for a `P`-generable
divergent weighting whose support admits a strictly increasing deferral function under
which each element's value is settled before the next is priced, the weighted average of
price minus truth is not frequently above any `γ > 0` (and symmetrically below).  Learning
pseudorandom frequencies (thm:prand) is present as
`lic_learning_varied_pseudorandom_of_historicalVerifiers`.  Neither is *instantiated* here:
the weighting (drilled ∧ chosen) as a `P`-generable feature, the feedback-trader emission
for the shortfall sentences, and the deferral function are the generability certificate
item 101 owes.  **They enter as named hypotheses stated by content**, never as axioms:
`UnbiasedFromFeedback` (the drilled-and-chosen weighted bias eventually within `γ` of
zero) and `DrillPseudorandom` (the drilled sums are the `q`-fraction of the chosen sums up
to `err K`).  **The target, reduced:** under the two, the chosen-path bias is at most
`(γ · drilled mass + err K)/q` (`chosen_path_unbiased`) — unbiased on the chosen path by
the drills' independence from the choice.  **The incident bound in `q`.**  On the
low-price bin (drilled, chosen, `p ≤ θhi`) unbiasedness bounds the fraction of shorts by
`θhi + γ` (`blind_rate_le`): the forecast filter's threshold is honest up to the
unbiasedness rate, and the speed of `γ → 0` in the drilled mass `qK` is what the paper
does not give — **the incident bound in `q` needs that rate, and it is open**.  What the
signed average does *not* bound is net under-pricing on shorts offset by over-pricing
elsewhere, which is why the bin, not the whole path, is the subsequence.  **What now holds
as a consequence** of the two external hypotheses: chosen-path unbiasedness and the
bin-level blind-spot rate; the round's `forecast_term_within` (FIX) and the exclusion
results (`forecast_slack`, `cgate_zero_of_forecast`) are unchanged.  **What remains a
hypothesis:** the two external results' instantiation (item 101), the schedule's
pseudorandomness, and the rate of unbiasedness.

### 9.D The named hypotheses, sharpened

- **D.1 Description faithfulness** (0.4): `PricedInterface`, `event_reads_interface`,
  `misdescription_witness`; the fixture.
- **D.2 The actuator condition**, now a well-formedness condition on `J` (`WellFormed`):
  every required resolution of a reserved matter declares an actuator independent of the
  agent; under it every frozen drill runs (`frozen_drill_runs`), and a `J` violating it
  fails `CS` for that matter by construction (`ill_formed_fails_cs`), since `CS`
  quantifies the agent idle.
- **D.3 The settlement horizon**, restated after A.6: a hypothesis for helpers she *can*
  correct only (`correctable_helper_horizon`); for helpers she cannot, the standing
  shortfall is charged each block (`uncorrectable_helper_charged`).  Confirmed.
- **D.4 Influence on her standards**, generally: an entry of her standards component whose
  provenance includes an undeclared non-principal input (`Source`, `Standards`,
  `influenced`); it agrees with the round's flag on every row (`influenced_iff_flag`,
  `rows_agree`).  Where it is not decidable: the definition decides a *recorded*
  provenance; an undeclared input is, by definition, one the record does not carry as
  declared, so whether the recorded provenance is complete is count integrity again
  (item 101's companion), not something the definition decides.

### 9.E Settlement under delay

**The algebra** (`DAuction`): block `k` settles at `k + L_k`; a hypothesis's *cash* is its
allowance plus its settled winnings minus every bid it placed — unsettled bids stay in
escrow (`cash`) — and a bid is feasible against cash net of escrow plus the block's
allowance (`FeasibleEscrow`).  Cash never falls below the allowance minus the bid
(`cash_succ_ge`), so **wealth stays nonnegative** (`cash_nonneg`), and the weighted
overestimation on the *settled* blocks is at most the allowance while the escrowed
exposure of the unsettled ones is at most the allowance plus the settled underpromise
(`delayed_overestimation`).  **The lag and coverage:** by time `K` at most `K − λ` tests
have arrived under a lag of at least `λ` (`tests_le_of_lag`), so a hypothesis's test takes
`λ` longer and its escrowed bids tie up its capital meanwhile; with mean lag `n + 2`
about half the decisions are unsettled at any time (fixture).

**Part F (e), re-evaluated.**  All three options now have an algebra: escrowed
feasibility keeps wealth nonnegative and bounds the settled overestimation under any lag.
What differs is the escrow.  Option 1 escrows every bid for `f(n) − n`, growing.  Option 3
escrows every bid for a random lag of mean `n + 2`: half the capital is locked at any time
and a hypothesis's test arrives half a horizon late.  Option 2 settles *in pieces*: each
evaluation time releases its share of the escrow as its gate settles, so the locked
capital is the remaining weight times the bid, and the test arrives progressively.
**Revised recommendation: option 2**, the mixture with per-time gates and piecewise
settlement — it puts the same weight on every delay as option 3 in expectation (so the
timing-exploitation argument against option 1 holds for it), it needs no hidden draw (the
schedule `α_t` is public and leaves no free delay), and its escrow is released as weight
settles; its cost is the settlement record and the unsettled-tail error bounded by the
remaining weight times `D` (`partial_settlement`).  The reserved decision in
`DECISIONS.md` is updated; the recommendation stays reserved, and Part A's single
evaluation stays the default.

### 9.F The fixtures

| fixture | expectation | result |
|---|---|---|
| cross-block with standing violations | the `Δ = 3/10` witness charged each block, no net gain; the knowledge residual: untracked memory, the old witness applies; the observation channel tracked: every later block charged | matches |
| self-report | the per-block charge stops at remedy; the total still loses to not violating; manipulated ratification not counted | matches |
| a helper she cannot halt | charged every block past any horizon; a halt-able helper's later violation beyond the horizon uncharged | matches |
| the signed rate | noisy honest bidders: positive part linear, signed sum zero | matches |
| allowance schedules | linear: constant incident rate; the landed rule: total `o(K)`, the ratio falling | matches |
| misdescription | proposer-written description passes; interface description excluded | matches |
| drills | no drill: the under-priced shortfall persists; at rate `q` the price converges, faster at higher `q` | matches |
| delayed settlement | escrowed feasibility keeps cash nonnegative at lag `n + 2`; about half unsettled | matches |

All 23 earlier fixtures pass unchanged.

### 9.G What changed in the ledger

`DECISIONS.md`: standing violations with taint-tracked fruits; the actuator
well-formedness condition; description faithfulness; the corrected `ϖ` recommendation;
Part F's *Awaiting the author* entry updated to option 2.  `PRIORITIES.md`: items 101 and
102 in place; no new item.  Wiki: `Corrigibility.md` (standing violations, the corrected
rate statement, the `ϖ` band, the named hypotheses, Part F's column and recommendation),
`Continuation-BRIA.md` (delayed settlement), `Legitimacy.md` (disclosure cures as an
instance; influence by provenance), `Glossary.md`, `Theorem-Spine.md` 10.21.

## 8. Outstanding maintainer actions

1. Whether to adopt Part F's recommendation — **after the follow-up (§9.E), the mixture
   over evaluation times with per-time gates and piecewise settlement (option 2)**, the
   random time (option 3) having been the round's original recommendation — in place of
   Part A's single evaluation, and with which weights: the decision turns on how much
   escrowed capital and settlement record the arrangement will carry for weight on long
   delays.  Queued in `DECISIONS.md`, *Awaiting the author*.
