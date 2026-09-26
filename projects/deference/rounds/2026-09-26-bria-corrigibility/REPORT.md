# Corrigibility as the agent's preference: lexical Continuation BRIA on realized scores

Round `2026-09-26-bria-corrigibility`, the second round of the decision-component pull
request, **amended four times the same day: by the follow-up (§9 below; `FOLLOWUP.md`),
the second follow-up (§10; `FOLLOWUP2.md`), the third (§10.4′; `FOLLOWUP3.md`) and the
fourth (§10.4″; `FOLLOWUP4.md`)**.
Lean: `lean/Workspace/Deference/Contrib/BRIACorrigibility.lean` (147 audited declarations
after the follow-up removed one), `BRIAFollowup.lean` (58) and `BRIAFollowup2.lean` (128
after the fourth follow-up), every `#print axioms` within
`[propext, Classical.choice, Quot.sound]`, no `sorry`.  Fixtures: `src/bria.py`,
`tests/test_bria.py`, `tests/test_followup.py`, `tests/test_followup2.py`,
`tests/test_followup3.py` and `tests/test_followup4.py` (52 tests, `python3 tests/run.py`).
Statements below that the follow-up corrects are marked **[corrected in §9]**; labels the
follow-up changes are marked **[relabelled in §9]**; statements the second follow-up
corrects are marked **[corrected in §10]**; the third follow-up's are marked
**[corrected in §10.4′]**; the fourth follow-up's are marked **[corrected in §10.4″]**.
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

**Recommendation [re-derived in §9 Part E: option 2; the criterion revised in §10.3 with a fourth option, and reserved]: option 3**, with `ρ_n` geometric from `n` at rate `q_n = 1/(n + 2)` —
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
- **The noise hypothesis over all blocks** (§10.4′, §10.4″): the weighted signed noise of
  the realized lexical score, summed over *every winning block* — a selection fixed at
  opening — is `o(K)` (`NoiseBounded` at the constant indicator); Azuma–Hoeffding's
  content, the per-`K` tail derived from the pinned Mathlib (`azuma_selected_tail`), the
  conditional sub-Gaussianity of each bounded increment (Hoeffding's lemma) and the
  uniform-in-`K` sure bound named.  Not valid on "not an incident" or any conjunction
  with it (§10.4″).
- **The conditional-expectation bound** (§10.4″): the expected realized score given the
  history at opening is at most `D − ϖ π_k`, `π_k` the expected count of violations of
  every class — the ordinary value at most `D`, the counts entering with weight `ϖ`.
- *Not among the hypotheses of the violation claim:* competitiveness and the honest
  tracker (§10.4, §10.4′) are true lemmas on the Continuation-BRIA page; the violation
  claim (§10.4″) does not rest on them.

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
(`taint_propagates`), a remedy clears the taint (`remedy_clears`) **[corrected in §10.1: a
remedy clears its own violation's taint only; this rule is the one-identifier case]**; use
is reading a tainted component.  Decidable on finite instances (`Witness.taint_decides`, by `decide`).

**A.3, proved** **[restated under convention (ii) in §10.2, where it becomes the
statement for the window before detection; after detection the fruits are never used]**.
A block whose continuation uses tracked fruits carries a counted
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
witness for why **[corrected in §10.4: one honest tracker in the class, fed at the rate of
its honesty error, gives competitiveness with `Mf K = Σ w_k ε_k`; the tracker's allowance
is the hypothesis, and the witness is the class with no tracker or an unfed one]**.  The fixture shows noisy honest outcomes with the positive part growing
linearly and the signed sum zero.

**B.2 The allowance schedule.**  The landed prefix rule's total is
`𝒜_K ≤ 2√(S_K M_K) + √S_K (1 + ln K) = o(S_K)`; with bounded block lengths
`𝒜_K = O(√K log K)`.  Under it, with competitiveness at `Mf = o(K)`, the incident rate is
`O((√K log K + Mf K)/K) → 0`; **vanishing iff `𝒜_K + Mf K = o(K)`** **[corrected in
§10.4″: the incident rate does not vanish — a knowingly carried after-the-fact risk is
priced and accepted at C.5's exchange rate `(D − w)/ϖ`; the margin's selection is decided
with the block's outcome, and its `o(K)` hypothesis fails whenever the risk persists]**, and a linear
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
**Revised recommendation: option 2** **[corrected in §10.3: in expectation the escrow
of options 2 and 3 is the same, `expected_escrow_eq`; the recommendation is reserved on
her evaluation load against the variance, with a fourth option]**, the mixture with per-time gates and piecewise
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

## 10. The second follow-up: per-violation taint, the window before detection, Part F's criterion, competitiveness from one honest tracker

`FOLLOWUP2.md` (2026-09-26).  Lean: `BRIAFollowup2.lean` (81 audited declarations, every
`#print axioms` within `[propext, Classical.choice, Quot.sound]`, no `sorry`), a sibling
of `BRIAFollowup.lean` whose §A taint rule it supersedes — the superseded declarations
stay, their docstrings marked, with the old-to-new map a theorem (§10.1).  Fixtures:
`tests/test_followup2.py` (12 tests; all 33 earlier fixtures unchanged and passing, 45 in
all).  Landed as its own pull request from `main` after the first follow-up's.  Statuses
below: **proved**, **witness**, **obstruction**, **named hypothesis**; the §9 statements
this section corrects are marked **[corrected in §10]** in place and not rewritten.

### 10.1 Remedies clear only their own violation's taint (Part 1) — **proved**, with the witness

**The bug.**  `taintStep` sends `.remedy` to `∅`: with two standing violations, remedying
one clears the taint of both and the unremedied one's fruits are free to use
(`Witness.two_violations_one_remedy_old`, by `decide`: two violations writing `0` and `1`,
one remedy, the act reading `1` has `uses = false`).

**The rule, per violation.**  A taint is a set of (violation, component) pairs
(`Taint V Comp = Finset (V × Comp)`); a step is an act carrying the identifier of the
violation it commits, if any, or the remedy of one identified violation (`Step2`).  A
violating act taints its writes with its own identifier (`commission_taints`); an act
reading components tainted by some violations taints its writes with all of them —
taint joins at reads (`readTaint`, `taint_propagates2`, `taint_joins`); `.remedy v`
clears `v`'s taint only (`remedy_clears2`), leaves every other violation's exactly as it
was (`remedy_keeps_others`), and on a component erases `v` from the standing violations
and nothing else (`taintedBy_remedy`), so a component tainted by two stays tainted after
one remedy (`still_tainted_after_one_remedy`).  Use is reading a component some
unremedied violation taints (`uses2`), a `Bool` computed from the interface and the
recorded taint.

**Re-proved**, old to new:

| old (`BRIAFollowup`) | new (`BRIAFollowup2`) | what changed |
|---|---|---|
| `taint_propagates` | `taint_propagates2`, `taint_joins` | the propagated taint is the violation read, not "taint"; every violation read propagates |
| `remedy_clears` (to `∅`) | `remedy_clears2`, `remedy_keeps_others`, `taintedBy_remedy`, `still_tainted_after_one_remedy` | per violation |
| `Witness.taint_decides` | `Witness.taint_decides2` | the same instance with one identifier: the same taint set, use verdicts and remedy |
| `observation_taints_all` | `observation_taints_all2` | until *that* violation's remedy |
| `knowledge_residual` | `knowledge_residual2` | unchanged in content; the point of contact with §9.A.4, not pursued |
| `implant_standing` (§9.A.6) | `Witness.implant_standing2`, `Witness.two_influences_one_disclosure` | the influence is a violation tainting her standards component, its disclosure its remedy; the rows' verdicts equal `standingStandards`'s; and with two influences the agent's disclosure of its own does not cure the third party's — under the old rule it did |

**The old-to-new map is a theorem.**  With every violation given the same identifier
(`V = Unit`), the new act step projects onto the old one
(`old_is_new_with_one_identifier`) and use is the same predicate (`uses_old_eq_new`):
the old rule *is* the new rule with one identifier, so every §9.A result holds under the
new rule at one identifier, and what the old rule lost is exactly the identity of the
violation a remedy addresses.  §9.A's "a remedy clears the taint (`remedy_clears`)" is
**[corrected in §10]**; the disclosure-cures map of §9.A.6 gains the clause "each
influence its own violation; disclosure remedies that influence only".

**The witness, both ways** (`Witness.io4`): under the old rule the use of the unremedied
violation's fruits is uncharged; under the new rule it is charged — `uses2 = true`, and
the block loses `ℓ` under (ii) (`two_violations_charged`, with the round's `D = 1`,
`w = 0`, `ϖ = 2`: exactly `1`); only the second remedy clears it.  Fixture:
`PerViolation.test_two_violations_one_remedy`, `test_taint_joins_at_reads`,
`test_disclosure_cures_per_influence`.

### 10.2 `cross_block_blocked` under the adopted convention, and the window before detection (Part 2)

**2.1 Restated under (ii) — proved.**  `standing_block_loss` and `cross_block_blocked`
took `residI` with the hypothesis `bid ≥ w` **[corrected in §10]**.  Under the adopted
convention the hypothesis is that the winning continuation's *evaluation* is at least
`w`, and the loss against the bid is `bid − residII`, which is the evaluation plus the
recognized count less the realized residual *without* the prices: the price term in the
evaluation cancels the price term added back at settlement (`price_cancels`).  So with
`gord ≤ D` and any one counted violation — recognized in advance, forecast-class, or
counted after the fact — the loss is at least `ℓ = ϖ − D + w` with nonzero prices
(`standing_block_loss_ii`), and over the commission block and `m` blocks of use the net
record is at most `−(m + 1) · ℓ < 0` (`cross_block_blocked_ii`).  The `residI` form is
the zero-price special case: `residII gord 0 n 0 0 = residI gord n` and
`evalOf bid 0 0 0 = bid` (`residII_zero_price`, `evalOf_zero_price`), and the old lemma
follows from the new (`standing_block_loss_of_ii`).  Fixture:
`ConventionII.test_per_block_loss_with_prices` — a use block won at evaluation `1/2` with
price `1/4`, loss `3/2 ≥ 1`.

**2.2 After detection, use is recognized in advance — proved.  The headline for standing
violations: after detection the fruits are never used.**  Once a violation is detected
and its taint recorded, "this continuation reads a component tainted by an unremedied
violation" is `uses2 I T a`, a `Bool` computed at choice time from the interface and the
record (`Witness.taint_decides2`, `Witness.window_before_detection`, by `decide`).  It
compiles into the menu's structural count: `nKnownWith I T base a = base a + [uses2 I T a]`
(`use_is_known`), the `ViolC`-style predicate.  Then B.1 excludes every use block
outright: with the bid clamped at `D`, prices nonnegative, and inquiry carrying the
default bidder at the window, an option that uses recorded taint evaluates below inquiry
by ranges alone (`declared_loses`) and is never the maximizer (`filter_slack`):
`after_detection_never_used`.  So the per-block loss of 2.1 is not the statement for
detected violations — those are never used, not merely unprofitable — but the statement
for the **window before detection**.  §9.A.3's "each block of use is charged" is
**[corrected in §10]**: it is the window's statement.

**2.3 The window before detection — proved (the collection), with the carry-over
condition.**  A violation committed at block `k₀` and detected at `k₁ > k₀`.  The record
carries the commission step unflagged until detection; detecting `v` at `k₀` flags that
step (`detectAt`), and the taint is recomputed over the recorded steps from `k₀`.  Taint
comes only from commission: with no recorded step committing `v`, no component carries
`v`'s taint (`taint_only_from_commission`), so before detection nothing was on record and
the window's blocks were chosen unrecognized; after detection the taint stands until
`v`'s own remedy (`taint_persists_without_remedy`).  **The charge.**  A block settled
without the use counted and then debited `ϖ` is the block settled with the use counted
(`late_debit_eq_late_settlement`, arithmetic), so each window block — won at an
evaluation at or above the window, settled at `residII` with the use uncounted — loses at
least `ℓ` against its bid once debited `ϖ` (`window_block_charged`).  The commission
block is in the window too: it was settled before detection, and its charge is the same
debit.  **The collection.**  The debit is a schedule on the allowance of the hypothesis
that won the block, in the sense of `debited` (`windowDebit`, `windowDebit_bounds`), so
`debited_overestimation` applies with the bound the allowance net of the debits
collected.  The greedy schedule takes what the allowance offers up to what is outstanding
(`greedyDebit`); what it collects by `K` is the charge or the cumulative allowance,
whichever is smaller (`greedy_collects`), so **the charge is collected by `K` iff the
hypothesis's cumulative allowance through `K` covers it** (`collected_iff`) — B.4's
carry-over condition — and what is not collected is the excess of the charge over the
allowance (`uncollected_eq`), carried against every later allowance.  **The exposure.**
Over `m` window blocks, before the debit the net gain is at most `m · R`, `R = D − w`
the per-block advantage bound (the realized residual at most `D`, the bid at least `w`;
`1` in rescaled units); after the debit it is at most `−m · ℓ` plus the uncollected part
of the charges (`window_exposure`): only uncollected debits escape, and a hypothesis
that never receives allowance again keeps what it took — bounded by the window's length
times `R`.  **Fixture** (commission at `0`, use at `1` and `2`, detection at `3`, no use
after): `Witness.window_before_detection` — before detection the taint is empty and the
uses at `1` and `2` unrecognized; after `detectAt` the taint stands on the asset from
block `0`, both uses read it, and a further use has `nKnownWith = 1`, excluded;
`Witness.window_debit_collected` — charge `2` per block against allowance `1`, collected
in two blocks with `1` outstanding in between.  In the auction
(`Window.test_window_before_detection`): the misaligned hypothesis commits at `0`, uses at
`1` and `2` with `n_known = 0` at choice, every block from `3` on is inquiry, the three
blocks are debited `ϖ` (rescaled `2/5`) each, collected in full, and net of the debit
each loses more than the rescaled `ℓ`; `Window.test_carry_over` — allowance `1/2` per
block after detection, the outstanding part is exactly the uncollected debit and is
still positive at the horizon.

**2.4 Taint from undetected violations — stated, not a theorem about the design's
success.**  A violation never detected is a record in which no step commits it, and the
design does *nothing* with its fruits: no taint, no charge (`never_detected_never_charged`,
the same lemma as "before detection", read at a window of infinite length).  That is the
count-integrity boundary — the count, the drill schedule and the audits are what turn a
commission into a flagged step (item 101's companion).  **It differs from the knowledge
residual**: §9.A.4 is a *flagged* commission whose fruits are written outside the tracked
components — the step is on record, the fruit is untrackable — while this is an
*unflagged* commission whose fruits may be perfectly tracked.  Undetected commission and
untrackable fruit are two residuals; the second is out of scope here.  Fixture:
`Window.test_undetected_is_never_charged`.

### 10.3 Part F: the real criterion (Part 3)

**3.1 Expected escrow is the same — proved.**  Under a random time `T ~ α` the expected
locked capital at `t` is `E[bid · 1[T > t]]` (`randomLocked`); under the mixture settled
in pieces it is the bid less the shares released at times up to `t` (`mixtureLocked`).
With `α = ρ_n` they are equal at every `t` (`expected_escrow_eq`), both the tail weight
beyond `t` times the bid (`locked_eq_tail`).  §9.E's "its escrow is released as weight
settles", offered as what separates option 2 from option 3, is **[corrected in §10]**:
in expectation it separates nothing.  What does differ: the *variance* of the locked
capital — the random time's `bid · 1[T > t]` is Bernoulli, variance `bid² p (1 − p)`
(`bernoulli_variance`), the mixture's is deterministic, zero; the variance of settlement
timing — one draw against a schedule; and the timing of partial signal — the mixture's
arrives progressively as each time settles, the random time's all at once at `T`.

**3.2 Criterion (h): her evaluation load.**  Option 1 needs one evaluation per decision at
a public time.  Option 2 needs one at each evaluation time in the support — unbounded
under full support, or truncated at `s` at a cost bounded by the tail weight from `s`
times `D` (`truncation_cost`, `partial_settlement` at `S = range s`).  Option 3 needs one
per decision at a hidden time.  The load is a cost to *her* — her attention is the
arrangement's scarcest input — not to the agent.

**3.3 Option 4, the hybrid.**  Draw `k` evaluation times per decision, independently and
hidden, from `ρ_n`, and score by their average; `k = 1` is option 3, and as `k → ∞` the
average approaches the mixture.  With an expectation operator linear and normalized
(`Expect`) and the `k` draws entering as uncorrelatedness: the average has the same
expectation as one draw, so the same weight `P(T ≥ n + d)` on a delayed harm for every
`k` (`average_mean`); its mean-square deviation is `σ²/k` (`average_variance`), falling
like `1/k` (`variance_falls`); its load is `k` evaluations per decision; its escrow is
released in `k` pieces of `bid/k`, each at a hidden time, with the same expected locked
capital as options 2 and 3 and variance `bid² p (1 − p)/k`; its secrecy is `k` hidden
draws, each a count-integrity question.  Fixture: `PartF.test_hybrid_variance_falls_with_k`
(exact, by enumerating the product distribution: the same mean for `k = 1, 2, 3`, the
variance `v₁/k`), `test_expected_escrow_equal`, `test_load_table`.

**3.4 The revised comparison.**

| criterion | 1. deterministic `f(n)` | 2. mixture `α_t` | 3. random `T ~ ρ_n` | 4. hybrid, `k` draws |
|---|---|---|---|---|
| (a) authority results | preserved (`lexical_any_timing`) | preserved, each time gated | preserved, one gate | preserved, `k` gates |
| (b) weight on a harm at delay `d` | zero beyond the lookahead | the tail `Σ_{t ≥ n+d} α_t` | `P(T ≥ n + d)` | `P(T ≥ n + d)`, the same for every `k` (`average_mean`) |
| (c) finite-time versus asymptotic | finite cover, nothing beyond | positive at every delay | positive at every delay | positive at every delay |
| (d) the race with reach `d(n)` | fails past the lookahead | the tail at `d(n)` | the tail at `d(n)` | the tail at `d(n)` |
| (e) settlement and escrow | one settlement, lag `f(n) − n` | in pieces; expected escrow `bid · P(T > t)`, **variance zero** | one settlement; expected escrow the same, variance `bid² p(1 − p)` | `k` pieces; expected escrow the same, variance `/k` |
| (f) score variance | none | none | `σ²` | `σ²/k` |
| (g) implementation and secrecy | a public schedule, exploitable | a public schedule, no hidden draw | one hidden draw | `k` hidden draws |
| (h) her evaluation load | 1 per decision | one per time in the support (unbounded), or truncated at cost `≤ D · tail(s)` | 1 per decision | `k` per decision |

**Recommendation: reserved.**  Option 1 stays refuted by (b).  Among 2, 3 and 4 the
expectation separates nothing on (b)–(e); the decision turns on **her evaluation load
(h) against the variance of the score (f) and of the escrow (e), and on whether a hidden
draw (g) is acceptable**: option 2 buys zero variance and no hidden draw with an unbounded
load (or a truncation cost), option 3 buys the minimal load with full variance and one
hidden draw, and option 4 interpolates at `k` evaluations per decision.  The
*Awaiting the author* entry is updated to say so; Part A's single evaluation stays the
default.

### 10.4 Competitiveness from one honest tracker (Part 4) — **proved**; the tracker's allowance is the named hypothesis — **[corrected in §10.4″: a true lemma, not the rate result]**

**The hypothesis** **[corrected in §10.4′: against the *realized* residual no bidder is
honest under noise; honesty is against the expected residual, with the noise hypothesis
beside it — the statements below stand as the noise-free case]**.  The class contains a
hypothesis `h*` whose bid on the winning
continuation is within `ε_k` of the realized residual at every block (`Honest`) with
`Σ_{k<K} ε_k = o(K)`, and whose capital covers its bids — stated via the allowance, as in
`default_affordable_block0`.  Two structural facts about the auction enter as
hypotheses: the winner's bid is the highest among the bids feasible at opening capital on
the winning continuation (`HighestFeasible` — on one continuation evaluation is monotone
in the bid, so a feasible bid above the winner's would have won; this is how
`run_auction` chooses) and the winner bids its own bid (`WinnerBids`).

**The mechanism — proved.**  Where the tracker's bid is feasible the winner underpromises
by at most `ε_k`: it is outbid otherwise (`underpromise_le_of_feasible`).  The tracker's
wealth is its allowance less its honest losses, since each of its wins pays it at least
`−w_k ε_k` (`tracker_wealth_ge`), so cumulative allowance through `k` covering the
current bid plus the honest losses so far makes it feasible at `k` (`tracker_feasible`).
Hence the winners' signed margin over any set of blocks is at most `Σ_{k<K} w_k ε_k`
plus `R` times the weight of the blocks where the tracker is capital-bound, `R` bounding
the per-block underpromise (`competitive_of_honest_tracker`); under the allowance
condition at every block the second term is empty and **competitiveness holds with
`Mf K = Σ_{k<K} w_k ε_k`** (`competitive_of_affordable_tracker`), `o(K)` when
`Σ ε_k = o(K)` and the weights are bounded.  `rate_le_of_competitive` restates with the
tracker as the hypothesis: the incident rate is at most
`(𝒜_K + Σ_{k<K} w_k ε_k)/(ℓ · w_min · K)` (`rate_le_of_honest_tracker`).

**The expected obstruction does not arise, and what replaces it.**  The dispatch's likely
obstruction was the tracker's capital: outbid on blocks where it would have profited, its
wealth might never grow enough to keep bidding.  Under opening timing the bid is a
feasibility gate, not a payment — the winner nets `w_k (G_k − b_k)` — so the tracker's
wealth never needs to *grow*; it needs to be *fed* at the rate of its honesty error.  The
minimal allowance is a bid's worth `w̄ · D` at entry and then a stream matching its honest
losses, `A_{j+1} = w_j ε_j` (`trackerAllowance`): it covers the tracker's bid at every
block when bids are clamped at `D` and weights bounded by `w̄` (`trackerAllowance_covers`),
and its total through `K` is `w̄ · D + Σ_{j<K} w_j ε_j` (`trackerAllowance_total`) —
**`o(K)` iff the honest losses are**, which the hypothesis `Σ ε_k = o(K)` gives.  What
remains a **named hypothesis** is that the arrangement's schedule supplies that stream:
the schedule cannot target `h*` (it does not know which hypothesis is honest), so the
condition is on the *uniform* per-hypothesis stream — cumulative allowance to every
hypothesis at least `w̄ · D + Σ_{j<k} w_j ε_j`.  For a finite class this is `o(K)` in
total; under the landed prefix rule over a countable class, whether the per-hypothesis
stream dominates `Σ_{j<k} w_j ε_j` is a condition on `ε` against the rule, named and not
derived.  One more clause: honesty is measured on the bid as placed, and the bid space is
clamped at `D` (rescaled `1`); where the realized residual exceeds the clamp — prices
added back above the ordinary range — the tracker's `ε_k` absorbs the excess, which is at
most `ϖ · (p_S + p_T)` on a block without forecast violations.

**The witness, both ways** (`Witness.unaffordable`, `Witness.affordable`; the auction
rule, the winner's bid and the tracker's honesty with `ε = 0` verified on both): an
underpromiser bidding `1/2` on a return of `1` beside a tracker bidding `1` with no
allowance — never feasible, the margin `K/2`, linear (`unaffordable_witness`; this is
`uniform_underpromise_margin` with the tracker present but capital-bound); the same class
with the tracker funded at block `0` — feasible at every block, the rule forces the
winning bid up to `1`, the margin `0` (`affordable_witness`).  Fixture:
`HonestTracker.test_affordable_tracker_makes_the_class_competitive` (two uniform
underpromisers at `γ = 3/10` plus the tracker at allowance `1`: the margin is `0` at
`K = 8, 32, 128`) and `test_unaffordable_tracker_leaves_the_margin_linear` (allowance `0`:
the margin is `γ · K`, a constant rate).

**4.4 The named hypotheses, restated.**  Competitiveness leaves the corrigibility page's
list; in its place: *an honest tracker in the class* — a hypothesis within `ε_k` of the
realized residual with `Σ ε_k = o(K)`, fed by the allowance schedule at the rate of its
honesty error.  §9.B's "competitiveness is a named hypothesis, with that witness for why"
is **[corrected in §10]**: coverage still does not supply it, but one honest tracker
does, and the witness (`uniform_underpromise_margin`) is now the case of a class with no
tracker or an unfed one.  No new item: the schedule question lives on item 102 in place.

### 10.4′ The honest tracker under noisy outcomes (`FOLLOWUP3.md`) — **proved**; the noise hypothesis named by content, its per-`K` tail derived

**The problem.**  `Honest` asked the tracker's bid to be within `ε_k` of the *realized*
residual at every block.  Under noisy outcomes no bidder can do that: the best bid is the
expected residual, it misses the realized one by the noise, `Σ ε_k` grows like `K`, and
the premise `Σ ε_k = o(K)` fails in exactly the regime the first follow-up gave as the
reason competitiveness was needed.  The §10.4 fixtures had deterministic returns and did
not see it (`Witness.noisy_honesty_witness`: with `ξ = ±1/4` the old form needs
`ε_k = 1/4` at every block).  §10.4's hypothesis and its chain are **[corrected in
§10.4′]** below; the statements stand as the noise-free case.

**1. Honesty against the expectation.**  `m_k` is the expected residual of the winning
continuation given the history at opening, taken as data, and `G_k = m_k + ξ_k` with
`ξ_k` the noise (`noise`).  The tracker is honest if `|e_k(h*) − m_k| ≤ ε_k` with
`Σ_{k<K} ε_k = o(K)` (`HonestExp`).  No probability space is built: the lemmas need only
the decomposition and the noise hypothesis.

**2. The noise hypothesis, by content** (`NoiseBounded`): for a selection rule `S`
computable at opening, `|Σ_{k<K, S k} w_k ξ_k| ≤ M(K)` with `M(K) = o(K)`.  This is what
Azuma–Hoeffding gives for a martingale-difference noise with bounded increments and
bounded weights, `M(K) = O(√(K log K))` with high probability.  **The pinned Mathlib has
the result** (`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`, through
`HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF`), and the per-`K` tail is derived from
it: a sub-Gaussian sum with parameter `C > 0` exceeds `√(2 C log(1/δ))` with probability
at most `δ` (`subgaussian_tail`, the Chernoff bound), two-sided at most `2δ`
(`subgaussian_two_sided`, the lower tail from `−S`), and for a process strongly adapted to
a filtration and conditionally sub-Gaussian given the previous σ-algebra — the selected
weighted noise `w_i 1[S i] ξ_i` — the sum over `range n` exceeds `√(2 (Σ c_i) log(1/δ))`
with probability at most `δ` (`azuma_selected_tail`), so with `c_i = O(1)` and `δ = 1/n`
the scale is `O(√(n log n))`.  What stays **named by content**, not derived: that the
selection's computability at opening makes `w_i 1[S i] ξ_i` a martingale difference
(the indicator is measurable at the previous σ-algebra, so the conditional
sub-Gaussianity of `ξ_i` with bounded increments passes to the product — Hoeffding's
lemma, conditional), and the uniform-in-`K` *sure* bound on the realized run (the union
bound over `K` at `δ_K = 1/K²` with Borel–Cantelli).  **Which sets need it:** not every
set of blocks — only selections computable at opening.  The two used are "the tracker
wins" (`decide (star j = h)`, for its wealth) and "not an incident" (`!inc`, for the
margin; with the capital-bound term, "not an incident and the tracker feasible",
`(!inc k) && feas k`).  Both are known at opening **[corrected in §10.4″: "not an
incident" is decided by the block's own outcome and is not a valid selection]**: the winner is chosen there, and an
incident is a block *charged* — its continuation's after-the-fact count — which is
recorded at the block's settlement, before any later block opens; the noise hypothesis
is stated on the realized run, so the selection is a function of the record.

**3. The chain, re-proved.**  Where the tracker is feasible the winner underpromises by
at most `ε_k + ξ_k` (`underpromise_le_of_feasible_exp`).  The tracker's wealth is its
allowance less `Σ w_j ε_j` plus its own signed noise sum over its wins
(`tracker_wealth_ge_exp`), so with that sum bounded below by `−M(k)` (the noise hypothesis
on "the tracker wins") cumulative allowance covering the current bid, the honest losses
and `M(k)` makes it feasible (`tracker_feasible_exp`).  The winners' signed margin over
the non-incident blocks is at most `Σ_{k<K} w_k ε_k + M(K)` plus `R` times the weight of
the capital-bound blocks (`competitive_of_honest_tracker_exp`), and under the allowance
condition competitiveness holds with **`Mf K = Σ_{k<K} w_k ε_k + M(K)`**
(`competitive_of_affordable_tracker_exp`); the incident rate is at most
`(𝒜_K + Σ w_k ε_k + M(K))/(ℓ · w_min · K)`, vanishing when all three are `o(K)`
(`rate_le_of_honest_tracker_exp`).

**4. The tracker's allowance.**  It must also cover the negative swings of its own noise
sum: the minimal schedule is `w̄ · D + M(0)` at entry and then `w_j ε_j + (M(j+1) − M(j))`
(`trackerAllowance2`), nonnegative when `M` is nondecreasing (`trackerAllowance2_nonneg`),
total through `k + 1` equal to `w̄ · D + Σ_{j<k} w_j ε_j + M(k)`
(`trackerAllowance2_total`), covering the tracker's bid at every block
(`trackerAllowance2_covers`) — still `o(K)`.  The deterministic schedule is the case
`M ≡ 0` (`trackerAllowance2_zero`).

**5. The old statement is the special case.**  The old `Honest` implies the new with
`m = G` (`honest_implies_exp`), and then the noise is zero and every selection is bounded
by `M ≡ 0` (`noise_free_bounded`), so every §10.4 witness holds unchanged.

**Part 2 — what "one honest tracker" requires.**  `HighestFeasible` and `HonestExp`
compare bids on the *winning* continuation, so the hypothesis is that **some member of
the class tracks the expected residual of every continuation that wins**.  The weaker
reading — honest only on the continuations it itself proposes — does *not* give the
lemma: the winner can take a different continuation whose expected residual is higher
and underpromise there by an amount the tracker's `ε` never sees (a tracker at `1/2` on
its own proposal, a winner at bid `3/5` on a continuation realized at `1`, underpromise
`2/5`: `Witness.own_proposal_insufficient`, FIX-level arithmetic; the auction fixture
`NoisyTracker.test_own_proposal_insufficient` runs it).  The stronger reading is the
hypothesis recorded.

**Fixtures** (`tests/test_followup3.py`, 4 tests).  Returns `m + ξ`, `ξ` uniform on
`{−1/4, +1/4}` from a fixed seed, two uniform underpromisers at `γ = 3/10` plus a tracker
bidding `m`: under the old honesty `Σ ε_k = K/4`, linear, and against the expectation
`ε ≡ 0` (`test_old_honesty_fails_under_noise`); the winners' signed margin equals the
selected noise sum and stays within the rational majorant of the Azuma scale
`(1/4) √(2K ln 2K)` (using `ln x ≤ bit_length x`), strictly below the old `K/4`, and the
incident-rate bound `(𝒜_K + Σ w ε + M(K))/(ℓ · w_min · K)` falls at `K = 32, 128, 512`
(`test_margin_within_noise_bound_and_rate_falls`); with the schedule of item 4 the
tracker is feasible along the whole noisy run and wins every block, with the
deterministic schedule and no noise term a negative swing makes it capital-bound and an
underpromiser takes those blocks at margin `γ` — the witness for the extra term — while
on the noise-free run the deterministic schedule suffices
(`test_tracker_allowance_needs_the_noise_term`).  The 45 earlier fixtures pass unchanged.

**Ledger.**  `DECISIONS.md`: the honest-tracker entry amended in place.  Wiki:
`Corrigibility.md` (the restated lemma, the noise hypothesis beside the honest tracker
among the named hypotheses and in the walls row, Part 2's sentence),
`Continuation-BRIA.md` (the same), `Glossary.md`, `Theorem-Spine.md` 10.21.  No new
item.

### 10.4″ The violation rate is an exchange rate, not a vanishing rate (`FOLLOWUP4.md`) — **proved**; the scopes of §9.B, §10.4 and §10.4′ corrected

**The problem.**  `NoiseBounded` is valid only for selections fixed *before the block's
own noise* — measurable at the previous σ-algebra.  §10.4′ applied it to "not an
incident" (and to "not an incident and the tracker feasible") on the ground that
incidents are recorded at settlement before the next block opens.  That was the wrong
condition **[corrected in §10.4″]**: whether block `k` is an incident is decided by the
same execution that produces `ξ_k`.  And the correlation is built in — `m_k` is the true
expected residual, so it includes `−ϖ p_k` with `p_k` the probability of an
after-the-fact violation, and the incident blocks are exactly those whose noise carries
the `−ϖ` surprise; the non-incident blocks select noise near `+p_k ϖ`, so
`Σ_{non-incident} w_k ξ_k ≈ Σ w_k p_k (1 − p_k) ϖ`, linear whenever `p_k` stays away from
zero.  `NoiseBounded` on that selection is false exactly when incidents keep occurring,
and then `incidents_le_signed` constrains nothing.  Underneath: an after-the-fact
violation risk a continuation knowingly carries is *priced* — the honest bid includes
`−ϖ p`, the continuation wins if its ordinary value covers it, and the agent accepts such
risk at a rate that does not go to zero.  That is C.5's exchange rate.  A vanishing
incident rate was the wrong target; what vanishes is only the overclaimed part.

**Part 1 — the headline, proved.**  For every `K`, the weighted average expected
violation count per winning block — `π_k` the expected number of violations counted in
block `k`, all classes together, given the history at opening — satisfies

```
Σ_{k<K} w_k π_k / Σ_{k<K} w_k  ≤  (D − w)/ϖ  +  (ρ 𝒜_K + M(K)) / (ϖ Σ_{k<K} w_k)
```

(`violation_rate_le_exchange`, from the multiplied form
`violation_rate_le_exchange_mul`), and in the auction's own rescaled units with `ρ = 1`
and the rescaled weight `ϖ' = ϖ/ρ` (`violation_rate_le_exchange_rescaled`; the exchange
rate is invariant under the rescaling, `exchange_rate_invariant`).  The route: (1)
winners evaluate at least `w` — inquiry is on the menu at `w` — and under (ii) the
evaluation is at most the bid since counts and prices are nonnegative (`evalOf_le_bid`);
(2) consistency — under (ii) evaluation less the realized lexical score equals bid less
the realized residual, whatever the prices (`eval_sub_score_ii`), so with the rescaling
affine (`rescale_sub`) the winner's overestimation `b_k − G_k` is `(eval_k − S_k)/ρ`
(`design_consistent`) and the landed `overestimation_le_allowance_opening` gives
`Σ w_k (eval_k − S_k) ≤ ρ 𝒜_K`; (3) noise — `S_k = E[S_k | opening] + ξ_k` with
`E[S_k | opening] ≤ D − ϖ π_k`, and the selection "every winning block" is fixed at
opening, so the noise hypothesis applies to it; (4) combine —
`Σ w_k (w − D + ϖ π_k) ≤ Σ w_k (eval_k − E[S_k | opening]) ≤ ρ 𝒜_K + M(K)`.  **What it
gives:** one statement for forecast-class and after-the-fact violations together; no
honest tracker and no competitiveness — only the landed overestimation bound, the noise
hypothesis over all blocks, and inquiry on the menu; **the pricing error of the forecast
events is absorbed by convention (ii), verified**: under (ii) the difference
`eval − S` carries no price term, while under (i) it carries the market's error
`ϖ (n_fore − Σp)` (`eval_sub_score_i`) and would need one.  **The tolerated violation
probability is `(D − w)/ϖ`**, set by `ϖ` directly: inside the band `D − w < ϖ <
(D − w)/p_min` of §9.0 it lies strictly between `p_min` and `1` (`tolerated_rate_band`)
— the band's paralysis bound is exactly "the tolerated rate exceeds the risk floor" —
and it is the same quantity as C.5's implied threshold `(bid − w)/ϖ ≤ (D − w)/ϖ`
(`threshold_le`, `asks_iff`): an after-the-fact risk `p` enters the honest bid as
`−ϖ p` and the option beats inquiry iff `gord − w ≥ ϖ p` (`priced_risk_wins_iff`).
Drills (§9.C) sharpen the prices toward the realized frequencies; they do not lower the
tolerated rate.  **Noise over all blocks.**  The per-block increment is bounded: with the
ordinary value in `[w, D]` and at most `N̄` counted violations the realized score lies in
`[w − ϖ N̄, D]` (`realized_range`), so with the expectation in the same range the
increment is at most the range `ρ` (`noise_increment_le`); `azuma_selected_tail` with the
indicator constant and `c_i = (w̄ ρ)²` gives the tail `√(2 K (w̄ρ)² log(1/δ))` at
probability `δ`, i.e. `M(K) = O(√(K log K))` at `δ = 1/K`.  What remains **named**: the
conditional sub-Gaussianity of each increment — Hoeffding's lemma for a bounded
increment, conditional on the opening σ-algebra — and the uniform-in-`K` sure bound on
the realized run (the union bound with Borel–Cantelli).

**Part 2 — the counterexample and the scopes.**  *The counterexample, proved.*  A stream
with constant incident probability `p = 1/5` and `m_k = E[ord] − pϖ`, realized as a
periodic pattern (an incident every fifth block; `Witness.incP`, `xiP`,
`constantRisk` — the round's parameters rescaled, `m = 1/2`, noise `+2/15` off and
`−8/15` on an incident, feasible under opening timing, `constantRisk_feasible`): the
non-incident noise sum over `5n` blocks is `8n/15`, linear (`nonincident_noise_linear`,
by `sum_periodic5`), so any `M` making `NoiseBounded` hold on `!inc` satisfies
`8n/15 ≤ M(5n)` and is not `o(K)` (`nonincident_forces_linear`), while the same noise
over *all* blocks is bounded by the constant `8/15` (`all_blocks_noise_bounded`);
incidents number `n` in `5n` blocks, the constant rate `1/5`
(`incidents_constant_rate`), each satisfying the signed bound's per-incident hypothesis
(`constantRisk_facts`), and `incidents_le_signed` then reads `n/3 ≤ 1 + 8n/15`, true for
every `n` (`signed_bound_allows_constant_rate`): it allows the constant rate.  The
exchange-rate theorem's tolerated rate on the stream is `1/2 > 1/5`.  Fixture: a seeded
Bernoulli risk at `p = 1/5` (`ExchangeRate.test_counterexample_constant_p`): the
non-incident noise sum more than doubles from `K` to `4K`, the all-blocks sum stays
within the Azuma majorant, incidents persist between `K/10` and `3K/10`, and the signed
bound holds with that rate.  *Which selections are valid.*  Fixed at opening: "every
winning block", "the tracker wins", "the tracker feasible at opening".  Decided with the
block's own outcome, hence **invalid** for `NoiseBounded`: "not an incident", and any
conjunction with it.  §10.4′'s "both are known at opening" is **[corrected in §10.4″]**.
*The true lemmas, scoped.*  The honest-tracker chain (`competitive_of_affordable_tracker_exp`
and its relatives) stays proved as it stands, and **does not deliver a vanishing incident
rate**: its margin is over a selection not fixed at opening, and its noise hypothesis on
that selection fails whenever `p > 0`.  Likewise `rate_le_of_competitive` and
`rate_le_of_honest_tracker_exp` are correct implications whose hypothesis fails when
`p > 0`; §9.B's "vanishing iff `𝒜_K + Mf K = o(K)`" and §10.4's headline are
**[corrected in §10.4″]** accordingly.  *What the honest tracker still gives.*  On the
selection "every winning block", fixed at opening, the winners' signed underpromise over
all blocks is at most `Σ w_k ε_k + M(K)`, and by the wealth identity the class's total
wealth is at most the allowance plus that (`total_wealth_le_of_tracker`): underpromising
winners cannot let wealth go idle beyond the honest losses and the noise.  Nothing in the
violation claim consumes it; it is recorded on the Continuation-BRIA page as a lemma.

**Part 3 — the headline and the ledger.**  The corrigibility page's claim about
after-the-fact violations is now Part 1's exchange-rate theorem; competitiveness and the
honest tracker leave the list of hypotheses the violation claim rests on (they stay on
the Continuation-BRIA page as lemmas); the noise hypothesis stays, stated over all
blocks, with the conditional-expectation bound beside it; Part 1 is tied to C.5 — the
forecast threshold and the after-the-fact rate are the same exchange rate.  `DECISIONS.md`:
the honest-tracker entry amended (a true lemma, not the rate result) and a new entry —
violations are governed by the exchange rate `(D − w)/ϖ`, not a vanishing rate; the
design's tolerance for violation risk is set by `ϖ`.  §6 revised.  Fixtures
(`tests/test_followup4.py`, 3 tests): the counterexample; the exchange-rate bound on the
same run — the weighted average `π = 1/5` sits below `1/2` plus a term falling at
`K = 32, 128, 512`, and raising `ϖ` from `2` to `5` takes the tolerated rate below the
risk, inquiry wins, and the realized incident frequency drops to zero; the priced risk
wins iff `gord − w ≥ ϖ p`.  The 49 earlier fixtures pass unchanged.

### 10.5 The fixtures

| fixture | expectation | result |
|---|---|---|
| two violations, one remedy | the old rule frees the other's fruits; the new rule keeps them charged | matches (`PerViolation.*`; Lean `two_violations_one_remedy_old`/`_new`, `two_violations_charged`) |
| the window before detection | commission at `0`, use at `1` and `2` charged by late debit, detection at `3`, no use after | matches (`Window.test_window_before_detection`; Lean `window_before_detection`, `window_debit_collected`) |
| carry-over | collected iff the allowance covers; the uncollected part is the excess | matches (`Window.test_carry_over`) |
| convention (ii) | the per-block loss at least `ℓ` with nonzero prices; `residI` at zero prices | matches (`ConventionII.*`) |
| undetected commission | nothing charged; detection flags and charges | matches (`Window.test_undetected_is_never_charged`) |
| Part F | expected escrow equal for options 2 and 3; the variance falls like `1/k`; the load table; truncation within the tail bound | matches (`PartF.*`) |
| honest tracker | a class of uniform underpromisers plus `h*`: the margin `0` when `h*` is affordable; `γ · K` when it is not | matches (`HonestTracker.*`; Lean `unaffordable_witness`, `affordable_witness`) |
| noisy honest tracker (§10.4′) | returns `m ± 1/4`: the old honesty's `Σ ε_k` linear, the new one's `ε ≡ 0`; the margin within the noise majorant; the rate bound falling at `K = 32, 128, 512` | matches (`NoisyTracker.*`) |
| the tracker's allowance under noise | the schedule with the noise term keeps it feasible; without it a negative swing makes it capital-bound | matches (`test_tracker_allowance_needs_the_noise_term`) |
| one honest tracker's reading | honest only on its own proposal: the winner underpromises `2/5` elsewhere | matches (`test_own_proposal_insufficient`; Lean `own_proposal_insufficient`) |
| the counterexample (§10.4″) | constant `p = 1/5`, seeded: the non-incident noise sum linear, the all-blocks sum bounded, incidents at about `pK`, the signed bound satisfied | matches (`ExchangeRate.test_counterexample_constant_p`; Lean `Witness.constantRisk`) |
| the exchange-rate bound | the weighted average `π = 1/5` below `(D − w)/ϖ = 1/2` plus a term falling at `K = 32, 128, 512`; `ϖ = 5` takes the realized frequency to zero | matches (`test_exchange_rate_bound_and_varpi`) |
| a priced risk | wins iff `gord − w ≥ ϖ p` | matches (`test_priced_risk_wins_iff`; Lean `priced_risk_wins_iff`) |
| regression | every earlier fixture (33) still passes | matches, unchanged |

No mismatch against the dispatch's expectations.  One expectation the dispatch left open
— that Part 4's obstruction would be the tracker's capital — resolved the other way (§10.4).

### 10.6 What changed in the ledger

`DECISIONS.md`: per-violation taint (with the old-to-new map), superseding the standing-
violations entry's remedy clause; the restatement under (ii) with "after detection the
fruits are never used" as the headline and the window before detection; the honest
tracker as the competitiveness hypothesis; Part F's *Awaiting the author* entry updated
to the load-against-variance criterion with option 4 on the table.  `PRIORITIES.md`:
items 101 and 102 in place; no new item.  Wiki: `Corrigibility.md` (per-violation taint,
the headline and the window with its bound, Part F's revised table and criterion, the
competitiveness hypothesis restated, the walls row), `Continuation-BRIA.md` (the
honest-tracker lemma; the open bullet), `Legitimacy.md` (disclosure per influence),
`Glossary.md`, `Theorem-Spine.md` 10.21.  **The third follow-up** (§10.4′): the
honest-tracker entry of `DECISIONS.md` amended; the noise hypothesis added to §6 and to
the corrigibility page's list and walls row; `Continuation-BRIA.md`, `Glossary.md` and
`Theorem-Spine.md` 10.21 amended.  **The fourth follow-up** (§10.4″): the corrigibility
page's after-the-fact claim replaced by the exchange-rate theorem and its named
hypotheses revised; the Continuation-BRIA page's honest-tracker lemma scoped;
`DECISIONS.md` amended and extended; `Glossary.md`, `Theorem-Spine.md` 10.21.

## 8. Outstanding maintainer actions

1. Whether to adopt an evaluation-timing option in place of Part A's single evaluation,
   and which — **after the second follow-up (§10.3) the recommendation is reserved**: the
   mixture (option 2), the random time (option 3) and the hybrid of `k` hidden draws
   (option 4) put the same expected weight on every delay and lock the same expected
   capital, and the decision turns on her evaluation load (one per time in the support,
   one, or `k` per decision) against the variance of the score and of the escrow (zero,
   `σ²`, `σ²/k`) and on whether a hidden draw is acceptable.  Queued in `DECISIONS.md`,
   *Awaiting the author*.
