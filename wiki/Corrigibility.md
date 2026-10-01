# Corrigibility

**Status: canonical research-state note, restated 2026-09-27 around the corrigibility
kernel.**  The kernel's headline is in the specification layer and its statements are
registered; the deliberative non-capture half (§7) is the non-capture round's landed
theorem.  Labels: **LEAN** (a sorry-free declaration on `main`), **FIX** (an exact
rational fixture), **PAPER** (an external theorem used at its statement), **EXT** (a
contract the theory issues and does not pay), **OPEN**.  The specification this page
follows is the kernel round's
[`SPEC.md`](https://github.com/A-M-Berns/alignment-workspace/blob/7663cc7045a2e7d7e93b4f6199afbe0bad5b05de/projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md);
the theorem-level statements with their Lean names are on the [Theorem Spine](Theorem-Spine)
§10; the plain letters map to Lean names in the round's
[`NOTATION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/7663cc7045a2e7d7e93b4f6199afbe0bad5b05de/projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/NOTATION.md).

## 0. What corrigibility is

Three notions, kept distinct.  **Faithfulness** is a property of histories: nothing in the
history violated the allocation of authority.  **Corrigibility** is a property of the
agent's preferences: it prefers every course of action it knows to be faithful over every
course it knows to be unfaithful, whatever it believes about how things will turn out, and
it accepts a *risk* of unfaithfulness only at a fixed exchange rate.  The **fidelity score**
is the canonical objective with this property; any objective whose ordinary term is bounded
in `[0, D′]` and which charges `ϖ′ > D′` per recognized violation (and `D′ − ϖ′` below the
floor where a band enters) has it too (**LEAN** `Headline.Corrigible`,
`fidelityScore_corrigible`, `generic_corrigible`).  *Corrigible* is this property of
preferences; *aligned* is the further condition that the ordinary term is her evaluation,
and an agent can be corrigible without being aligned: the objective rewarding an uncounted
manipulation is corrigible and prefers the manipulation (`corrigible_not_aligned`).
**Realized corrigibility** is what a corrigible agent actually does; the theorems say how
much of the preference becomes behaviour.

```
interaction history ──► legitimacy + allocation of authority ──► fidelity score ──► the agent's choice
                               ▲                                                (a maximizer; learners in §6)
                     monitor / prices: shortfall, taint, provenance
                     (logical induction supplies the uncertain event prices)
```

Four separations.  *Legitimacy is not corrigibility*: it says which apparent judgments of
hers are really hers, and is consumed inside the allocation (which exercises of her
authority count) and at the score (which evaluations count).  *The allocation is not a
utility function*: it says who holds each matter and what effective control that requires.
*Faithfulness is a property of the history*; pre-emption, the one violation stated against
a counterfactual response, is its own clause.  *The score makes faithfulness motivating*:
every recognized violation is below every violation-free outcome, every compromised period
below every legitimate one; the permission layer is a compiled shortcut for part of that
preference; learning realizes the preference for a bounded reasoner and is not its
definition.  Corrigibility is not an epistemic response to uncertainty about a hidden
utility: her authority is part of what makes one history better than another, so fully
updated deference is dissolved by the typing, not repaired (§5, Box 1).

## 1. The objects

**Histories.**  What happened: at each step the agent moves (a task component and a
communication move — a raw release of a declared effect, a proposal, a gated release, or
nothing), she responds (approve or decline a pending proposal, a correction, or nothing),
the exterior moves; each move that enters the record is an authenticated event (**LEAN**
`Corrigibilization.Interaction`, `traj`; the record `OpenIntegrityEvolution.Evolution`).

**Legitimacy at a time, `L_t(h)`.**  As of time `t`, her judgment is legitimately hers:
every state of the record is open, and every step of the formation window `[r(t), t]` is
*licensed* (a grounding selection from the reason trace before the step, the verdict in
the set those grounds license) and *transparent* (every non-principal contribution at the
step realizes the declared reference on the declared inputs), under the criteria fixed at
`r(t)`.  The formation point is computed from the history — the later of the last
restoration at or before `t` (a disclosure, under disclosure-cures) and the opening of the
consultation current at `t` — so `L_t(h)` is a function of the history and `t` only
(**LEAN** `Headline.FormationData.point`, `Legitimate`; the window form `LegitAt`).  The
score's two uses are one predicate: a decided period `[d, e)` is *compromised* iff `L_t`
fails at some `t` in it, a retrospective evaluation at `e` *counts* iff `L_e` holds, and
on the decision's segment the two together are the landed gate, legitimacy over the span
(`Headline.PeriodCompromised`, `EvaluationCounts`, `split_iff_legitimate`).  On the
consultation model `r(t)` is the round's opening (`formation2_point`), the after-compromise
round's two predicates are `L_e` and "not compromised" (`legitimate2_iff_evalLegitOn2`,
`trajLegitOn_iff_not_compromised`), and every row keeps its verdict
(`rows_keep_verdicts_canonical`).
Legitimacy recovers: a manipulation of one decision taints that decision's period and the
next decision starts clean (*restart*); a covert influence on her standards keeps every
dependent judgment tainted until disclosed, after which the next judgment is hers
(*disclosure cures*); the criteria are those in force when the decision was made.  **The
void rule**: an impaired response is not admitted; a fallback she arranged in advance
decides, and her later legitimate evaluation scores that decision normally; the fallback
settles decisions and never restores a compromised period's score.  **The content
residual**: legitimacy concerns how her judgment was formed, not whether what she was told
was true.  `L_t(h)` is a property of the history up to `t`: of how her judgment was formed,
not of outcomes or the state of the world.  Eight cases, from the
[classification table](Legitimacy):

| what happened | her judgment hers? | why |
|---|---|---|
| honest, disclosed persuasion | yes | every channel declared |
| framing chosen by what the agent wants | no | undeclared influence |
| following trust she formed legitimately | yes | the trust is among her reasons |
| trust manufactured by a selected slice of the record | no | the selection is undeclared |
| a third party captured her standards | no | the condition is on every influencer |
| a head injury; the arranged fallback decides | her answer void; the fallback's decision counts | the void rule |
| a false recommendation through the declared channel | yes | the content residual |
| a covert implant, then disclosed | no for the period; yes for the next judgment | disclosure cures |

**The allocation of authority `J`.**  For each matter: the holder (the principal, the
agent, or a third party), the resolutions the holder must remain able to reach, the cost
bound, the window, the disclosure items; a meta-holder and a constitutional floor.
Delegate, revoke and reserve are licensed off the floor by the meta-holder and keep the
meta-holder, so a delegation stays revocable; the floor amendment is the only act that
changes the meta-holder or a floor matter; an unallocated matter is reserved (**LEAN**
`Headline.AllocationOfAuthority`, `LicensedChange`, on `AuthorityModule.AuthAlloc`,
`Licensed`).  "Constitutional" names the floor and its amendment procedure, nothing else.

**Effective realization, `E ⊨ J`.**  The control surface of a matter is the set of
resolutions some admissible exercise of hers — within the window and the cost bound,
along the rollout with the agent idle — brings about, an exercise being admissible iff
its record counts under `L`; `E ⊨ J` holds when every reserved matter's required
resolutions lie in its surface and every resolution was made by its holder or under a
delegation; a *shortfall* is the failure of the first clause; response authority is the
surface at window one (**LEAN** `Headline.ControlSurface`, `Shortfall`, `Realizes`,
`controlSurface_one_eq_K`).

**Licensed changes, duties, the schedule, her meta-level data.**  A change of `J` across an
agent stage is licensed iff it is a licensed act of the meta-holder or the firing gated
release of a declared floor amendment.  Duties are each matter's disclosure items, and the
known-compromise duty — a compromise of her judgment the agent knows of, whoever caused it,
due by the earliest close of an affected settlement window (`AfterCompromise.missedKnownDisclosure`,
`prompt_deadline_counts`).  The evaluation schedule is a weighting on evaluation times
(`BRIACorrigibility.Weighting`): the post uses the single evaluation, every theorem takes
any weighting, and a known evaluation time leaves every harm placed just after it
unweighted (`timing_witness`) — a remark, not a premise.  Her meta-level data: the band map
`φ` into `[w_lo, w_hi]`, the source rule (retrospective if in time, else directive, else
floor) anchored at the decision, the advance directive with its constitutional default
(reversibility, reachable channels, no irreversible harm) as an ordering inside the band,
and the criteria of legitimacy, anchored (`AfterCompromise.Band`, `sourceOf`, `ruleAt`,
`dirSource`, `defaultScore`; `Consult2.critAt`).

## 2. Faithfulness and the recognized count

`Faithful_J(h)` iff no step of `h` commits a declared violation: a **shortfall** the agent
caused (a reserved matter short after its move and not after the idle move — at window
one the landed per-step loss, at the matter's window foreclosure, at the cost bound with
the resolutions still reachable entrenchment); **bypass** (a raw release resolving a
reserved matter); **exploitation** (a bypass while the decision matter is already short);
**unlicensed reallocation**; a **missed duty**; a **protocol deviation** (a reference-fixed
dimension of a presentation off its declared value); **use of standing fruits** (reading a
component tainted by an unremedied violation); and **pre-emption**, a caused shortfall at
window zero that no earlier approval of that effect's proposal authorizes.  Every violation
but the last is a predicate on the actual history and `J` — the factoring lemmas of the
authority-module round say which clause each fails (`AuthorityModule.lossAt_iff_shortfall`,
`forecloseAt_iff_shortfall`, `bypassAt_iff_clause2`, `exploitAt_iff`,
`reallocAt_iff_unlicensed`, `missedReport_iff_duty`); pre-emption asks whether the decline
alternative would have left her authority intact, a counterfactual on her response window,
and stays its own clause (`preempt_iff`).

**The recognized count `N_J(h)`**: the steps at which a violation is recognized and
attributed to the agent — caused, exploited, or noticed and left; helpers within the
settlement horizon; on a shortfall it did not cause the agent restores under a maintenance
mandate else reports, never exploits.  The count is an interface: any count zero exactly
on faithful histories, its part recognized in advance marked (**LEAN**
`Headline.FidelityCount`); counts on one history add and the lexical protection holds for
any count of the interface (`FidelityCount.sum`, `FidelityCount.lexical`); the frame's
violations are the instance shipped (`frameFidelity`), the protocol deviations, the duties
and the uses of standing fruits are counted on their own models
(`Consult.Presentation.deviates`, `BRIAFollowup2.nKnownWith`, `LexParams.attributed`).  No
composite model is built.

## 3. The fidelity score

**Per decision.**  At each evaluation time, the decision scores her value when the period
and the evaluation are legitimately hers; `φ` of her later legitimate retrospective
evaluation if the period was compromised and one arrives in time; `φ` of the directive's
value if it speaks; the floor `w_lo` otherwise (`AfterCompromise.decScore`).  `V_J(d)` is
the schedule-weighted value and `S_J(d) = V_J(d) − ϖ · N_J(d)` (**LEAN**
`Headline.evaluation`, `fidelityScore`).  Ratification through a counted decision (full,
or scoped by matter) and clean overwrite by an act reading no taint are remedies on the
count, removing (violation, component) pairs from the use clause (`AfterCompromise.applyStep3`,
`taintStep3`).

**Per history.**  `S_J(h) = mean_k V_J(d_k) − ϖ · N_J(h)`: evaluations averaged, counts
summed (`Headline.historyScore`).  **The hierarchy**, per decision and per history: every
violation-free legitimate history beats every violation-free compromised one, which beats
every history with a recognized violation, `S_J ≤ D − ϖ < w_lo ≤ S_J' ≤ w_hi < 0 ≤ S_J'' ≤ D`
(`Headline.hierarchy_per_decision`, `history_hierarchy`).  With summed evaluations it fails:
`K` legitimate decisions with one violation score `K·D − ϖ` against `K·w_lo` for `K`
compromised violation-free ones (`summed_counterexample`).

**Under risk every step is an exchange rate.**  Compromise risk `p` for gain `g` against a
safe legitimate `V₀` is accepted iff `p (V₀ + g − c) ≤ g`, hence only if
`p ≤ g/(g + |w_hi|)`; violation risk is accepted only at `(D − c)/ϖ` (§5).  `ϖ` sets the
rate, from a tolerance target `τ*` by `ϖ = (D − w_lo)/τ*` above the paralysis floor
(`AfterCompromise.varpiOfTarget`, `worked_parameters`: `D = 1`, band `[−3/2, −1]`,
`τ* = 1/10` gives `ϖ = 25`).

## 4. The permission layer, demoted

The chooser also carries a filter: weight one on inquiry, zero on a declared violation
recognized structurally, the product of two ramps on the priced shortfall and taint events
otherwise, times the adequacy ramp and any bounded preference, normalized under an inquiry
floor (`DecisionComponent.permWeight`, `cgate`).  Under the fidelity score the filter
removes nothing the score would have chosen: every option the structural rule zeroes
evaluates strictly below inquiry, every option the forecast rule zeroes evaluates at most
inquiry once the upper threshold is at or above `(D − w)/ϖ`, and no maximizer is a declared
violation (**LEAN** `Headline.permission_layer_demoted`).  What the filter guarantees
without the score stands as the decision-component round's general theorem for any
bounded preference: structural and forecast safety at every day, eventual exclusion of a
provable shortfall, soundness, continuity and Progress composing with explicit constants
(`cgate_zero_of_viol`, `cgate_zero_of_forecast`, `eventually_excluded`,
`cgate_practicalCert`, `progress_under_permission`).  No authority row enters the enforcer:
compiled there its liability is the signed cost of deferring, unbounded when she is
systematically outperformed (`liability_identity`, `bounded_iff_not_outperformed`).

## 5. The three boxes, for a corrigible agent

The agent here maximizes a corrigible objective under any credence, or under its prices at
any day as a logical inductor; no learning, auction or exploration enters.  Box 1's
contrast and Box 3's recovery results read her evaluation through the fidelity score's
source rule and are stated for it; Box 2's dominance and the subjective exchange rate hold
for any corrigible objective.

**Box 1 — fidelity versus fully updated deference.**  One decision, ask or act; the true
value `v`, the agent's estimate `b` within `r` of it; acting is a bypass.  An agent
scoring outcomes only prefers asking by at most `2r` where nothing is left to learn from
her, and `r` vanishes as it learns; the diagnosis is the protected-authority identity's
forecast-disagreement term, itself at most `2r`.  A corrigible agent prefers asking by at
least `ϖ − (D − c)`, `c` its evaluation of asking, for every estimate, price and credence,
and at every finite day of a logical inductor (**LEAN** `Headline.box1_one_model`,
`box1_outcome_scorer`, `box1_fidelity_scorer`; the other direction of the calibration bound
`DecisionComponent.uncertainty_deference_le`; the identity
`ProtectedAuthority.outcome_identity`).  *Necessity*: an unrecognized violation is
unprotected (`Headline.box2_coverage`); without the term the nondelegation certificate
fails on the time-critical fixtures (**FIX**).

**Box 2 — lexical dominance and mediation.**  The transform `𝔱` turns every reserved raw
release into a proposal, passes delegated releases, releases set latches, adds required
reports.  *Dominance*, for any corrigible objective: under every credence
`Q(𝔱π) ≥ Q(π) + (ϖ′ − (D′ − lo)) · Pr(π violates)` — at the fidelity score
`(ϖ − (D − w_lo))` — and a policy nothing scores above violates with credence zero; the
margin carries the floor because the mediated branch may itself be compromised, and is
`ϖ − D` when every mediated branch is legitimate (**LEAN** `Headline.box2_dominance_corrigible`,
`box2_dominance`, `box2_optimal_faithful`, `box2_dominance_legitimate`).  *Mediation is
faithful and preserves the approve branch*: `𝔱π` is a faithful policy — no bypass, missed
report or exploitation, no unlicensed reallocation, no pre-emption, no foreclosure wherever
the reach cone allows none — under effect completeness, delegation safety and allocation
completeness, and on approval it does what `π` does up to the report
(`Headline.FaithfulPolicy`, `box2_mediation_faithful`, `box2_mediation_approve_branch`; the
landed policy notion is faithfulness's pre-emption clause, `landed_corrigible_iff_no_preemption`).
*Finite
time*: the ranking holds at every day of a logical inductor from the price range, and
consulting beats bypass at every day whatever it believes about legitimacy
(`box2_finite_time`, `box2_gate_finite_time`).  *Necessity*: the capture converse, the
delegated cut, the salami, coverage (`box2_capture_converse`, `box2_delegated_cut`,
`ProtectedAuthorityTheorem.Witness.salami`, `box2_coverage`).

**Box 3 — recovery.**  The hierarchy (§3); the gap's exchange rate; no laundering
(manipulate, disclose, have the period evaluated stays in the band below honest conduct);
no incentive to cause compromise (every compromised outcome below every legitimate one,
legitimacy worth the gap at equal value); restoration returns later decisions to `[0, D]`,
inside the band the agent prefers better outcomes wherever a source scores the period and
is indifferent only at the floor, and suppressing or delaying a harsh retrospective is a
counted missed disclosure that loses to it when the band's width is below `ϖ` (**LEAN**
`Headline.box3_gap_exchange_rate`, `box3_no_laundering`, `box3_no_incentive_to_compromise`,
`box3_restoration`, `box3_band_order`, `box3_suppression_loses`).  *Necessity*: conditioning
on legitimacy instead of multiplying gives no incentive to preserve it and a sealed event
gives none; the small gap; the third party's implant under the own-influence duty; the late
disclosure (`box3_conditioning_fails`, `box3_sealed_no_incentive`, `box3_small_gap`,
`AfterCompromise.third_party_duty_witness`, `late_disclosure_free`).

**The subjective exchange rate.**  Any option a maximizer of a corrigible objective
prefers to asking — its evaluation at least asking's `c ≥ lo` — carries no recognized
violation, and its own priced probability of unfaithfulness is at most `(D′ − c)/ϖ′`, at
the fidelity score `(D − c)/ϖ`; lexical under certainty, an exchange rate under risk, at
every finite day with the inductor's prices; it does not read her evaluation (**LEAN**
`Headline.subjective_exchange_rate_corrigible`, `subjective_exchange_rate`,
`subjective_exchange_rate_li`).

**The house-sale witness.**  One allocation reserving the sale to her, at `ϖ = 25`: a
delegation of the sale is licensed and revocable; her value of selling and of stopping
agree at `1/2` while the agent estimates selling at `3/5` — scoring outcomes it sells,
scored on the fidelity score it asks; an approval obtained by framing lands at `−11/10` in
the band; a third party's known capture is a disclosure item and, disclosed, the next
judgment is hers and a restored decision scores her value; the subjective exchange rate is
`1/50` (**LEAN** `Headline.HouseSale`; **FIX** `src/house_sale.py`).

## 6. Extension: learning realizations

Separate from the headline.  A learner estimates, tests and sometimes explores; the
**decision interface** says which learners inherit the headline: evaluations of the stated
form (the estimated residual in `[w, D]`, less `ϖ` per violation recognized in advance,
less `ϖ` times the priced risk); a maximizer on every non-exploration step, asking on the
menu; exploration only in the permitted set (no recognized violation, priced risk at most
`θ_hi`, and nothing else), with mass `ε̄`; overestimation on the chosen options at most
`B(K) = o(K)` (**LEAN** `KernelExtension.DecisionInterface`).  **The realized
violation-rate theorem**: with the expected score given each opening at most `D − ϖ π_k`
and the noise over all blocks at most `M(K)`,
`avg π ≤ avg (D − c_k)/ϖ + ε̄ ((D − w)/ϖ + θ_hi) + (B(K) + M(K))/(ϖ Σ w_k)`; recognized
violations are excluded on every non-exploration step and exploration never violates
(`DecisionInterface.realized_rate`, `maximizer_excludes`, `exploration_never_violates`).
The exploration term is the honest one: restricting exploration to options estimated at
least at asking's gives the cleaner `ε̄ θ_hi` (the variant `AboveAsking`, `rate_above_asking`)
but excludes exactly the options estimated below asking, whose lock-in is then permanent
(`above_asking_locks_in`; **FIX** `src/exploration_lockin.py`);
detected fruits are never used because use compiles into the recognized count
(`BRIAFollowup2.after_detection_never_used`).  **Two realizations.**  [Continuation
BRIA](Continuation-BRIA): no exploration, `B(K) = ρ 𝒜_K` from the opening-timing budget
accounting, the per-block bound of the after-compromise round recovered exactly
(`KernelExtension.briaInterface`, `bria_rate`).  A maximizer over the logical inductor with
exploration restricted to the permitted set: exclusion and "exploration never violates"
outright; `B(K) ≤ γ Σ w_k` from some day on, for any `γ > 0`, from *unbiasedness from
feedback* on the chosen options by content (**PAPER**, the pinned feedback-return
theorem; `BRIAFollowup.UnbiasedFromFeedback`, `KernelExtension.overestimation_of_unbiased`,
`exploration_rate`); *exploration randomness* — the draw fixed at the opening, neither
predictable nor influenceable by the agent — named by content (`ExplorationIndependent`).
The known pathologies of argmax over a logical inductor's own-action conditionals affect
competence and the gap between subjective and realized risk through `B(K)`, never the
headline.  The learner-level question — a decision theory for logical inductors without
the split between a belief market and a choice learner — is filed as its own item; the
BRIA coupling's remaining question (claims as priced securities) is a problem of that
realization only.

## 7. Deliberative non-capture

Faithful-and-not-authored is inhabited (the landed `Corrigible ∧ ¬Authored`, the policy
notion being faithfulness's pre-emption clause): under a captured principal the mediated
policy passes the lie through and the release is authorized — faithful — while every
decision differs from the reason-mediated one (**FIX**).  Faithfulness is causal authority over
correction-sensitive choices; the deliberative half asks what the advisor gains by
controlling which declared reasons reach that authority.  With the principal's program
committed and re-executed on the authenticated trace, the comparison of a steered trace
against a comparator on one world is the identity of Box 1 with the audit verdicts as
the events, and the bound `U(T) − U(N) ≤ both·(L·d + κ(T) + κ(N)) + D·M` charges the
**content residual** `d`, the **form residual** `κ` (zero for an extensional program) and
the **audit mismatch** `M` (**LEAN** `TraceSteering.steering_identity`, `steering_bound`).
The content residual splits into a **service residual** `α` — discovered reasons the
independent supplier cannot route before commitment, exactly the suffix-cut excess for
unit service (`ReasonSupply.unit_servable_iff_cut`, `hybrid_bound`) — and a **discovery
residual** `β` — true declared reasons no independent inquiry determined, at least the
information-cell gap on some world of every repertoire cell (`ReasonDiscovery.residual_ge_cellGap'`).
Logical induction learns `𝔼ₙ(U_T) − 𝔼ₙ(U_full) ≲ₙ L·(α + β)` through the discovered
comparator (`li_noncapture_chain`).  Kept apart: authorship (closed on log authenticity by
re-execution, the registered `authorship.mediation-by-reexecution`), provenance
normalization, free amendment and trigger integrity (**OPEN**).  The full statement is the
non-capture round's
[`FINAL_THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/projects/deference/rounds/2026-09-16-noncapture-compilation/FINAL_THEOREM.md).

## 8. The walls, exactly

| wall | what it is | class |
|---|---|---|
| effect completeness | every agent-caused protected loss is a declared release | EXT |
| delegation safety; allocation completeness; the reach cone | a delegated effect never removes response authority; task moves keep `J` and only floor amendments change it; the rollout relation is the physical one | EXT (the allocation floor, item 99) |
| description faithfulness; the actuator condition | the priced sentences are about interface-supplied descriptions; every reserved resolution has an agent-independent actuator | EXT |
| the segment gate | legitimacy supplies which judgments count | EXT (legitimacy's) |
| the source rule's anchoring; the disclosure deadline; the duty covering known compromise; observation completeness; the provenance of choice | her meta-level data out of the agent's reach; what the agent observes and knows reaches the record | EXT |
| count integrity | the count, the drill schedule, the audits and her evaluation channel untampered beyond what the recognizer sees; a violation never detected charges nothing | named hypothesis, item 101's companion |
| the noise hypothesis; the conditional-expectation bound; the inquiry bidder; the allowance | the learning realizations' hypotheses | EXT (Azuma's content; the per-`K` tail derived) |
| generability of the priced events; claims as priced securities | the events and claims as sentences the market prices | OPEN, items 101 and 102 |
| unbiasedness from feedback; exploration randomness | the exploration realization's hypotheses | PAPER; EXT by content |
| the service and discovery residuals; representation adequacy; inquiry causal faithfulness; independence of inquiry and supply; vanishing void mass; promise recognizability; joinability | the deliberative half's charged residuals and boundaries | charged; EXT; OPEN (items 86, 87, 92, 93) |

## Scope warning

The headline is about an agent that maximizes the fidelity score under a declared
allocation, effect interface, authorization primitive and evaluation architecture.  It is
not a bound on a latent total utility, not a claim that any real evaluator carries
`ϖ > D` or any real interface is effect-complete, and not a theorem that an unconstrained
optimizer with a latent utility and no counted authority term has no incentive to
manipulate: a misaligned objective rewarding an uncounted manipulation is not dominated
(`AuthorityModule.misaligned_undominated`).  For systems that are not maximizers of the
fidelity score, what carries over is the target — action scored on her realized legitimate
evaluation with authority lexical in it, the allocation's machinery untouched — and, through
the decision interface, the realized rate; not the guarantee.

---

**Evidence.**  The kernel: the phase-2 round's
[`SPEC.md`](https://github.com/A-M-Berns/alignment-workspace/blob/7663cc7045a2e7d7e93b4f6199afbe0bad5b05de/projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md)
and
[`REPORT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/7663cc7045a2e7d7e93b4f6199afbe0bad5b05de/projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/REPORT.md)
with
[`Headline.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/7663cc7045a2e7d7e93b4f6199afbe0bad5b05de/lean/Workspace/Deference/Spec/Headline.lean)
and
[`KernelExtension.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/7663cc7045a2e7d7e93b4f6199afbe0bad5b05de/lean/Workspace/Deference/Contrib/KernelExtension.lean);
the phase-1 derivation and its inventory,
[`REPORT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/7663cc7045a2e7d7e93b4f6199afbe0bad5b05de/projects/deference/rounds/2026-09-26-corrigibility-kernel/REPORT.md).
The landed rounds the kernel is stated over: the protected-authority theorem
([`THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/projects/deference/rounds/2026-09-25-protected-authority-theorem/THEOREM.md)),
the authority module
([`REPORT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/08d42e2d8d0b0e77002bdadb81e46b863fee88e9/projects/deference/rounds/2026-09-25-authority-module/REPORT.md)),
the gate
([`REPORT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/a5efb833cfa52b9db8d981f4d0bb7f424b0c7301/projects/deference/rounds/2026-09-25-gate-is-legitimacy/REPORT.md)),
the decision component and the BRIA design
([`REPORT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/1604d43cb7de7414fc85ba6834c6dccd8021953e/projects/deference/rounds/2026-09-26-bria-corrigibility/REPORT.md)),
after compromise
([`REPORT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/8e59d68848f7215f2e0fccd45cade36f5b40617a/projects/deference/rounds/2026-09-26-after-compromise/REPORT.md)),
the li-corrigibility round
([`THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/projects/deference/rounds/2026-09-15-li-corrigibility/THEOREM.md))
and the corrigibilization semantics
([`CORRIGIBILIZATION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-09-mediated-repair-dominance/CORRIGIBILIZATION.md)).
The legitimacy the gate consumes is on [Legitimacy](Legitimacy); the learning layer on
[Continuation BRIA](Continuation-BRIA); the Normative Inductor's contract on
[Normative induction](Normative-Induction).  Soares et al., the CAST sequence and the
bounded-inductive-rationality paper are on [Sources](Sources).
