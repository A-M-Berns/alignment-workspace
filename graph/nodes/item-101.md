---
id: item-101
kind: leaf
leaf_kind: task
action: "Execute item 101 per its deliverable shape and acceptance check: The shortfall event as a security: generability and pricing of `Short`."
who: agent
item: "101"
title: "The shortfall event as a security: generability and pricing of `Short`"
section: "Deference line — second wave"
maintainer_order: 94
difficulty: "open"
project: deference
dispatchable: true
item_status: open
deliverable: "the `LUVCombinationSyntax` (or the pinned interface's equivalent) of the shortfall indicator over a finite consultation-and-control model, the expected shortfall as a priced security, and the decision-component exclusion stated on it; or the exact obstruction with its fixture."
acceptance: "`python3 tests/run.py` green; Lean audits clean; the round's entrenchment, storm and latency fixtures reproduced on the priced event."
work:
  - {kind: decision, ref: 2026-09-25--authority-normative-inductor-s-decision-component}
  - {kind: decision, ref: 2026-09-26--independent-source-clears-clean-overwrite-steered}
  - {kind: decision, ref: 2026-09-26--observation-completeness-named-hypothesis-every-observation}
  - {kind: decision, ref: 2026-09-26--value-influence-matter-influence-her-values}
author: "@smithy-verity"
size: L
size_reason: "one item entry of 1060 words"
version: 1
---
## Statement
A solution to item 101 ships the certificate and the priced event, or the negative with its fixture.

## Source
PRIORITIES.md, item 101 (The shortfall event as a security: generability and pricing of `Short`); its context: the round's `REPORT.md` §2 and the "Interface for the later rounds" note; `AuthorityModule.lean` §§2–3; item 90 for the generability shape; item 100 for the normativity-side instance.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The authority-module round (`projects/deference/rounds/2026-09-25-authority-module/`)
states the control surface as a finite proposition over the idle-agent rollout
(`AuthorityModule.CS`, `reachIdle`, `Short`): for an option, "the move leaves the matter
short of its requirement" is a finite disjunction over exercises of bounded length of
decidable clauses (admissibility, a cost sum, the concern at the end), so it is statable
as a sentence or a bounded logically uncertain variable once the model's transition
functions, the cost table, the window, the bound and the admissibility checker are
constants of the theory.  Nothing yet makes it a *security*: no generability certificate
for the rollout as an expressible feature, for the gate's decidable `LegitOn` as the
admissibility verdict, or for the shortfall indicator, and no pricing.  The architecture's
direction is to move the authority term from the agent's score into a constraint on the
Normative Inductor's decision component, with exclusions based on forecast shortfall —
which needs exactly this security.

*Deliverable shape:* the `LUVCombinationSyntax` (or the pinned interface's equivalent)
of the shortfall indicator over a finite consultation-and-control model, the expected
shortfall as a priced security, and the decision-component exclusion stated on it; or the
exact obstruction with its fixture.
*Acceptance check:* `python3 tests/run.py` green; Lean audits clean; the round's
entrenchment, storm and latency fixtures reproduced on the priced event.
*Context:* the round's `REPORT.md` §2 and the "Interface for the later rounds" note;
`AuthorityModule.lean` §§2–3; item 90 for the generability shape; item 100 for the
normativity-side instance.
*Consumed by:* the move of authority into the decision component; any pricing of
entrenchment.
*A solution ships:* the certificate and the priced event, or the negative with its fixture.

*2026-09-25 (decision-component round):* the consumer is now concrete — the permission
layer's ramps read `p_n(S_a)` and `p_n(T_a)` as inputs (`DecisionComponent.permWeight`),
and `eventually_excluded` takes "the price is eventually above the threshold" as its
hypothesis; generability of `S_a` and `T_a` is the named hypothesis under which
provability induction supplies it.  The taint event `T_a` (the segment through her
evaluation not `Counted`) joins the shortfall event as what this item must make a
security.

*2026-09-26 (BRIA-corrigibility round):* the events are now sentences of a declared
control model `M` in `J` about an option's declared description, so no price conditions
on the agent's own untaken action (`BRIACorrigibility.factors_through_description`); what
generability requires is `M`'s transition table, the cost table, the window and the
admissibility verdict as constants of the theory and the rollout as an expressible
feature.  **Companion filed here, not as a new item — count integrity:** the count, the
drill schedule, the audits and her evaluation channel are one integrity surface with the
priced events; tampering beyond what the recognizer sees raises the realized score
(`tamper_raises`), and the design takes their integrity as a named hypothesis.  Also
here: drill calibration (`DrillCalibrated`, `forecast_term_within`) — that with drills
at rate `q` independent of the agent's choice the shortfall and taint prices on the
chosen path are calibrated — is a named hypothesis whose derivation from the inductor's
properties needs the drilled event as a security; the incident bound in `q` and the
allowance is a conjecture.

*2026-09-26 (BRIA-corrigibility follow-up):* the drill-calibration target is reduced to
two external results the pinned library carries — affine unbiasedness from feedback
(thm:wubaff, `LogicalInduction.lic_not_frequently_positive_feedback_return`) on the
drilled-and-chosen weighting, and learning pseudorandom frequencies (thm:prand) for the
schedule — entered by content as `BRIAFollowup.UnbiasedFromFeedback` and
`DrillPseudorandom`; under them the shortfall price is unbiased on the chosen path
(`chosen_path_unbiased`) and the low-price bin's blind-spot fraction is at most
`θhi + γ` (`blind_rate_le`).  **What this item must now supply for them to fire:** the
drilled-and-chosen indicator as a `P`-generable weighting, the feedback-trader emission
for the shortfall sentences, and the deferral function under which each drill's outcome
is settled before the next block is priced.  Two more companions filed here:
**description faithfulness** (the priced sentences are about interface-supplied
descriptions, `PricedInterface`; a proposer-written description passes,
`misdescription_witness`) and **the actuator condition** as a well-formedness condition
on `J` (`WellFormed`).  The rate of unbiasedness in the drilled mass, which the incident
bound in `q` needs, is open.

*2026-09-26 (BRIA-corrigibility second follow-up):* the count-integrity boundary has a
formal face on the fruits side — a violation never detected is a record no step of which
commits it, and the design charges nothing for its fruits
(`BRIAFollowup2.never_detected_never_charged`); this is *undetected commission*, a
different residual from the untrackable fruit of a flagged commission (knowledge), and it
is exactly what the count, the drill schedule and the audits this item's companion names
must turn into a flagged step.  Detection at `k₁` after commission at `k₀` recomputes the
taint from commission and charges the window by late debit (`detectAt`,
`window_block_charged`, `collected_iff`).

*2026-09-26 (after-compromise round):* count integrity now also covers **the provenance
of why an act was chosen**.  Under clean overwrite an independent source clears a
component's taint while a derivation steered by the tainted memory keeps it
(`AfterCompromise.clean_overwrite`, `taint_propagates3`); the distinction is whether the
act's *choice* read the memory, which the tracking sees only if the declared reads
include it — an integrity fact about the interface, not a legitimacy fact.  Also here:
the twin market's redaction on refusal over reserved knowledge (`TwinMarket`) and its
leakage residual (`leakage`), and the extension of the disclosure duty to *known*
third-party compromise (`missedKnownDisclosure`) — what the agent knows is this item's
companion again.

*2026-10-01 (thin-legitimacy round, as corrected by its follow-up):* **what is done** — the
shortfall of an option is an *atom* reserved per option description (`ShortfallSecurity.shortAtom`),
the model's rollout reaches the market through the deductive process at a declared stage
(`shortfallProcess short defer`, the stagewise union with a base theory), the atom family over
an efficiently generated family of options is emitted (`shortAtom_codes`), and provability
induction prices a shortfall the process eventually proves to one ahead of deduction
(`deferred_ahead`), discharging `DecisionComponent.eventually_excluded`
(`deferred_eventually_excluded`); the pre-decided table's generability (`shortLUV_codes`) is
registered as what it is (`shortfall.table-generable`).  **What is not done** — the process's
computation (`DeductiveProcessComputation` for `shortfallProcess` is not built, and the inductor
over the union is a hypothesis); the table's entries against a Lean instance of the module's
physics beyond the entrenchment fixture (`EffectiveAuthority.Dep.entrenchment_table_agrees`);
drill calibration (the drilled-and-chosen weighting as `P`-generable), the feedback trader's
emission for the shortfall atoms, the deferral function's relation to the drill schedule, and
the taint event `T_a` as a security.  This prices the uncontrasted shortfall inside a declared
model; caused shortfall is a count-side object, and learned membership (M4) is a different
event (`EffectiveAuthority.asks_iff_line`).
