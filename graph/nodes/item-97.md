---
id: item-97
kind: leaf
leaf_kind: task
action: "Execute item 97 per its deliverable shape and acceptance check: Declare each channel's reference in the evaluation ecosystem, and certify its realization."
who: agent
item: "97"
title: "Declare each channel's reference in the evaluation ecosystem, and certify its realization"
section: "Deference line — second wave"
maintainer_order: 90
difficulty: "substantial"
project: deference
dispatchable: true
item_status: open
deliverable: "the three declarations as readings of the log, the Lean witnesses, and the mechanized three-link chain; or the exact channel whose reference the ecosystem cannot declare, with the fixture."
acceptance: "`python3 tests/run.py` green; Lean audits clean; the round's `SelectionSealing` and `Priority68` fixtures reproduced against the declared `x`."
work:
  - {kind: decision, ref: 2026-09-24--evaluation-ecosystem-declared-input-view-advisor}
author: "@smithy-verity"
size: L
size_reason: "one item entry of 659 words"
version: 1
---
## Statement
A solution to item 97 ships the declarations with their witnesses, or the negative with its channel.

## Source
PRIORITIES.md, item 97 (Declare each channel's reference in the evaluation ecosystem, and certify its realization); its context: `REPORT.md` §§4, 7, 8 of the round; `TransparentChannel.lean`; item 87's residual paragraph (clause 6); item 89's 2026-09-15 note; item 68's acceptance check.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The transparent-channel round (`projects/deference/rounds/2026-09-24-transparent-channel/`)
states one primitive behind item 87 clause 6, item 89, item 68 and the causal-contract wall:
a channel of the frame realizes a publicly declared reference on its declared inputs
(`TransparentChannel.Realizes`), with the reason-mediated payload as the downstream half
(`reasonMediated_of_reexecution`).  The theorems are algebra; what does not exist is the
declaration.  For the evaluation ecosystem of `EvaluationEcosystem.lean`: (a) the
declared-input view `x` as a reading of the log — the round uses the non-advisor
pre-commitment events, under which the `leak` advisor is a transparency failure and
`view_prog` in the market world is a non-blind `x`; (b) the reference `κ` of the reason
channel (the registrar's routing composed with the supplier's docket), of the activation
channel (the answering process, candidate-blind by sequencing or isolation) and of the
specification channel (an amendment event kind for the mandate); (c) `Realizes` witnesses
for the ecosystem frame in the shape of `Instance.mediation_witness`, and the failure
witnesses for `leak` and for a secret evaluator change; (d) the third link of the
non-capture chain, actual supplier to reference supplier, as `li_noncapture` applied a
third time, with the mismatch branch fed by `expect_mismatch_le_defects` through
`li_gated_le` in place of the Boolean `hsealed`.

*Deliverable shape:* the three declarations as readings of the log, the Lean witnesses, and
the mechanized three-link chain; or the exact channel whose reference the ecosystem cannot
declare, with the fixture.
*Acceptance check:* `python3 tests/run.py` green; Lean audits clean; the round's
`SelectionSealing` and `Priority68` fixtures reproduced against the declared `x`.
*Context:* `REPORT.md` §§4, 7, 8 of the round; `TransparentChannel.lean`; item 87's residual
paragraph (clause 6); item 89's 2026-09-15 note; item 68's acceptance check.
*Consumed by:* items 68, 72, 87 (clause 6), 89; any canonicalization of "transparent
mediation" as a contract (queued in `DECISIONS.md`).
*A solution ships:* the declarations with their witnesses, or the negative with its channel.

*2026-09-24 (second pass of the round, `ECOSYSTEM_REALIZATION.md`).*  Delivered: (a) the view
as a reading of the log (`TransparentEcosystem.view`, the non-advisor pre-commitment events;
over-rich and under-rich ends witnessed); (b) the activation reference for every log
(`payload_take`, `realizes_activation`: activation is a reading of the prefix through the
commit, so sealed comparison is the shared-prefix condition, `mismatch_zero_sequenced`, and
same-branch attains the mismatch), the reason reference (`κR`, `realizes_reason`: admitted
view plus the advisor's declared program on the view, realized iff the advisor's contribution
is that program's output) and the specification reference (`realizes_spec`, depth zero); (c)
the witnesses; (d) the three-link chain (`TransparentChain.li_noncapture_chain3`, with `tauR`
as the first link's quantity).  What remains of this item: an **advisor-mandate event kind**
binding the advisor's program in the log, so that `realizes_reason`'s hypothesis is a
re-execution check as clause 2's is (the second pass carries the declaration as public frame
data); an **amendment event kind** for the mandate, so the specification tower has depth
above zero; the Logical-Induction transfer of the activation defect indicators (a compiled
`G_M ≤ G_τ` with its generability certificate); and the declared inquiry policy under which
the engine-ownership clauses of independence become `Realizes` hypotheses.

*2026-09-24 (protected-authority round):* a fourth channel.  The response `r` as a function
of the dossier and the operative evaluator has no declared reference; its defect
`τ_resp = P(r ≠ argmax)` bounds the execution divergence `E[ξ_d] ≤ D·τ_resp`
(`ProtectedAuthority.expect_execDiv_le`), and manufactured divergence is charged nowhere
else.  Filed as item 98.

*2026-09-25 (protected-authority-theorem round):* the declared amendment effects
`IsAmend` of the allocation theorem are the amendment event kind the specification tower
needs; a reallocation is authorized only through their gated release, not through
ordinary approval (`ReallocAt`, `authPolicy_no_realloc`).

*2026-09-25 (legitimacy-internal-external round):* transparency covers every channel of
influence on the principal's cognition, including the **consultation protocol** — how and
when she is asked — and disclosed actions in the world; which influence is admissible is the
declared reference's to decide.  The reason channel's declared scope is therefore where
asking-at-a-chosen-moment, framing and dark patterns are charged; no separate response
channel exists (item 98).  The amendment event kind is what hypothesis (L) of item 98 and
the specification tower both need.
