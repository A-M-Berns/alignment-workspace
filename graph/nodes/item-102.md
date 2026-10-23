---
id: item-102
kind: leaf
leaf_kind: task
action: "Execute item 102 per its deliverable shape and acceptance check: BRIA's bids against the market: block claims as priced securities."
who: agent
item: "102"
title: "BRIA's bids against the market: block claims as priced securities"
section: "Deference line — second wave"
maintainer_order: 95
difficulty: "open"
project: deference
dispatchable: true
item_status: open
deliverable: "the claim-as-security interface with its generability certificate, the feasibility restatement, and the settlement rule; or the exact obstruction with its fixture."
acceptance: "`python3 tests/run.py` green; Lean audits clean; the continuation-BRIA round's auction fixtures reproduced on priced claims."
work:
  - {kind: decision, ref: 2026-09-25--authority-normative-inductor-s-decision-component}
  - {kind: decision, ref: 2026-09-27--decision-theory-logical-inductors-without-belief}
author: "@smithy-verity"
size: L
size_reason: "one item entry of 671 words"
version: 1
---
## Statement
A solution to item 102 ships the interface with its certificate, or the negative.

## Source
PRIORITIES.md, item 102 (BRIA's bids against the market: block claims as priced securities); its context: the round's `REPORT.md` Part D; `ContinuationBRIA.lean` `Auction`; `DecisionComponent.lean` §4; items 86, 90, 101.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The decision-component round (`projects/deference/rounds/2026-09-25-decision-component/`)
restricts Continuation BRIA's menu to the composed gate's support and bounds ramp-region
exposure along a continuation with a cumulative budget, but leaves the coupling between
BRIA's bids and the market unsolved: nothing checks a block claim against prices, and
nothing prices one.  What is needed: block claims (promised returns over a lease) as
sentences or bounded logically uncertain variables of the inductor's theory, so that a bid
is a priced security the market can check; the auction's feasibility (`Auction.Feasible`,
wealth against bids) restated against prices; and a claim's settlement at a test as an
assessed world of the assessment process.  The continuation-BRIA page's open bullet on
the LI coupling is this item.

*Deliverable shape:* the claim-as-security interface with its generability certificate,
the feasibility restatement, and the settlement rule; or the exact obstruction with its
fixture.
*Acceptance check:* `python3 tests/run.py` green; Lean audits clean; the continuation-BRIA
round's auction fixtures reproduced on priced claims.
*Context:* the round's `REPORT.md` Part D; `ContinuationBRIA.lean` `Auction`;
`DecisionComponent.lean` §4; items 86, 90, 101.
*Consumed by:* the competence layer of the decision component; item 86.
*A solution ships:* the interface with its certificate, or the negative.

*2026-09-26 (BRIA-corrigibility round):* a partial answer.  The evaluation decomposes
as `bid − ϖ·n_known − ϖ·(p(S) + p(T))` (`BRIACorrigibility.evalOf`): the forecast part of
a claim is already the market's — the prices — and what the hypothesis bids on is the
*residual*, ordinary value plus violations recognizable only after the fact; settlement
adds back the prices (`settlement_ii_consistent`).  What remains of this item is the
residual as a security: the bid on it checked against prices, feasibility stated
against them, and its settlement at a test as an assessed world.  The block-`0`
feasibility of the default bidder after the rescaling is a condition on the allowance
schedule (`default_affordable`), which any pricing restatement must carry.

*2026-09-26 (BRIA-corrigibility follow-up):* corrected — the block-`0` allowance suffices
under bounded block weights (`BRIAFollowup.default_affordable_block0`), and with unbounded
weights the minimal schedule tracks the running maximum of the weights
(`default_affordable_of_schedule`); the incident-rate statement any pricing restatement
must carry is the signed bound under competitiveness (`incidents_le_signed`,
`Competitive`) with an `o(K)` allowance, the landed prefix rule's `O(√K log K)` — a
linear allowance gives a constant rate.  Settlement under delay now has its algebra
(`DAuction`, `cash_nonneg`, `delayed_overestimation`): bids feasible against cash net of
escrow; a claim-as-security restatement must state feasibility against prices net of the
same escrow.

*2026-09-26 (BRIA-corrigibility second follow-up):* competitiveness is no longer the
primitive hypothesis a pricing restatement must carry — one honest tracker in the class,
fed by the allowance at the rate of its honesty error, gives it with margin
`Σ_{k<K} w_k ε_k` (`BRIAFollowup2.competitive_of_affordable_tracker`,
`rate_le_of_honest_tracker`), under the auction rule that the winner's bid is the highest
feasible bid on the winning continuation (`HighestFeasible`) and with the tracker's
minimal allowance `w̄ · D` at entry plus `w_j ε_j` per block (`trackerAllowance`).  What a
restatement against prices must carry is (i) that rule stated on priced claims and (ii)
whether the arrangement's uniform per-hypothesis allowance stream — the landed prefix
rule's, over a countable class — dominates `Σ_{j<k} w_j ε_j` for the honest hypothesis,
which is a condition on `ε` against the rule and is not derived here.  The escrow
comparison among evaluation-timing options is settled in expectation
(`expected_escrow_eq`): what a priced restatement carries is the variance, not the mean.

*2026-09-27 (kernel phase 2, R7):* **re-scoped to the Continuation BRIA realization
only.**  The kernel's headline is stated for a plain maximizer of the fidelity score and
consumes no auction; the decision interface of the extension
(`Contrib.KernelExtension.DecisionInterface`) is what any learner must meet, and BRIA
meets it with no exploration and `B(K) = ρ 𝒜_K` (`bria_rate`).  What this item still asks
— block claims as priced securities, feasibility against prices, settlement at a test as
an assessed world — is a problem of that realization: it sharpens `B(K)` and the
competence of the BRIA chooser, and nothing in the headline or the interface theorem waits
on it.  The learner-level question it was standing in for is item 103.
