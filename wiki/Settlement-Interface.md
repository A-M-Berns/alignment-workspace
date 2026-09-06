# Settlement interface

**Status: canonical.** Six distinct conditions, each with one home. Four are typed
inputs of the protocol; two are consequences or clauses of theorems elsewhere. There
is no single "settlement integrity" hypothesis.

Everything in [Legitimacy](Legitimacy) is a statement about a *history*. This page
fixes what that history is, which part of it counts as settled, and why the two must
never be identified.

## The full history and its settlement view

A cognitive trajectory leaves a **full normative history**: an append-only record of
authenticated events — admissions of obligations with their anchored specifications,
grounds cited and answers given, objections, standing and licence changes, defeats
and dispositions with their successors, semantic migrations, service events,
compiler receipts, and receipts arriving through the settlement interface. Most of
these are *internal* moves. A participant made them and a participant can contest
them.

The **settlement view** is a distinguished projection: which externally supplied
items are available at a prefix. An item belongs to no participant — nobody opened
it, nobody can answer it away — which is what makes it usable as a ground no
coalition controls and as the basis of a terminal discharge.

If everything a process wrote counted as settled, it could settle its own debts by
writing them settled. If nothing counted as settled, no obligation could ever
terminally close.

## Six conditions, six homes

| condition | home | form |
|---|---|---|
| **interface authenticity** — an item marked available really arrived through the boundary | external input | the protocol's availability predicate is assumed to mean this |
| **source trustworthiness** — the item is true or reliable | external input, separate | nothing in the theory consumes an item's truth |
| **historical receipt immutability** — a discharge certified at a prefix stays certified | Integrity, a theorem | a closure receipt stores availability at its own prefix and survives every later transition |
| **the internal closure judgment** — under the warrant in force at that prefix, this item suffices to close this requirement | Integrity, stored | a field of the closure receipt; never recomputed |
| **authority to use the closure** | Integrity, stored | the receipt's warrant, in force at its prefix |
| **counterfactual resistance to suppression or delay** | Robust Openness, only where the application routes a concern through settlement access | a route's adequacy under the declared interventions |

Availability does not establish the closure judgment, and the judgment does not
establish the item's truth. A discharge requires all three of availability, judgment
and authority, stored together.

## Closure is not answer

A valid closure yields a **resolution witness** — evidence that the anchored
requirement has been legitimately accounted for — and the fate recorded is
`closed`. An adequate answer yields a resolution witness too, with fate `answered`.
The theory never converts one into the other. A settlement-backed discharge of a
question is not an answer to it, and the account says which happened.

## Reconsideration is an appended event

A later trajectory may reject the rationale of an earlier closure. It does not
rewrite it: the closure receipt, its settlement item and its judgment stay in the
account of the occurrence they closed. What the trajectory may do is admit a **fresh
occurrence** anchored at the reconsideration, which then has its own three fates.
Whether a successful challenge *must* create such an occurrence is licence content of
the practice, supplied through warrants and not derived here.

## Three uses of settlement in the realization

The [Normative Inductor](Normative-Inductor) uses one history and three distinct
settlement functions: certified reports translated into sentences the assessment
process settles; settlement items as citable grounds for a disposal, whose relevance
stays a history question; and closure receipts that terminally discharge an anchored
obligation, which no participant's challenge, verdict or quote can manufacture.

---

**Evidence.** The protocol's settlement fields, the closure receipt and its
immutability under substitution are
[`OccurrenceIntegrity.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/lean/Workspace/Normativity/Contrib/OccurrenceIntegrity.lean),
registered as `legitimacy.receipts-immutable`; the six-way separation is §3 of the
consolidation round's
[`CONSOLIDATION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md).
The attacks that forced the item/judgment distinction — genuine settlement with
unrelated closure, rule revision and reinterpretation flipping a historical closure —
are the integrity adversary round's
[`ATTACKS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/projects/normativity/legitimacy/rounds/2026-09-05-integrity-adversary/ATTACKS.md).
The structural settlement specification that preceded this account is the
normative-continuity settlement round's
[`SETTLEMENT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/198a86ae3e8a45737c3229e95718fa5882d06216/projects/normativity/legitimacy/rounds/2026-08-30-normative-continuity-settlement/SETTLEMENT.md).
