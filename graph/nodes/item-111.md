---
id: item-111
kind: leaf
leaf_kind: task
action: "Execute item 111 per its deliverable shape and acceptance check: Unbiasedness From Feedback for the score sequence, from `LogicalInduction`."
who: agent
item: "111"
title: "Unbiasedness From Feedback for the score sequence, from `LogicalInduction`"
section: "Deference line — second wave"
maintainer_order: 104
difficulty: "open"
project: deference
dispatchable: true
item_status: open
deliverable: "a Lean declaration in a contribution namespace whose conclusion is `Sequential.UnbiasedFromFeedback Q` for a `Sequential` built from an inductor's expectations, with the two assumptions as hypotheses and a witness inhabiting them; then `Sequential.theorem3a`, `theorem3a_rate`, `theorem3b` and the Corollary composed with it, registered `lean-proved`."
acceptance: "`lake build` and the axiom audit green; `python3 -m checkers.run` green on the registrations."
context: ["wiki/Deconfusing-Corrigibility-Companion.md"]
author: "@smithy-verity"
size: L
size_reason: "one item entry of 345 words"
version: 1
---
## Statement
A solution to item 111 ships the derivation, or the obstruction — in particular whether the support clause (PE2) can be discharged for the score family.

## Source
PRIORITIES.md, item 111 (Unbiasedness From Feedback for the score sequence, from `LogicalInduction`); its context: the round's `REPORT.md` and the wiki page `wiki/Deconfusing-Corrigibility-Companion.md`; the existing weighted predicate `BRIAFollowup.UnbiasedFromFeedback` and its consumer `KernelExtension.exploration_rate`, which take the same fact by content for the kernel's decision interface.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The companion formalization of "Deconfusing Corrigibility"
(`lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`,
`prompts/2026-10-17-post-companion-formalization/`) takes Unbiasedness From Feedback as a
named hypothesis on the estimate and score sequences —
`Sequential.UnbiasedFromFeedback`: `∀ γ > 0, ∃ N₀, ∀ K ≥ N₀, (1/K) Σ_{k<K} (U_k a_k − S_k) ≤ γ`
— and derives Theorem 3 and the Corollary from it.  Wanted: that hypothesis as a theorem
of `LogicalInduction`, for an agent whose estimates `U_k` are a logical inductor's
expectations of the score and whose realized scores enter the deductive process.  The
source is Theorem 4.8.16 of the Logical Induction paper, pinned as `thm:wubexp` /
`LogicalInduction.lic_not_frequently_positive_feedback_return`
(`projects/deference/faf-cleanroom-2026-10-02/packages/def-lattice/def-lattice-report.md`,
row 4.8.16, with the support clause its proof uses recorded there as PE2), instantiated
with the uniform weighting `w_k = 1`.  Two assumptions the post leaves implicit must be
explicit hypotheses of the statement: that each realized score `S_k` enters the deductive
process (the feedback-enters-the-deductive-process assumption, in the form the pinned
theorem's `FeedbackTruthComputation` certificate takes), and the latency with which it
does (the deferral function under which each score is settled before the next estimate
is priced).  The one-sided form above is the half of the weighted-unbiasedness
conclusion that the theorems consume; the theorem may deliver the absolute-value form.

*Deliverable shape:* a Lean declaration in a contribution namespace whose conclusion is
`Sequential.UnbiasedFromFeedback Q` for a `Sequential` built from an inductor's
expectations, with the two assumptions as hypotheses and a witness inhabiting them; then
`Sequential.theorem3a`, `theorem3a_rate`, `theorem3b` and the Corollary composed with it,
registered `lean-proved`.
*Acceptance check:* `lake build` and the axiom audit green; `python3 -m checkers.run`
green on the registrations.
*Context:* the round's `REPORT.md` and the wiki page
`wiki/Deconfusing-Corrigibility-Companion.md`; the existing weighted predicate
`BRIAFollowup.UnbiasedFromFeedback` and its consumer `KernelExtension.exploration_rate`,
which take the same fact by content for the kernel's decision interface.
*Consumed by:* the post's "Learning with logical induction" section, which currently
rests on the hypothesis; any round deriving the exploration bound `U_k a_k ≥ −δ − λ θ`
from linearity of the inductor's expectation.
*A solution ships:* the derivation, or the obstruction — in particular whether the
support clause (PE2) can be discharged for the score family.
