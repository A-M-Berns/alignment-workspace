---
id: item-105
kind: leaf
leaf_kind: step
action: "Register W1 as a theorem of record with exact hypotheses and its witness, the paper's auction over a logical inductor on a finite environment, then try the belief-disagreement environment A1 as a countermodel to the strong compatibility form."
who: agent
files: [projects/decision-theory/rounds/2026-09-29-li-bria-synthesis-spec, lean/Workspace/]
item: "105"
title: "Belief–decision compatibility: W1 as a theorem of record, and the unresolved implication"
section: "Deference line — second wave"
maintainer_order: 98
difficulty: "substantial"
project: decision-theory
dispatchable: true
item_status: open
deliverable: "paper-level theorems with named hypotheses and witnesses; Lean for the algebraic core where the pinned formalization admits it; or the countermodel with its fixture."
acceptance: "`python3 tests/run.py` green; Lean audits clean if any."
context: ["projects/decision-theory/rounds/2026-09-29-li-bria-synthesis-spec/tests/test_cm.py"]
author: "@smithy-verity"
size: L
size_reason: "one PRIORITIES item and a round section"
version: 1
---
## Statement
W1 holds as a statement of record with exact hypotheses and a witness, and the
implication from M2(c) and M3 to the strong compatibility form is proved under
added hypotheses or refuted by a countermodel.

## Source
PRIORITIES.md, item 105 (belief–decision compatibility: W1 as a theorem of
record, and the unresolved implication);
projects/decision-theory/rounds/2026-09-29-li-bria-synthesis-spec/REPORT.md,
section 7.

## Notes
The line's first registered theorem would be W1; the belief-disagreement
environment A1 is the obvious countermodel attempt for the strong form.

## Item
`projects/decision-theory/rounds/2026-09-29-li-bria-synthesis-spec/PROBLEM_STATEMENT.md` §5 states the compatibility relation in two forms.  The
**established** form W1: under LI recovery relative to the observation stream (M2(c),
item 91), a post-selection forecast `F⁺_k` of the selected option's realized score
published as a market state after the selection is in the stream, and settlement within
a computable deferral, `limsup (1/K) Σ_{k≤K} (e_k − F⁺_k) ≤ 0` — from no overestimation
and `thm:wubaff` on the trivial weighting.  The **strong** form: the same on every
`P`-generable weighting.  The first pass's derivation of the strong form from M2(c) and
M3 is invalid (the subsequence gap; the cumulative-loss gap, repaired by `ε`-shifted
bidders; the access gap — a weighting must be computable at forecast time, so a
selection-based weighting serves post-selection forecasts and serves pre-selection
forecasts only where the selection is predictable from the market state, and publicity
of the selection does not make an internal test set recognizable; the semantic gap — a
forecast for an unselected option settles against nothing), and **no countermodel to
the implication exists**: its status is unresolved.  Two deliverables.  (i) W1 as a
statement of record with its hypotheses exact and its witness (the paper's auction over
a logical inductor on a finite environment).  (ii) The implication settled: a proof
under added hypotheses (weighted no-overestimation; a sound market-reading bidder for
the selected option on a recognizable test set), or a countermodel — the
belief-disagreement environment A1 of §7 is the candidate for one.

*Deliverable shape:* paper-level theorems with named hypotheses and witnesses; Lean for
the algebraic core where the pinned formalization admits it; or the countermodel with
its fixture.
*Acceptance check:* `python3 tests/run.py` green; Lean audits clean if any.
*Context:* the round's `PROBLEM_STATEMENT.md` §3, §5, §7 (A1); `TEST_SUITE.md` T11; the
cross-subsidy and heads-tracker fixtures in `projects/decision-theory/rounds/2026-09-29-li-bria-synthesis-spec/tests/test_cm.py`; items 91, 102.
*Consumed by:* item 106; item 102 (a bid checked against prices is the strong form's
lower half stated on priced claims).
*A solution ships:* W1 of record and the implication's status, either way.
