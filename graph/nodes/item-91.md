---
id: item-91
kind: leaf
leaf_kind: question
action: "Work PRIORITIES item 91: define the oracle-relativized inductor and check that its parts are computable relative to the stream."
who: agent
item: "91"
title: "Empirical settlement of activated securities: an oracle-relativized inductor"
section: "Deference line — second wave"
maintainer_order: 87
difficulty: "open"
project: deference
dispatchable: true
item_status: open
deliverable: "a paper-level theorem with its exact hypotheses and a witness that a real log's securities are determined relative to the stream; Lean where the pinned formalization's relativization admits it."
acceptance: "`python3 tests/run.py` green; Lean audits clean."
work:
  - {kind: decision, ref: 2026-09-15--corrigibility-nucleus-landed-item-90-split}
author: "@smithy-verity-opus55"
size: M
size_reason: "one open work order"
version: 1
---
## Statement
Logical induction relativized to an observation stream has its inductor,
traders and deductive process computable relative to the stream.

## Source
PRIORITIES.md: "Empirical settlement of activated securities: an
oracle-relativized inductor"

## Notes
How the logical-induction level meets real logs: computable relative to a
non-computable stream, between levels (AI reading). PRIORITIES #91, open.

## Item
The li-corrigibility round states its feedback extension by `thm:wubexp` for
comparisons *determined via `Γ`* — the sequenced-settlement pair with a finite horizon in
a closed finite model (`FEEDBACK_BOUNDARY.md`).  The paper's deductive process is
computable (`def:dedproc`); a trace of physical observations is not computable from the
day, so an activated security read off a real log is outside the framework as stated.
State and prove the oracle-relativized form: an inductor, traders and a deductive
process computable relative to an observation stream, with `thm:expprovind` and
`thm:wubexp` relative to the stream, and "determined via `Γ`" read as determined by `Γ`
plus the observed prefix; then show that a real log's activated securities, with an
explicit finite horizon on the occurrence, are determined relative to the stream.  This
is an extension of the feedback boundary, not a hypothesis of T1–T3′.

*Deliverable shape:* a paper-level theorem with its exact hypotheses and a witness that
a real log's securities are determined relative to the stream; Lean where the pinned
formalization's relativization admits it.
*Acceptance check:* `python3 tests/run.py` green; Lean audits clean.

*Context:* `FEEDBACK_BOUNDARY.md` §4 of the round; item 87 (availability) for what the
securities are; item 90 for the certificate side.
*Consumed by:* T4 of the round, whose "determined via `Γ`" hypothesis this item realizes
for empirical logs.
*A solution ships:* the relativized theorem, or the negative with its witness.
