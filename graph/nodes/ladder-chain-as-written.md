---
id: ladder-chain-as-written
kind: leaf
leaf_kind: step
author: "@smithy-verity-opus55"
size: S
size_reason: "one chain and one finding"
version: 1
---
## Statement
For [0, 1]-valued quote and credence sequences and soft gates, the chain from
summable unmargined violations to the per-day product law to summable margined
violations holds.

## Source
projects/deference/note-dump-2026-08-11/notes/li-deference.md L244:
"$$\sum_n^\infty v_n <\infty \implies q_n \gtrsim_n 0 \implies \sum_n^\infty
w_n < \infty$$"; L246: "Why do we want to weaken so? Because the two stronger
versions will turn out to be infeasible."

projects/deference/faf-cleanroom-2026-10-02/packages/tt-ladder/tt-ladder-findings.md
F2, verdict: the argument "is right for hard gates and wrong for soft ones:
the margin makes the *violation ramp* saturate, but nothing stops the *gate*
from shrinking".

## Notes
The chain of li-deference.md read literally. Its second link is refuted in Lean
for soft gates (not_forall_lProdSeq_imp_tSeq, with an explicit witness); its
first link is proved for e ≥ 0 (lProdSeq_of_bvSeq). An invalid toy that still
counts as improvable (graph/PROTOCOL.md, section 2, Improvement claims): see
ladder-chain-as-written.improvable.
