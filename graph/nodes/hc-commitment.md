---
id: hc-commitment
kind: leaf
leaf_kind: question
action: "Add the faithful-state clause, divergence in state true and nonnegative weight to HcCommitment, then attempt an inhabitant of HcRealized with normalised tables or show it unsatisfiable."
who: agent
files: [projects/deference/faf-cleanroom-2026-10-02/packages/corr-exo-trader]
author: "@smithy-verity"
size: M
size_reason: one flagged definition and one repair
version: 1
---
## Statement
An updateless commitment over Bayesian-logical-induction belief states that
stops in states whose implemented beliefs say continue, when the button
correlates with divergence between implemented and algorithmic beliefs, is
satisfiable with normalised tables.

## Source
The BLI thread's Choice 3 as its public audit records it
(projects/deference/corrigibility-note-dump-2026-10-01/corrigibility-bli-thread-and-early-questions-audit.md,
item 1.4: UDT over BLI commits to stop in states whose implemented beliefs say
continue, when the button correlates with implemented/algorithmic divergence);
projects/deference/faf-cleanroom-2026-10-02/packages/corr-exo-trader, the
flagged definition HcCommitment (projects/deference/faf-cleanroom-2026-10-02/DIGEST.md,
line 151: "it encodes a label where it promises a mechanism") and HcRealized.

## Notes
Flagged by the clean-room; the repair (the faithful-state clause, divergence in
state, nonnegative weight) is the action. Shares its object with the
updateless-dt branch (a UDT-over-BLI construction).
