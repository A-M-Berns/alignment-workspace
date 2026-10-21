---
id: faithful-updatelessness
kind: leaf
leaf_kind: step
given: draw-as-act-coordinate
action: "Prove the general-k normalized affine locus by the Bernstein-basis comparison hand-derived in the dp-faithful-udt docstring, and strict_bestReply_open."
who: agent
files: [Cleanroom/Decision/DpFaithfulUdt/]
work:
  - {kind: open, ref: kfold_faithful_iff_affine_normalized_open}
author: "@smithy-verity"
size: M
size_reason: "one open question and one package report"
version: 1
---
## Statement
For the prior states and policy interpretations the formal core's Q10 asks
about, the UDT and the conditional-UDT procedures earn the optimality
endorsement on a decision problem exactly on the normalized affine locus, for
every point count.

## Source
projects/decision-theory/decision-problems-note-dump-2026-10-01/decision-problems-v2.md,
section 10, Q10;
projects/deference/faf-cleanroom-2026-10-02/packages/dp-faithful-udt/dp-faithful-udt-report.md:
the affine-coupling conjecture refuted as stated
(kfold_faithful_iff_affine_refuted), repaired with normalization and proved at
k = 2 (kfold2_norm_faithful_both_iff_affine), the general case OPEN
(kfold_faithful_iff_affine_normalized_open), with strict_bestReply_open among
five OPEN statements.
