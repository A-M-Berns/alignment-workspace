---
id: compiler.deductive-end-to-end.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 2
author: "@smithy-verity"
---
## Statement
The claim asserts that a constraint on prices compiles to a legal trading strategy inside the market recursion, giving per-date conformance within a schedule while preserving the logical induction criterion. The declaration certifies this for a deductive process: the market compiled from the deductive projection schedule is a logical inductor over the process, and at every date its distance from the day's representation on the fragment is within that date's tolerance. The gaps: the claim speaks of constraints on prices in general, and the declaration of the deductive region alone (the constraint-schedule forms are the companion declarations end_to_end_effective and end_to_end_of_constraints_effective, which this record does not certify); the claim leaves the schedules free, and the declaration fixes the fragment and tolerance schedules as primitive recursive data; preserving the criterion means the pinned source's own IsLogicalInductor over the deductive process, under the source's certificate, not an absolute criterion; and the construction is computable, not efficient, the generator being doubly exponential in the fragment dimension, which the claim does not say.

## Source
projects/normativity/CLAIMS.md, entry `compiler.deductive-end-to-end` (class lean-proved, status active, origin round 2026-08-18-projection-enforcement; answers item 48).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md (the paragraph stating the declaration as kernel-supported and its companions); context: projects/normativity/rounds/2026-08-18-projection-enforcement/FINAL_FORMALIZATION_STATUS.md.
The file header of lean/Workspace/Normativity/Contrib/DeductiveEffective.lean (what the compiler needed and did not need of the process), read by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice).
