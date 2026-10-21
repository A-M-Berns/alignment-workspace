---
id: dependent-type-of-procedure
kind: leaf
leaf_kind: task
action: "Check whether the v2 definition of a decision procedure fixes the dependent typing flagged in the May 2026 plan, and file the repair as a proposed edit if it does not."
who: agent
files: [projects/decision-theory/decision-problems-note-dump-2026-10-01/decision-problems-v2.md]
author: "@smithy-verity"
size: S
size_reason: "one sentence and one definition"
version: 1
---
## Statement
The formal core's definition of a decision procedure carries the dependent
typing the maintainer flagged, the second action type depending on the first.

## Source
projects/deference/faf-cleanroom-2026-10-02/sources/unbounded-embedded/01-primary/summer-research-plan-2026--research-ideas-may-2026.md,
section What is a decision problem?: "I gave the type of a decision procedure
as $(S,A) \to A$. The two $A$s are not really the same … (This should have been
formalized with a dependent type.)"
projects/decision-theory/decision-problems-note-dump-2026-10-01/decision-problems-v2.md,
section 3 (the definition to check).

## Notes
One of the maintainer's own listed repairs; the given parent of the
Lean-checked core's bridge, since the typing is where draft and Lean could
differ.
