---
id: uea-updateless-variant
kind: leaf
leaf_kind: route
given: uea-theorem-1
action: "Reconcile notes/01-interleaving-sketch.md with sink-or-swim findings F-6 to F-9 and state which updateless optimality notion the repaired theorem of the updateless self-game uses."
who: agent
files: [projects/deference/faf-cleanroom-2026-10-02/sources/unbounded-embedded/unbounded-embedded-lab/notes/01-interleaving-sketch.md, projects/deference/faf-cleanroom-2026-10-02/packages/uea-sink-swim/uea-sink-swim-findings.md]
author: "@smithy-verity-opus55"
size: M
size_reason: "a sketch reconciled against four findings"
version: 1
---
## Statement
An updateless variant of Theorem 1, with Cole Wyeth's optimality notion
replaced by an updateless one, holds for an updateless agent in the finite
shadow and in rOSI.

## Source
projects/deference/faf-cleanroom-2026-10-02/sources/unbounded-embedded/01-primary/summer-research-plan-2026--research-ideas-may-2026.md:
"If the formalism were switched to a variant of reflective oracles which
allowed correlation, then the definition of optimality might no longer rule
out Omega predicting you. If the definition of optimality were fixed in some
other way, then the reflective oracles in themselves might not be causing any
problems."

projects/deference/faf-cleanroom-2026-10-02/packages/uea-sink-swim/uea-sink-swim-findings.md:
"the answer to the sketch's round-2 target 2 is "it does nothing""

projects/deference/faf-cleanroom-2026-10-02/sources/unbounded-embedded/unbounded-embedded-lab/notes/01-interleaving-sketch.md.

## Notes
A route of uea-theorem-1.improvable. The clean room's sink-or-swim findings
F-6 to F-9 formalize round 2's content: opaque Newcomb is ill-posed at the
model level, the argmax threshold is 1000/1999, the policy-level floor has a
self-trap, and the current-node floor with the updateless yardstick is inert.
The updateless self-game's repaired theorem (udt-trust-repaired) is the clean
room's updateless version of the theorem. Linked to the updateless-dt branch.
