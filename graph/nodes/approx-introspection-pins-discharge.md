---
id: approx-introspection-pins-discharge
kind: leaf
leaf_kind: question
action: "Discharge the gap packages and the expert pins (ExpertPinsGaps) at grade (a) for a distinct inductor expert, not only for the self-expert, in the def-lattice-arrows and def-squeeze-diamond neighbourhood."
who: agent
files: [projects/deference/faf-cleanroom-2026-10-02/packages/def-squeeze-diamond/, projects/deference/faf-cleanroom-2026-10-02/packages/def-lattice-arrows/]
author: "@smithy-verity"
size: L
size_reason: "a Lean discharge over two packages"
version: 1
---
## Statement
The gap packages and the expert pins the bounds-transfer repair assumes are
discharged at grade (a) for a distinct inductor expert.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/def-squeeze-diamond/def-squeeze-diamond-report.md,
section 3b (the identification of the repair with
tower_instance_of_totalTrust_gapBets, with the pins as Step 0) and
def-squeeze-diamond-findings.md (ExpertPinsGaps); the self-expert discharge in
the same package; the distinct-expert case is not discharged there.

## Notes
The open half of the landed repair step tt-mart-repair-via-bounds-transfer
(li-trust's): the Lean instance holds at threshold one half, conditional on the
pins; the self-expert discharges them and a distinct expert does not yet.
