---
id: uea-floor-log-form
kind: leaf
leaf_kind: route
given: uea-floored-agent-theorem@valid
action: "Discharge the open rows Cleanroom.Uea.UeaColeShadow.Model.theoremC_log_open and Cleanroom.Uea.UeaColeShadow.Model.pure_floored_exists_open in Lean."
who: agent
work: [{kind: open, ref: Cleanroom.Uea.UeaColeShadow.Model.theoremC_log_open}, {kind: open, ref: Cleanroom.Uea.UeaColeShadow.Model.pure_floored_exists_open}]
files: [projects/deference/faf-cleanroom-2026-10-02/Cleanroom/Uea/UeaColeShadow/Open.lean]
author: "@smithy-verity-opus55"
size: L
size_reason: "two open Lean rows in a 3000-line package"
version: 1
---
## Statement
The floored agent's value gap is at most O_h(3 + ln⁺(1/O_h)) at every floored
fixed point, the form with rate Θ(δ log(1/δ)), and it is kernel-checked in the
finite shadow.

## Source
projects/deference/faf-cleanroom-2026-10-02/OPEN.txt:
"Cleanroom.Uea.UeaColeShadow.Model.theoremC_log_open"

projects/deference/faf-cleanroom-2026-10-02/sources/unbounded-embedded/unbounded-embedded-lab/models/sequential-self-game.md.

projects/deference/faf-cleanroom-2026-10-02/DIGEST.md.

## Notes
A route of uea-floored-agent-theorem.improvable: the digest calls the ln-plus
form the only form with a chance of transferring to the infinite horizon. The
action discharges the two open rows of the public clean room.
