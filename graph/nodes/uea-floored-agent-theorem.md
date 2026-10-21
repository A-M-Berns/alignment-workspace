---
id: uea-floored-agent-theorem
kind: and
children: [uea-floored-agent-theorem.record, uea-floored-agent-theorem.bridge, uea-floored-agent-theorem.complete]
refinement_of: uea-theorem-1
author: "@smithy-verity-opus55"
size: M
size_reason: "a package report section and one Lean declaration"
version: 1
---
## Statement
In the finite shadow of Cole Wyeth's setting, every fixed point of the agent
with a one-query current-node self-trust floor is near-optimal at every
history, with value gap bounded in terms of the odds O_h against the
self-hypothesis and no factor in the number of actions.

## Source
projects/deference/faf-cleanroom-2026-10-02/sources/unbounded-embedded/unbounded-embedded-lab/models/sequential-self-game.md:
"Every fixed point of the current-node floor is near-optimal at every history"

projects/deference/faf-cleanroom-2026-10-02/packages/uea-cole-shadow/uea-cole-shadow-report.md.

projects/deference/faf-cleanroom-2026-10-02/DIGEST.md.

projects/deference/faf-cleanroom-2026-10-02/OPEN.txt:
"Cleanroom.Uea.UeaColeShadow.Model.theoremC_log_open"

## Notes
A refinement of uea-theorem-1 (refinement_of): the theorem restated for a
slightly different agent in a finite model. The ln-plus form with the tight
rate Θ(δ log(1/δ)) and the existence of pure floored fixed points are open
rows of the public clean room (OPEN.txt), which the improvement claim's routes
carry.
