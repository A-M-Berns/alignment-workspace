---
id: caution-outpaces-capability
kind: leaf
leaf_kind: step
action: State J4 as a trajectory inequality using corr-caution-power's floored quantilizer bound per step and prove a cumulative harm bound under it.
who: agent
files: [projects/deference/faf-cleanroom-2026-10-02/packages/corr-caution-power]
author: "@smithy-verity"
size: M
size_reason: one checklist condition and one package
version: 1
---
## Statement
The agent's calibration about its own value coverage, and the caution it takes
under low coverage, grow at least as fast as the risk that new capability
creates.

## Source
The author,
projects/deference/corrigibility-note-dump-2026-10-01/position-statement-v2.md,
section 1.3: "Even if the agent does have capabilities far beyond its
understanding of human values and legitimacy, it should be trained with the
wisdom to know that's the case, and to know the kind of caution necessary.";
checklist condition J4 in
projects/deference/corrigibility-note-dump-2026-10-01/position-statement-v2.md;
the clean-room package
projects/deference/faf-cleanroom-2026-10-02/packages/corr-caution-power
(Taylor's quantilizer theorem over the library, quantilize_optimal; the floored
caution rule's robustness under algebra misspecification,
floored_cost_bound_misspec; delegative value learning's statement S12 refuted
twice).

## Notes
Condition J4. Formal caution primitives exist; the condition is not formalized
as a trajectory statement, which is the action.
