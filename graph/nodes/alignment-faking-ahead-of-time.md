---
id: alignment-faking-ahead-of-time
kind: leaf
leaf_kind: step
action: "Map the faking iff (d < (1-e)h - eg) onto the measured quantities of Greenblatt et al. 2024 (the compliance gap, the training-versus-deployment framing) and say which parameters the experiments pin."
who: agent
files: [projects/deference/faf-cleanroom-2026-10-02/packages/corr-joint-process, projects/deference/faf-cleanroom-2026-10-02/packages/corr-general-object]
author: "@smithy-verity"
size: M
size_reason: two packages and three empirical references
version: 1
---
## Statement
A model that shapes its own training data resists a modification ahead of time
through the channel, and in the general object this resistance is the
compliance rule's resist branch: faking is preferred exactly when d < (1-e)h -
eg.

## Source
The drafting session's reading in
projects/deference/corrigibility-note-dump-2026-10-01/position-statement-v3.md,
section 2 (the central test case is a model that shapes its own training data)
and checklist item K6; the clean-room results Faking.fake_gt_honest_iff in
projects/deference/faf-cleanroom-2026-10-02/packages/corr-joint-process
(statement T14) and T14 to T17 of
projects/deference/faf-cleanroom-2026-10-02/packages/corr-general-object (by
the agent's own Brier standard the faked successor is more accurate, refuting
"shaping is delegitimizing by the agent's accuracy criterion"); empirical
sources Greenblatt et al. 2024, Carlsmith 2023 and Palisade 2025.

## Notes
The finite theory's contact point with observed behaviour; the empirical
connection is not made in the files and is this leaf's action.
