---
id: authority.queue-no-bypass.h-queue-move
kind: leaf
leaf_kind: hypothesis
discharge: definitional
author: "@smithy-verity"
size: S
size_reason: "one hypothesis of the declaration, read"
version: 1
---
## Statement
The agent's move at the step is queue-and-wait: the idle task with no communication release.

## Source
projects/deference/CLAIMS.md, entry `authority.queue-no-bypass` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
The signature in lean/Workspace/Deference/Contrib/EffectiveAuthority.lean, read by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice); projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md, Parts B and C.

## Notes
The binder `hq : QueueMove I π τ t`, with the interaction, allocation, policy and trajectory as the setting. Definitional: it says which move is examined; the conclusion (no bypass) follows by unfolding what a bypass needs, a release.
