---
id: authority.queue-no-caused-shortfall.h-queue-move
kind: leaf
leaf_kind: hypothesis
discharge: definitional
author: "@smithy-verity"
size: S
size_reason: "one hypothesis of the declaration, read"
version: 1
---
## Statement
The agent's move at the step is queue-and-wait, in an interaction with an authority allocation, an admissibility relation and a cost table.

## Source
projects/deference/CLAIMS.md, entry `authority.queue-no-caused-shortfall` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
The signature in lean/Workspace/Deference/Contrib/EffectiveAuthority.lean, read by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice); projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md, Parts B and C.

## Notes
The binder `hq : QueueMove I π τ t` with the setting's binders. Definitional: the move examined; the conclusion follows because the post-agent state is the idle state.
