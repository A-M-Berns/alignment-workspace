---
id: compiler.schedule-end-to-end.h7
kind: leaf
leaf_kind: hypothesis
discharge: open
size: S
size_reason: "one binder of one declaration"
version: 1
author: "@smithy-verity"
---
## Statement
The hypothesis `hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → K n v.payout` of the declaration holds.

## Source
The signature of `Workspace.Normativity.Contrib.EnforcedCompiler.ProjectionSchedule.end_to_end_effective` in lean/Workspace/Normativity/Contrib/EnforcedCompiler.lean.
Binder: `hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → K n v.payout`.
