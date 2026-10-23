---
id: compiler.constraints-end-to-end.h1
kind: leaf
leaf_kind: hypothesis
discharge: open
size: S
size_reason: "one binder of one declaration"
version: 1
author: "@smithy-verity"
---
## Statement
The hypothesis `hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → C.regionPred n v.payout` of the declaration holds.

## Source
The signature of `Workspace.Normativity.Contrib.EffectiveRepresentation.end_to_end_of_constraints_effective` in lean/Workspace/Normativity/Contrib/EffectiveRepresentation.lean.
Binder: `hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → C.regionPred n v.payout`.
