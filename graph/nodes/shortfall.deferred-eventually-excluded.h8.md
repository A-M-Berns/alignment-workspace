---
id: shortfall.deferred-eventually-excluded.h8
kind: leaf
leaf_kind: hypothesis
discharge: open
size: S
size_reason: "one binder of one declaration"
version: 1
author: "@smithy-verity"
---
## Statement
The hypothesis `hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (shortfallProcess short defer)).D n)` of the declaration holds.

## Source
The signature of `Workspace.Deference.Contrib.ShortfallSecurity.deferred_eventually_excluded` in lean/Workspace/Deference/Contrib/ShortfallSecurity.lean.
Binder: `hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (shortfallProcess short defer)).D n)`.
