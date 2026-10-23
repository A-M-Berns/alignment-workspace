---
id: compiler.schedule-end-to-end.h3
kind: leaf
leaf_kind: hypothesis
discharge: open
size: S
size_reason: "one binder of one declaration"
version: 1
author: "@smithy-verity"
---
## Statement
The hypothesis `hlocal : ∀ n, FragmentLocal (S.fragment n).toFinset (K n)` of the declaration holds.

## Source
The signature of `Workspace.Normativity.Contrib.EnforcedCompiler.ProjectionSchedule.end_to_end_effective` in lean/Workspace/Normativity/Contrib/EnforcedCompiler.lean.
Binder: `hlocal : ∀ n, FragmentLocal (S.fragment n).toFinset (K n)`.
