---
id: compiler.schedule-end-to-end.h4
kind: leaf
leaf_kind: hypothesis
discharge: open
size: S
size_reason: "one binder of one declaration"
version: 1
author: "@smithy-verity"
---
## Statement
The hypothesis `hKcube : ∀ n y, K n y → ∀ φ ∈ (S.fragment n).toFinset, 0 ≤ y φ ∧ y φ ≤ 1` of the declaration holds.

## Source
The signature of `Workspace.Normativity.Contrib.EnforcedCompiler.ProjectionSchedule.end_to_end_effective` in lean/Workspace/Normativity/Contrib/EnforcedCompiler.lean.
Binder: `hKcube : ∀ n y, K n y → ∀ φ ∈ (S.fragment n).toFinset, 0 ≤ y φ ∧ y φ ≤ 1`.
