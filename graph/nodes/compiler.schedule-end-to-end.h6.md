---
id: compiler.schedule-end-to-end.h6
kind: leaf
leaf_kind: hypothesis
discharge: open
size: S
size_reason: "one binder of one declaration"
version: 1
author: "@smithy-verity"
---
## Statement
The hypothesis `hrep : ∀ n, ∀ φ ∈ S.coords n, repEval (S.fragment n) (S.rep n (DP.D n) φ) (S.market DP n) = q n φ` of the declaration holds.

## Source
The signature of `Workspace.Normativity.Contrib.EnforcedCompiler.ProjectionSchedule.end_to_end_effective` in lean/Workspace/Normativity/Contrib/EnforcedCompiler.lean.
Binder: `hrep : ∀ n, ∀ φ ∈ S.coords n, repEval (S.fragment n) (S.rep n (DP.D n) φ) (S.market DP n) = q n φ`.
