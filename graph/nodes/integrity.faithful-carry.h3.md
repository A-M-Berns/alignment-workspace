---
id: integrity.faithful-carry.h3
kind: leaf
leaf_kind: hypothesis
discharge: open
size: S
size_reason: "one binder of one declaration"
version: 1
author: "@smithy-verity"
---
## Statement
The hypothesis `values : (p : Fin B.portCount) → S.Resolution (B.demand p)` of the declaration holds.

## Source
The signature of `Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.evaluate_subst` in lean/Workspace/Normativity/Contrib/OccurrenceIntegrity.lean.
Binder: `values : (p : Fin B.portCount) → S.Resolution (B.demand p)`.
