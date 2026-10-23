---
id: force.row-tolerance.h4
kind: leaf
leaf_kind: hypothesis
discharge: open
size: S
size_reason: "one binder of one declaration"
version: 1
author: "@smithy-verity"
---
## Statement
The hypothesis `hbound : ∑ i ∈ pres.rowIndex, pres.intensities i * pres.rowViolation i (Q n) ^ 2 ≤ ε + M` of the declaration holds.

## Source
The signature of `Workspace.Normativity.Contrib.EnforcementStrategy.rowViolation_le_of_intensity_ge` in lean/Workspace/Normativity/Contrib/EnforcementStrategy.lean.
Binder: `hbound : ∑ i ∈ pres.rowIndex, pres.intensities i * pres.rowViolation i (Q n) ^ 2 ≤ ε + M`.
