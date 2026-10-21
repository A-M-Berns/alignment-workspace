---
id: thin-value-loss-bound
kind: leaf
leaf_kind: step
action: "Prove the kernel form of the value-loss bound and the loss of correct bounded by the pathwise transparency defect, beyond deterministic records."
who: agent
files: [lean/]
work:
  - {kind: priorities, ref: 107}
author: "@smithy-verity"
size: M
size_reason: "one registered bound and its kernel form"
version: 1
---
## Statement
The value lost to defects is at most the decision problem's range times the
prior mass where the actual record departs from the model's plus the same range
times the mass where the actual verdict departs from her program's, for
deterministic records.

## Source
wiki/Legitimacy.md ("The value lost to defects is at most" the two-term bound);
projects/deference/CLAIMS.md, thin.value-loss-le-defects
(ThinLegitimacy.value_loss_le_defects, deterministic records).

## Notes
Registered for deterministic records; the kernel form is the action.
