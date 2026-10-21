---
id: task-claim1-inhabitant
kind: leaf
leaf_kind: task
action: "Inhabit FrozenSystemL with a diagonal contract (discharge sealedSystem_exists for it) so that defect_ge_half_diagonal is non-vacuous."
who: agent
files: [projects/deference/faf-cleanroom-2026-10-02/Cleanroom/Trust/LegitLiRegister/, projects/deference/faf-cleanroom-2026-10-02/packages/def-frozen-sibling/]
author: "@smithy-verity"
size: L
size_reason: "a Lean existence construction over the frozen-sibling package"
version: 1
---
## Statement
A sealed frozen system with a diagonal contract exists in Lean, so that the
diagonal illegitimacy theorem has an instance.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/legit-li-register/legit-li-register-report.md,
the flag on defect_ge_half_diagonal (no inhabitant with a diagonal contract
exists in the run) and the package's open list.
