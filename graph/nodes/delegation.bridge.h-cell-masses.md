---
id: delegation.bridge.h-cell-masses
kind: leaf
leaf_kind: hypothesis
discharge: definitional
author: "@smithy-verity"
size: S
size_reason: "one hypothesis of the declaration, read"
version: 1
---
## Statement
The cell masses of the conditioning partition are nonnegative.

## Source
projects/deference/CLAIMS.md, entry `delegation.bridge` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
The signature of `Workspace.Deference.Contrib.DelegationBridge.delegation_bridge` and the definition `GradeTrust` with its docstring in lean/Workspace/Deference/Contrib/DelegationBridge.lean; prompts/2026-08-11-deference-finite-kernel/REPORT.md, §1.2 (T1 and the definition of grade trust); read by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice).

## Notes
The binder `hp : ∀ x, 0 ≤ p x`, with the cell type, the conditional expectations, the grades and the selections as the setting. Definitional: the masses of a partition's cells under a probability; the partition itself is carried by its cell type, so measurability of the objects is true by construction (the file's header calls this a re-typing, not a transcription).
