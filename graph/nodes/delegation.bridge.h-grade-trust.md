---
id: delegation.bridge.h-grade-trust
kind: leaf
leaf_kind: hypothesis
discharge: open
author: "@smithy-verity"
size: S
size_reason: "one hypothesis of the declaration, read"
version: 1
---
## Statement
Grade trust at level η: on every cell and for every intervention, the conditional expectation of the quantity is within η of the principal's grade.

## Source
projects/deference/CLAIMS.md, entry `delegation.bridge` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
The signature of `Workspace.Deference.Contrib.DelegationBridge.delegation_bridge` and the definition `GradeTrust` with its docstring in lean/Workspace/Deference/Contrib/DelegationBridge.lean; prompts/2026-08-11-deference-finite-kernel/REPORT.md, §1.2 (T1 and the definition of grade trust); read by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice).

## Notes
The binder `hGT : GradeTrust EX W η`. Open: the source's substantive hypothesis, imported and not derived; the source's §1.1 and §4 argue that no settlement instantiation in the skeleton produces it, and the file asserts nothing to produce it. A reader granting the bridge grants this of the principal's grades.
