---
id: delegation.bridge.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.DelegationBridge.delegation_bridge
hypotheses: [delegation.bridge.h-cell-masses, delegation.bridge.h-grade-trust]
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: delegation.bridge
---
## Statement
The declaration Workspace.Deference.Contrib.DelegationBridge.delegation_bridge is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `delegation.bridge` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
Documentation: verification: prompts/2026-08-11-phase-ii-promotion/REPORT.md; context: prompts/2026-08-11-deference-finite-kernel/REPORT.md.
The signature of `Workspace.Deference.Contrib.DelegationBridge.delegation_bridge` (theorem) in lean/Workspace/Deference/Contrib/DelegationBridge.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {p : C → ℚ} {EX W : C → P → ℚ} {J sel : C → P} {η : ℚ}
        (hp : ∀ x, 0 ≤ p x) (hGT : GradeTrust EX W η) :
        valuation p EX sel + gradeMargin p W J sel
            - 2 * η * disagreementMass p J sel
          ≤ valuation p EX J
## Notes
Filed by the map-as-canonical round from the registry entry and the declaration's signature; its hypotheses were unread (ruling F1, 2026-10-23) until the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice) filed the two hypothesis leaves by reading the declaration and its docstring: nonnegative cell masses, and grade trust at level η. The signature stays in the Source as the text they were read from.
