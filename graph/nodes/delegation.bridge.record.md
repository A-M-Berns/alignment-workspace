---
id: delegation.bridge.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.DelegationBridge.delegation_bridge
hypotheses: unread
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
