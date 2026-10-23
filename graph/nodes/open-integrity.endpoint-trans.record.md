---
id: open-integrity.endpoint-trans.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.OpenIntegrityEvolution.OpenIntegrity.trans
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: open-integrity.endpoint-trans
---
## Statement
The declaration Workspace.Normativity.Contrib.OpenIntegrityEvolution.OpenIntegrity.trans is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `open-integrity.endpoint-trans` (class lean-proved, status active, origin round 2026-09-07-final-pressure-pass; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md.
The signature of `Workspace.Normativity.Contrib.OpenIntegrityEvolution.OpenIntegrity.trans` (theorem) in lean/Workspace/Normativity/Contrib/OpenIntegrityEvolution.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {sem : OpennessSemantics S anchor Γ J R}
        {O₀ O₁ O₂ : ObligationState S anchor} (h₁ : OpenIntegrity S anchor sem O₀ O₁)
        (h₂ : OpenIntegrity S anchor sem O₁ O₂) : OpenIntegrity S anchor sem O₀ O₂
