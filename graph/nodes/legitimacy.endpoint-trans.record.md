---
id: legitimacy.endpoint-trans.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.LegitimateEvolution.Legitimate.trans
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: legitimacy.endpoint-trans
---
## Statement
The declaration Workspace.Normativity.Contrib.LegitimateEvolution.Legitimate.trans is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `legitimacy.endpoint-trans` (class lean-proved, status superseded, origin round 2026-09-07-final-pressure-pass; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md.
The signature of `Workspace.Normativity.Contrib.LegitimateEvolution.Legitimate.trans` (theorem) in lean/Workspace/Normativity/Contrib/OpenIntegrityEvolution.lean (an alias declared in lean/Workspace/Normativity/Contrib/LegitimateEvolution.lean), verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {sem : OpennessSemantics S anchor Γ J R}
        {O₀ O₁ O₂ : ObligationState S anchor} (h₁ : OpenIntegrity S anchor sem O₀ O₁)
        (h₂ : OpenIntegrity S anchor sem O₁ O₂) : OpenIntegrity S anchor sem O₀ O₂
