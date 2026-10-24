---
id: substitution.extensional-admits-both.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.SubstitutionSeparation.extensional_admits_both
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: substitution.extensional-admits-both
---
## Statement
The declaration Workspace.Deference.Contrib.SubstitutionSeparation.extensional_admits_both is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `substitution.extensional-admits-both` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
Documentation: verification: prompts/2026-08-11-phase-ii-promotion/REPORT.md; context: prompts/2026-08-11-deference-channel/REPORT.md.
The signature of `Workspace.Deference.Contrib.SubstitutionSeparation.extensional_admits_both` (theorem) in lean/Workspace/Deference/Contrib/SubstitutionSeparation.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (choice : (P → ℚ) → P) (v vh X : Ω → P → ℚ)
        (h : inducedSelection choice vh = inducedSelection choice v)
        (crit : (Ω → P) → (Ω → ℚ) → Prop) :
        crit (inducedSelection choice vh)
            (realizedQuantity X (inducedSelection choice vh))
          ↔ crit (inducedSelection choice v)
            (realizedQuantity X (inducedSelection choice v))
