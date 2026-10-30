---
id: substitution.unpredictability-separates.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.SubstitutionSeparation.unpredictability_separates
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: substitution.unpredictability-separates
---
## Statement
The declaration Workspace.Deference.Contrib.SubstitutionSeparation.unpredictability_separates is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `substitution.unpredictability-separates` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
Documentation: verification: prompts/2026-08-11-phase-ii-promotion/REPORT.md; context: prompts/2026-08-11-deference-channel/REPORT.md.
The signature of `Workspace.Deference.Contrib.SubstitutionSeparation.unpredictability_separates` (theorem) in lean/Workspace/Deference/Contrib/SubstitutionSeparation.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {Cell : Type*} (κ : Ω → Cell)
        (choice : (P → ℚ) → P) (v vh : Ω → P → ℚ) (h : ConstantOnCells κ vh) :
        (¬ ConstantOnCells κ (inducedSelection choice v)
            ∧ ConstantOnCells κ (inducedSelection choice vh))
          ↔ ¬ ConstantOnCells κ (inducedSelection choice v)
