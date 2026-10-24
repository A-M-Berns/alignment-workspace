---
id: thin.correct-of-thick.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ThinLegitimacy.correct_of_coherent_authorship_transparent
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: thin.correct-of-thick
---
## Statement
The declaration Workspace.Deference.Contrib.ThinLegitimacy.correct_of_coherent_authorship_transparent is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `thin.correct-of-thick` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.ThinLegitimacy.correct_of_coherent_authorship_transparent` (theorem) in lean/Workspace/Deference/Contrib/ThinLegitimacy.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (π : W → ℝ) (M A : Kernel W Rec)
        (F V : Credence W Rec) (hF : Coherent π M F) (hV : Authorship F V)
        (hT : WeakTransparent π A M) : Correct π A V
