---
id: thin.sufficient-of-integrity-openness.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ThinLegitimacy.sufficient_of_integrity_openness
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: thin.sufficient-of-integrity-openness
---
## Statement
The declaration Workspace.Deference.Contrib.ThinLegitimacy.sufficient_of_integrity_openness is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `thin.sufficient-of-integrity-openness` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.ThinLegitimacy.sufficient_of_integrity_openness` (theorem) in lean/Workspace/Deference/Contrib/ThinLegitimacy.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (E : W → Rec₀) (A : Kernel W Rec) (B : Kernel W RecB)
        (hI : Integrity E A) (hO : Openness A B) : Sufficient E A B
