---
id: thin.value-of-thick.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ThinLegitimacy.value_of_thick
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: thin.value-of-thick
---
## Statement
The declaration Workspace.Deference.Contrib.ThinLegitimacy.value_of_thick is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `thin.value-of-thick` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.ThinLegitimacy.value_of_thick` (theorem) in lean/Workspace/Deference/Contrib/ThinLegitimacy.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (E : W → Rec₀) (M A : Kernel W Rec)
        (B : Kernel W RecB) (F V : Credence W Rec) (hF : Coherent π M F) (hV : Authorship F V)
        (hT : WeakTransparent π A M) (hI : Integrity E A) (hO : Openness A B) : Value π E A V B
