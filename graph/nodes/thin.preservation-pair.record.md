---
id: thin.preservation-pair.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ThinLegitimacy.preservation_pair
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: thin.preservation-pair
---
## Statement
The declaration Workspace.Deference.Contrib.ThinLegitimacy.preservation_pair is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `thin.preservation-pair` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.ThinLegitimacy.preservation_pair` (theorem) in lean/Workspace/Deference/Contrib/ThinLegitimacy.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (E : W → Rec₀) (A : Kernel W Rec)
        (V : Credence W Rec) (hC : Correct π A V) (hI : Integrity E A) (e : Rec₀) (r : Rec)
        (hp : 0 < mass π (refKernel E A) (e, r)) : V r = post π (refKernel E A) (e, r)
