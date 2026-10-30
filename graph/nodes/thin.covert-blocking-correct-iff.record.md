---
id: thin.covert-blocking-correct-iff.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ThinLegitimacy.covert_blocking_correct_iff
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: thin.covert-blocking-correct-iff
---
## Statement
The declaration Workspace.Deference.Contrib.ThinLegitimacy.covert_blocking_correct_iff is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `thin.covert-blocking-correct-iff` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/FOLLOWUP.md.
The signature of `Workspace.Deference.Contrib.ThinLegitimacy.covert_blocking_correct_iff` (theorem) in lean/Workspace/Deference/Contrib/ThinLegitimacy.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (M : Kernel W Rec) (r₀ : Rec)
        (F V : Credence W Rec) (hF : Coherent π M F) (hV : Authorship F V)
        (hM : 0 < mass π M r₀) (hsum : 0 < ∑ w, π w) :
        Correct π (constKernel r₀) V ↔ ∀ w w', 0 < π w → 0 < π w' → M.k w r₀ = M.k w' r₀
