---
id: thin.reflection-inherited-value.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ThinLegitimacy.reflection_inherited_value
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: thin.reflection-inherited-value
---
## Statement
The declaration Workspace.Deference.Contrib.ThinLegitimacy.reflection_inherited_value is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `thin.reflection-inherited-value` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.ThinLegitimacy.reflection_inherited_value` (theorem) in lean/Workspace/Deference/Contrib/ThinLegitimacy.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (a : W → Rec)
        (V : Credence W Rec) (hC : Correct π (detKernel a) V) :
        ∀ (X : W → ℝ) (s : ℝ),
          s * (∑ w, π w) ≤ ∑ w, π w * (if s ≤ (∑ v, credenceOf a V w v * X v) then X w else s)
