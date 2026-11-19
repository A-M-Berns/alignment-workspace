---
id: appraisal.strong-split.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.AppraisalAccount.strong_split
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: appraisal.strong-split
---
## Statement
The declaration Workspace.Deference.Contrib.AppraisalAccount.strong_split is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `appraisal.strong-split` (class lean-proved, status active, origin round 2026-11-10-legitimacy-definition-prosecution; answers item 137).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md; context: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/VALUE_RESULTS.md.
The signature of `Workspace.Deference.Contrib.AppraisalAccount.strong_split` (theorem) in lean/Workspace/Deference/Contrib/AppraisalAccount.lean, verbatim, binders included, after the section variables in scope (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    variable {X : Type*} [Fintype X] (μ : X → ℝ)

    {S : Type*} [DecidableEq S] (hμ : ∀ x, 0 ≤ μ x) (s : X → S)
        (U uh : X → ℝ) (hu : ∀ x x', s x = s x' → uh x = uh x') :
        expectR μ (fun x => (uh x - condExp μ s U x) ^ 2)
          = miscalibration μ uh U + unusedInformation μ s uh U
