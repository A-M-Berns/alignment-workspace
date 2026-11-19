---
id: appraisal.mse-split.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.AppraisalAccount.mse_split
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: appraisal.mse-split
---
## Statement
The declaration Workspace.Deference.Contrib.AppraisalAccount.mse_split is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `appraisal.mse-split` (class lean-proved, status active, origin round 2026-11-10-legitimacy-definition-prosecution; answers item 137).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md; context: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/RESULTS.md.
The signature of `Workspace.Deference.Contrib.AppraisalAccount.mse_split` (theorem) in lean/Workspace/Deference/Contrib/AppraisalAccount.lean, verbatim, binders included, after the section variables in scope (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    variable {X : Type*} [Fintype X] {Y : Type*} [DecidableEq Y]
    variable (μ : X → ℝ)

    (hμ : ∀ x, 0 ≤ μ x) (g : X → Y) (T xhat : X → ℝ)
        (hx : ∀ x x', g x = g x' → xhat x = xhat x') :
        expectR μ (fun x => (xhat x - T x) ^ 2)
          = expectR μ (fun x => (T x - condExp μ g T x) ^ 2)
            + expectR μ (fun x => (xhat x - condExp μ g T x) ^ 2)
