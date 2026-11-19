---
id: appraisal.deferring.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.AppraisalAccount.deferring_identity
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: appraisal.deferring
---
## Statement
The declaration Workspace.Deference.Contrib.AppraisalAccount.deferring_identity is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `appraisal.deferring` (class lean-proved, status active, origin round 2026-11-10-legitimacy-definition-prosecution; answers item 137).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md; context: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/RESULTS.md.
The signature of `Workspace.Deference.Contrib.AppraisalAccount.deferring_identity` (theorem) in lean/Workspace/Deference/Contrib/AppraisalAccount.lean, verbatim, binders included, after the section variables in scope (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    variable {X : Type*} [Fintype X] {K : Type*} [DecidableEq K] (μ : X → ℝ)

    (hμ : ∀ x, 0 ≤ μ x) (k : X → K) (U V : X → ℝ) :
        (expectR μ (fun x => (condExp μ k U x - U x) ^ 2) - expectR μ (fun x => (V x - U x) ^ 2)
            = expectR μ (fun x => (condExp μ k U x - condExp μ (fun x => (k x, V x)) U x) ^ 2)
              - expectR μ (fun x => (V x - condExp μ (fun x => (k x, V x)) U x) ^ 2))
          ∧ ((∀ x x', k x = k x' → V x = V x') →
            expectR μ (fun x => (condExp μ k U x - condExp μ (fun x => (k x, V x)) U x) ^ 2)
              = 0)
