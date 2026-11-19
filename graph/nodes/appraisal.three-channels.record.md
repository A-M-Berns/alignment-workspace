---
id: appraisal.three-channels.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.AppraisalAccount.three_channels
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: appraisal.three-channels
---
## Statement
The declaration Workspace.Deference.Contrib.AppraisalAccount.three_channels is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `appraisal.three-channels` (class lean-proved, status active, origin round 2026-11-10-legitimacy-definition-prosecution; answers item 137).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md; context: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/RESULTS.md.
The signature of `Workspace.Deference.Contrib.AppraisalAccount.three_channels` (theorem) in lean/Workspace/Deference/Contrib/AppraisalAccount.lean, verbatim, binders included, after the section variables in scope (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    variable {X : Type*} [Fintype X] {A : Type*} [Fintype A] [Nonempty A]
    variable {S : Type*} [DecidableEq S]
    variable (μ : X → ℝ)

    (hμ : ∀ x, 0 ≤ μ x) (U : A → X → ℝ) (s : X → S) (c : S → A) :
        expectR μ (fun x => U (c (s x)) x)
            = expectR μ (best U) - (expectR μ (best U) - expectR μ (best (ubar μ s U)))
              - expectR μ (fun x => best (ubar μ s U) x - ubar μ s U (c (s x)) x)
          ∧ 0 ≤ expectR μ (best U) - expectR μ (best (ubar μ s U))
          ∧ 0 ≤ expectR μ (fun x => best (ubar μ s U) x - ubar μ s U (c (s x)) x)
