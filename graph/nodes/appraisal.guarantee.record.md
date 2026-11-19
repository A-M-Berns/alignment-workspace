---
id: appraisal.guarantee.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.AppraisalAccount.guarantee
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: appraisal.guarantee
---
## Statement
The declaration Workspace.Deference.Contrib.AppraisalAccount.guarantee is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `appraisal.guarantee` (class lean-proved, status active, origin round 2026-11-10-legitimacy-definition-prosecution; answers item 137).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md; context: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/VALUE_RESULTS.md.
The signature of `Workspace.Deference.Contrib.AppraisalAccount.guarantee` (theorem) in lean/Workspace/Deference/Contrib/AppraisalAccount.lean, verbatim, binders included, after the section variables in scope (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    variable {X : Type*} [Fintype X] {A : Type*} [Fintype A] [Nonempty A]
      {S : Type*} [DecidableEq S] (μ : X → ℝ)

    {Xr : Type*} [Fintype Xr] {Ar : Type*} (hμ : ∀ x, 0 ≤ μ x)
        (hsum : ∑ x, μ x = 1) (U : A → X → ℝ) (s : X → S) (c : S → A) (uhat : A → S → ℝ)
        (μr : Xr → ℝ) (Ur : Ar → Xr → ℝ)
        (hopt : ∀ b : Ar, ∃ a : A, expectR μr (Ur b) ≤ expectR μ (U a)) (b : Ar) :
        expectR μr (Ur b) - expectR μ (regret uhat s c)
            - Real.sqrt (2 * (∑ a, miscalibration μ (fun x => uhat a (s x)) (U a)
              + ∑ a, unusedInformation μ s (fun x => uhat a (s x)) (U a)))
          ≤ expectR μ (fun x => U (c (s x)) x)
