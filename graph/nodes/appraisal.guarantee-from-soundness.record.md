---
id: appraisal.guarantee-from-soundness.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.AccountJoin.guarantee_of_given
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: appraisal.guarantee-from-soundness
---
## Statement
The declaration Workspace.Deference.Contrib.AccountJoin.guarantee_of_given is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `appraisal.guarantee-from-soundness` (class lean-proved, status active, origin round 2026-11-10-legitimacy-definition-prosecution; answers item 137).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BRIDGE_LEAN.md; context: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md.
The signature of `Workspace.Deference.Contrib.AccountJoin.guarantee_of_given` (theorem) in lean/Workspace/Deference/Contrib/AccountJoin.lean, verbatim, binders included, after the section variables in scope (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    variable {X : Type*} [Fintype X] (μ : X → ℝ)
    variable {A : Type*} [Fintype A] {S : Type*} [DecidableEq S] {K : Type*} [DecidableEq K]
    variable [Nonempty A]

    (hμ : ∀ x, 0 ≤ μ x) (hsum : ∑ x, μ x = 1) (U : A → X → ℝ)
        (s : X → S) (c : S → A) (uhat : A → S → ℝ) (k : X → K)
        (hlink : ∀ a x x', k x = k x' → uhat a (s x) = uhat a (s x') → s x = s x') (v : ℝ)
        (hv : ∃ a, v ≤ expectR μ (U a)) :
        v - expectR μ (regret uhat s c)
            - Real.sqrt (2 * ∑ a, miscalibrationGiven μ k (fun x => uhat a (s x)) (U a))
          ≤ expectR μ (fun x => U (c (s x)) x)
