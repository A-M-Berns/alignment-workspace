---
id: appraisal.options-hull.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.AppraisalAccount.options_of_hull
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: appraisal.options-hull
---
## Statement
The declaration Workspace.Deference.Contrib.AppraisalAccount.options_of_hull is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `appraisal.options-hull` (class lean-proved, status active, origin round 2026-11-10-legitimacy-definition-prosecution; answers item 137).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md; context: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/VALUE_RESULTS.md.
The signature of `Workspace.Deference.Contrib.AppraisalAccount.options_of_hull` (theorem) in lean/Workspace/Deference/Contrib/AppraisalAccount.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {O Aσ Aρ : Type*} [Fintype O] [Fintype Aσ] (dσ : Aσ → O → ℝ)
        (dρ : Aρ → O → ℝ)
        (h : ∀ b, ∃ w : Aσ → ℝ, (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1 ∧
          ∀ o, dρ b o = ∑ a, w a * dσ a o) :
        ∀ (g : O → ℝ) (b : Aρ), ∃ a, ∑ o, dρ b o * g o ≤ ∑ o, dσ a o * g o
