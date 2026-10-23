---
id: rebuttal.liability-rebutted.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.liability_rebutted
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: rebuttal.liability-rebutted
---
## Statement
The declaration Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.liability_rebutted is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `rebuttal.liability-rebutted` (class lean-proved, status active, origin round 2026-10-21-rebuttal-and-end-to-end; answers item 113).
Documentation: verification: projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/REBUTTAL.md; context: projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/REBUTTAL.md.
The signature of `Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.liability_rebutted` (theorem) in lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ n₁ nE : ℕ)
        (hnE : 0 < nE) :
        ∀ n (v : PCWorld), (L n₁ nE false).Live n v →
          -(3 * (ρ c : ℝ) * (2 + ρ c)) ≤
            (realizedEnforcer (L n₁ nE false) (warrantEnforcer (schedRebutted c β hβ n₀ nE))).netWorth
              (history (L n₁ nE false) (warrantEnforcer (schedRebutted c β hβ n₀ nE))) v n
