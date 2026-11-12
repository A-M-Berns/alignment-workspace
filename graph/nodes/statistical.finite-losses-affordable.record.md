---
id: statistical.finite-losses-affordable.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.accountBounded_of_finite_losses
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: statistical.finite-losses-affordable
---
## Statement
The declaration Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.accountBounded_of_finite_losses is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `statistical.finite-losses-affordable` (class lean-proved, status active, origin round 2026-11-12-statistical-conditions; answers item 138).
Documentation: verification: projects/normativity/rounds/2026-11-12-statistical-conditions/THEOREM.md; context: projects/normativity/rounds/2026-11-12-statistical-conditions/REPORT.md.
The signature of `Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.accountBounded_of_finite_losses` (theorem) in lean/Workspace/Normativity/Contrib/StatisticalConditions.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (φ : ℕ → Sentence) (c : ℚ) (hc0 : 0 ≤ c)
        (hc1 : c < 1) (hC : M.C = floors φ (fun _ => c)) (b : ℕ → Bool)
        (hsettle : ∀ N v, M.L.Live N v → ∀ i, i < N → (v.Holds (φ i) ↔ b i = true))
        (hfresh : ∀ n, ∃ v, M.L.Live n v ∧ v.Holds (φ n))
        (R : ℕ) (hR : ∀ N, Losses.lost (c : ℝ) (realized b) N ≤ R) :
        M.AccountBounded (M.U * (((1 - (c : ℝ))⁻¹) ^ (R + 1) - 1))
