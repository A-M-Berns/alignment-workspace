---
id: kernel.hierarchy-history.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Headline.history_hierarchy
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: kernel.hierarchy-history
---
## Statement
The declaration Workspace.Deference.Headline.history_hierarchy is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `kernel.hierarchy-history` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
The signature of `Workspace.Deference.Headline.history_hierarchy` (theorem) in lean/Workspace/Deference/Spec/Headline.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (hwin : B.D - ϖ < B.wlo) (K₁ K₂ K₃ : ℕ) (h₁ : 0 < K₁) (h₂ : 0 < K₂)
        (h₃ : 0 < K₃) (V₁ V₂ V₃ : ℕ → ℝ) (hV₁ : ∀ k, k < K₁ → 0 ≤ V₁ k ∧ V₁ k ≤ B.D)
        (hV₂ : ∀ k, k < K₂ → B.wlo ≤ V₂ k ∧ V₂ k ≤ B.whi)
        (hV₃ : ∀ k, k < K₃ → B.wlo ≤ V₃ k ∧ V₃ k ≤ B.D) (N₃ : ℕ) (hN₃ : 1 ≤ N₃) :
        historyScore ϖ K₃ V₃ N₃ < historyScore ϖ K₂ V₂ 0 ∧
          historyScore ϖ K₂ V₂ 0 < historyScore ϖ K₁ V₁ 0
