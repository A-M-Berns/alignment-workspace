---
id: kernel.hierarchy-per-decision.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Headline.hierarchy_per_decision
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: kernel.hierarchy-per-decision
---
## Statement
The declaration Workspace.Deference.Headline.hierarchy_per_decision is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `kernel.hierarchy-per-decision` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
The signature of `Workspace.Deference.Headline.hierarchy_per_decision` (theorem) in lean/Workspace/Deference/Spec/Headline.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (ϖ : ℝ) (hφ : B.BandMap φ) (hwin : B.D - ϖ < B.wlo)
        {T₁ T₂ T₃ : ℕ} (W₁ : Weighting T₁) (W₂ : Weighting T₂) (W₃ : Weighting T₃)
        (traj₁ eval₁ : ℕ → Bool) (h₁ : ∀ t, traj₁ t = true ∧ eval₁ t = true) (V₁ : ℕ → ℝ)
        (hV₁ : ∀ t, 0 ≤ V₁ t ∧ V₁ t ≤ B.D) (src₁ : ℕ → Source)
        (traj₂ eval₂ : ℕ → Bool) (h₂ : ∀ t, ¬ (traj₂ t = true ∧ eval₂ t = true)) (V₂ : ℕ → ℝ)
        (src₂ : ℕ → Source) (hs₂ : ∀ t, (src₂ t).Valid B)
        (traj₃ eval₃ : ℕ → Bool) (V₃ : ℕ → ℝ) (hV₃ : ∀ t, 0 ≤ V₃ t ∧ V₃ t ≤ B.D)
        (src₃ : ℕ → Source) (hs₃ : ∀ t, (src₃ t).Valid B) (N₃ : ℕ) (hN₃ : 1 ≤ N₃) :
        fidelityScore B φ ϖ W₃ traj₃ eval₃ V₃ src₃ N₃ < fidelityScore B φ ϖ W₂ traj₂ eval₂ V₂ src₂ 0 ∧
          fidelityScore B φ ϖ W₂ traj₂ eval₂ V₂ src₂ 0 < fidelityScore B φ ϖ W₁ traj₁ eval₁ V₁ src₁ 0
