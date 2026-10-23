---
id: kernel.extension-bria-realization.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.KernelExtension.bria_rate
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: kernel.extension-bria-realization
---
## Statement
The declaration Workspace.Deference.Contrib.KernelExtension.bria_rate is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `kernel.extension-bria-realization` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
The signature of `Workspace.Deference.Contrib.KernelExtension.bria_rate` (theorem) in lean/Workspace/Deference/Contrib/KernelExtension.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (D ϖ θhi w : ℝ) (hϖ : 0 < ϖ) {n : ℕ} (a : Auction n)
        (hf : a.FeasibleOpening) (ρ : ℝ) (hρ : 0 < ρ) (bid : ℕ → ℝ) (hb : ∀ k, bid k ≤ D)
        (nKnown : ℕ → ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (c S m π : ℕ → ℝ)
        (hwin : ∀ k, c k ≤ bid k - ϖ * nKnown k - ϖ * p k)
        (hcons : ∀ k, a.b k - a.G k = ((bid k - ϖ * nKnown k - ϖ * p k) - S k) / ρ)
        (hm : ∀ k, m k ≤ D - ϖ * π k) (M : ℕ → ℝ)
        (hN : ∀ K, |∑ k ∈ range K, a.w k * (S k - m k)| ≤ M K) (K : ℕ)
        (hK : 0 < ∑ k ∈ range K, a.w k) :
        (∑ k ∈ range K, a.w k * π k) / (∑ k ∈ range K, a.w k)
          ≤ (∑ k ∈ range K, a.w k * (D - c k)) / (ϖ * ∑ k ∈ range K, a.w k)
            + (ρ * a.totalAllowance K + M K) / (ϖ * ∑ k ∈ range K, a.w k)
