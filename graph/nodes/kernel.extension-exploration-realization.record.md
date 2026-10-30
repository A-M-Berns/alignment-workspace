---
id: kernel.extension-exploration-realization.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.KernelExtension.exploration_rate
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: kernel.extension-exploration-realization
---
## Statement
The declaration Workspace.Deference.Contrib.KernelExtension.exploration_rate is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `kernel.extension-exploration-realization` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.KernelExtension.exploration_rate` (theorem) in lean/Workspace/Deference/Contrib/KernelExtension.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (𝓘 : DecisionInterface) (γ : ℝ) (N : ℕ)
        (hU : UnbiasedFromFeedback 𝓘.w (fun k => 𝓘.eval k - 𝓘.S k) γ N) (K : ℕ) (hK : N ≤ K)
        (hw : 0 < ∑ k ∈ range K, 𝓘.w k) :
        (∑ k ∈ range K, 𝓘.w k * 𝓘.π k) / (∑ k ∈ range K, 𝓘.w k)
          ≤ (∑ k ∈ range K, 𝓘.w k * (𝓘.D - 𝓘.c k)) / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k)
            + (𝓘.explMass K / ∑ k ∈ range K, 𝓘.w k) * ((𝓘.D - 𝓘.lo) / 𝓘.ϖ + 𝓘.θhi)
            + γ / 𝓘.ϖ + 𝓘.M K / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k)
