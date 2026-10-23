---
id: kernel.extension-realized-rate.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.KernelExtension.DecisionInterface.realized_rate
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: kernel.extension-realized-rate
---
## Statement
The declaration Workspace.Deference.Contrib.KernelExtension.DecisionInterface.realized_rate is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `kernel.extension-realized-rate` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
The signature of `Workspace.Deference.Contrib.KernelExtension.DecisionInterface.realized_rate` (theorem) in lean/Workspace/Deference/Contrib/KernelExtension.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (K : ℕ) (hK : 0 < ∑ k ∈ range K, 𝓘.w k) :
        (∑ k ∈ range K, 𝓘.w k * 𝓘.π k) / (∑ k ∈ range K, 𝓘.w k)
          ≤ (∑ k ∈ range K, 𝓘.w k * (𝓘.D - 𝓘.c k)) / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k)
            + (𝓘.explMass K / ∑ k ∈ range K, 𝓘.w k) * ((𝓘.D - 𝓘.lo) / 𝓘.ϖ + 𝓘.θhi)
            + (𝓘.B K + 𝓘.M K) / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k)
