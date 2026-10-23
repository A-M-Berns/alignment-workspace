---
id: progress.edge-bound.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.NormativeInductorComposition.edge_progress_bound
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: progress.edge-bound
---
## Statement
The declaration Workspace.Normativity.Contrib.NormativeInductorComposition.edge_progress_bound is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `progress.edge-bound` (class lean-proved, status active, origin round 2026-09-06-mathematical-consolidation; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md.
The signature of `Workspace.Normativity.Contrib.NormativeInductorComposition.edge_progress_bound` (theorem) in lean/Workspace/Normativity/Contrib/NormativeInductorComposition.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (Es : Finset E) (Ss : Finset S)
        (T Λ M ε : E → S → ℝ) (d ν : S → ℝ) (Γ D : ℝ)
        (hT : ∀ e ∈ Es, ∀ s ∈ Ss, 0 ≤ T e s)
        (hd : ∀ s ∈ Ss, 0 ≤ d s)
        (hedge : ∀ e ∈ Es, ∀ s ∈ Ss, 0 < T e s → Λ e s ≤ M e s * d s + ε e s)
        (hΓ : ∀ s ∈ Ss, ∑ e ∈ Es, T e s * M e s ≤ Γ * ν s) :
        (∑ e ∈ Es, ∑ s ∈ Ss, T e s * Λ e s) +
            D * (1 - ∑ e ∈ Es, ∑ s ∈ Ss, T e s) ≤
          Γ * (∑ s ∈ Ss, ν s * d s) + (∑ e ∈ Es, ∑ s ∈ Ss, T e s * ε e s) +
            D * (1 - ∑ e ∈ Es, ∑ s ∈ Ss, T e s)
