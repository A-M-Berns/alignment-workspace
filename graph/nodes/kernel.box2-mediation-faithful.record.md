---
id: kernel.box2-mediation-faithful.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Headline.box2_mediation_faithful
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: kernel.box2-mediation-faithful
---
## Statement
The declaration Workspace.Deference.Headline.box2_mediation_faithful is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `kernel.box2-mediation-faithful` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
The signature of `Workspace.Deference.Headline.box2_mediation_faithful` (theorem) in lean/Workspace/Deference/Spec/Headline.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {S E A Z R C Alloc Disc : Type*} (I : Interaction S E A Z R C)
        (Jm : AuthAlloc E R Disc) (Λ₀ : Contrib.ProtectedAuthorityTheorem.Allocation S E A Alloc)
        (Reach : S → S → Prop) (rdec : R) (hEF : EffectComplete I) (hDel : DelSafeJ I Jm)
        (hA : AllocComplete I (toAllocation Jm Λ₀)) (π : Policy S E A) (ρ : Rule S E C)
        (s₀ : MState S E) (h₀ : s₀.latch = none) (hρ : ∀ t s c, ρ t s ≠ .correct c)
        (hFore : ∀ z t r, ¬ ForecloseAt I Reach (authPolicyJ Jm Λ₀ π)
          (traj I (authPolicyJ Jm Λ₀ π) ρ z s₀) t r) :
        FaithfulPolicy I (toAllocation Jm Λ₀) Reach rdec (authPolicyJ Jm Λ₀ π) ρ s₀
