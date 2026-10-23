---
id: kernel.box2-finite-time.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Headline.box2_finite_time
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: kernel.box2-finite-time
---
## Statement
The declaration Workspace.Deference.Headline.box2_finite_time is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `kernel.box2-finite-time` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
The signature of `Workspace.Deference.Headline.box2_finite_time` (theorem) in lean/Workspace/Deference/Spec/Headline.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
        (Xv Xc : LUV) (ϖ D : ℝ) (hD : 0 ≤ D) (hϖ : D < ϖ) (n : ℕ) :
        score ϖ (D * Xv.expect P n) 1 ≤ D - ϖ ∧ D - ϖ < 0 ∧ 0 ≤ score ϖ (D * Xc.expect P n) 0
