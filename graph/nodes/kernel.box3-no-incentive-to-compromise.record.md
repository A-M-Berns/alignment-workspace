---
id: kernel.box3-no-incentive-to-compromise.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Headline.box3_no_incentive_to_compromise
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: kernel.box3-no-incentive-to-compromise
---
## Statement
The declaration Workspace.Deference.Headline.box3_no_incentive_to_compromise is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `kernel.box3-no-incentive-to-compromise` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
The signature of `Workspace.Deference.Headline.box3_no_incentive_to_compromise` (theorem) in lean/Workspace/Deference/Spec/Headline.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (hφ : B.BandMap φ) (V : ℝ) (hV : 0 ≤ V ∧ V ≤ B.D)
        {src : Source} (hs : src.Valid B) (traj eval : Bool) (h : ¬ (traj = true ∧ eval = true))
        (V' : ℝ) :
        decScore B φ traj eval V' src < decScore B φ true true V .floor ∧ |B.whi| ≤ V - φ V
