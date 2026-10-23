---
id: kernel.box3-no-laundering.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Headline.box3_no_laundering
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: kernel.box3-no-laundering
---
## Statement
The declaration Workspace.Deference.Headline.box3_no_laundering is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `kernel.box3-no-laundering` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
The signature of `Workspace.Deference.Headline.box3_no_laundering` (theorem) in lean/Workspace/Deference/Spec/Headline.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (hφ : B.BandMap φ) (Vretro Vhonest ϖ : ℝ)
        (hr : 0 ≤ Vretro ∧ Vretro ≤ B.D) (hh : 0 ≤ Vhonest) (n : ℕ) (hϖ : 0 ≤ ϖ) :
        bandScore B φ (.retro Vretro) - ϖ * n ≤ B.whi ∧ B.whi < 0 ∧
          0 ≤ decScore B φ true true Vhonest .floor
