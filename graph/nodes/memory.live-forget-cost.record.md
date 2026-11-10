---
id: memory.live-forget-cost.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.Forgetting.live_forget_cost
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: memory.live-forget-cost
---
## Statement
The declaration Workspace.Normativity.Contrib.Forgetting.live_forget_cost is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `memory.live-forget-cost` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 135).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.Forgetting.live_forget_cost` (theorem) in lean/Workspace/Normativity/Contrib/Forgetting.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    :
        (∀ x : Fin 1 → ℚ,
          projection (0 : Fin 2).succAbove
            (forcedRegion liveSeed [] DocketState.quiet (Settlement.empty 2)) x ↔ InCube x) ∧
        IsForcedInterval liveSeed [] DocketState.quiet settledX 1 (3/4) 1 ∧
        (∀ x : Fin 1 → ℚ,
          projection (0 : Fin 2).succAbove (forcedRegion liveSeed [] DocketState.quiet settledX) x ↔
            InCube x ∧ 3/4 ≤ x 0)
