---
id: seed.forced-interval-rational.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.IncompatibilitySemantics.forcedInterval_isForcedInterval
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: seed.forced-interval-rational
---
## Statement
The declaration Workspace.Normativity.Contrib.IncompatibilitySemantics.forcedInterval_isForcedInterval is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `seed.forced-interval-rational` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 118).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.IncompatibilitySemantics.forcedInterval_isForcedInterval` (theorem) in lean/Workspace/Normativity/Contrib/IncompatibilitySemantics.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {m : ℕ} (S : Seed (m + 1) A)
        (W : List (SubItem (m + 1))) (st : DocketState) (F : Settlement (m + 1)) (φ : Fin (m + 1))
        (hne : ∃ x, forcedRegionR S W st F x) :
        IsForcedInterval S W st F φ (forcedInterval S W st F φ).1 (forcedInterval S W st F φ).2
