---
id: solvency.conflict-names-suspects.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.WarrantSolvency.suspect_in_bundle
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: solvency.conflict-names-suspects
---
## Statement
The declaration Workspace.Normativity.Contrib.WarrantSolvency.suspect_in_bundle is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `solvency.conflict-names-suspects` (class lean-proved, status active, origin round 2026-11-07-score-side-binding; answers item 133).
Documentation: verification: projects/normativity/rounds/2026-11-07-score-side-binding/THEOREM.md; context: projects/normativity/rounds/2026-11-07-score-side-binding/REPORT.md.
The signature of `Workspace.Normativity.Contrib.WarrantSolvency.suspect_in_bundle` (theorem) in lean/Workspace/Normativity/Contrib/WarrantSolvency.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {d m : ℕ} {Q : Type*} (B : Bundle Q d) (c : FarkasCert d m)
        (hv : ∀ i, B.Allowed (c.row i)) (x : Fin d → ℚ) (hx : InCube x) :
        ∃ i, 0 < c.mult i ∧ (∃ cr ∈ B, cr.row = c.row i) ∧ ¬ (c.row i).Sat x
