---
id: inductor.conformance.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.excess_le_tol
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: inductor.conformance
---
## Statement
The declaration Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.excess_le_tol is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `inductor.conformance` (class lean-proved, status active, origin round 2026-10-22-normative-inductor-integration; answers item 39).
Documentation: verification: projects/normativity/rounds/2026-10-22-normative-inductor-integration/THEOREM_STORY.md; context: projects/normativity/rounds/2026-10-22-normative-inductor-integration/HANDOFFS.md.
The signature of `Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.excess_le_tol` (theorem) in lean/Workspace/Normativity/Contrib/WarrantForce.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (n : ℕ) (y : Fin d → ℚ) (hy : (W.bundle n).Region y) {c : CitedRow (Cite d) d}
        (hc : c ∈ W.bundle n) : excess c.row (W.priceVec DP n) ≤ W.tol n
