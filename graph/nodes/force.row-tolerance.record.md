---
id: force.row-tolerance.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.EnforcementStrategy.rowViolation_le_of_intensity_ge
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: force.row-tolerance
---
## Statement
The declaration Workspace.Normativity.Contrib.EnforcementStrategy.rowViolation_le_of_intensity_ge is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `force.row-tolerance` (class lean-proved, status active, origin round 2026-08-16-traderized-enforcement; answers item 41).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-16-traderized-enforcement/ENFORCEMENT.md.
The signature of `Workspace.Normativity.Contrib.EnforcementStrategy.rowViolation_le_of_intensity_ge` (theorem) in lean/Workspace/Normativity/Contrib/EnforcementStrategy.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (pres : Presentation) (n : ℕ)
        (Q : ℕ → Sentence → ℚ) (ε M δ : ℚ) (hδ : 0 < δ) (hEM : 0 < ε + M)
        (hbound : ∑ i ∈ pres.rowIndex,
          pres.intensities i * pres.rowViolation i (Q n) ^ 2 ≤ ε + M)
        (i : Fin pres.rows.length) (hβ : (ε + M) / δ ^ 2 ≤ pres.intensities i) :
        pres.rowViolation i (Q n) ≤ δ
