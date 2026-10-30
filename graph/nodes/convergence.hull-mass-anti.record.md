---
id: convergence.hull-mass-anti.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.ConvergenceMeasure.hullMass_anti
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: convergence.hull-mass-anti
---
## Statement
The declaration Workspace.Normativity.Contrib.ConvergenceMeasure.hullMass_anti is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `convergence.hull-mass-anti` (class lean-proved, status active, origin round 2026-10-21-rebuttal-and-end-to-end; answers item 119).
Documentation: verification: projects/normativity/seed/rounds/2026-09-17-convergence-measure/DYNAMICS.md; context: projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md.
The signature of `Workspace.Normativity.Contrib.ConvergenceMeasure.hullMass_anti` (theorem) in lean/Workspace/Normativity/Contrib/ConvergenceMeasure.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {I I' : IntervalData ι d} (h : Nested I I') (Φ : Finset (Fin d))
        {w : Fin d → ℚ} (hw : ∀ φ ∈ Φ, 0 ≤ w φ) : hullMass I' Φ w ≤ hullMass I Φ w
