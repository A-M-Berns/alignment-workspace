---
id: certificate.selection-eq-of-margin.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.CertificateBounds.selection_eq_of_margin
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: certificate.selection-eq-of-margin
---
## Statement
The declaration Workspace.Deference.Contrib.CertificateBounds.selection_eq_of_margin is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `certificate.selection-eq-of-margin` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
Documentation: verification: prompts/2026-08-11-phase-ii-promotion/REPORT.md; context: prompts/2026-08-11-deference-certificates/REPORT.md.
The signature of `Workspace.Deference.Contrib.CertificateBounds.selection_eq_of_margin` (theorem) in lean/Workspace/Deference/Contrib/CertificateBounds.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {v vh : P → ℚ} {j J : P} {η γ : ℚ}
        (herr : ∀ π, |v π - vh π| ≤ η)
        (hmargin : ∀ π, π ≠ j → vh π + γ ≤ vh j)
        (hγ : 2 * η < γ)
        (hJ : ∀ π, v π ≤ v J) :
        J = j
