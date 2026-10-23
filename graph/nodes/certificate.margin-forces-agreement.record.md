---
id: certificate.margin-forces-agreement.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.CertificateBounds.margin_forces_agreement
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: certificate.margin-forces-agreement
---
## Statement
The declaration Workspace.Deference.Contrib.CertificateBounds.margin_forces_agreement is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `certificate.margin-forces-agreement` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
Documentation: verification: prompts/2026-08-11-phase-ii-promotion/REPORT.md; context: prompts/2026-08-11-deference-certificates/REPORT.md.
The signature of `Workspace.Deference.Contrib.CertificateBounds.margin_forces_agreement` (theorem) in lean/Workspace/Deference/Contrib/CertificateBounds.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {v vh : P → ℚ} {j : P} {η γ : ℚ}
        (herr : ∀ π, |v π - vh π| ≤ η)
        (hmargin : ∀ π, π ≠ j → vh π + γ ≤ vh j)
        (hγ : 2 * η < γ) :
        ∀ π, π ≠ j → v π < v j
