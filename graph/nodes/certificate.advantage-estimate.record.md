---
id: certificate.advantage-estimate.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.CertificateBounds.advantage_estimate
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: certificate.advantage-estimate
---
## Statement
The declaration Workspace.Deference.Contrib.CertificateBounds.advantage_estimate is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `certificate.advantage-estimate` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
Documentation: verification: prompts/2026-08-11-phase-ii-promotion/REPORT.md; context: prompts/2026-08-11-deference-certificates/REPORT.md.
The signature of `Workspace.Deference.Contrib.CertificateBounds.advantage_estimate` (theorem) in lean/Workspace/Deference/Contrib/CertificateBounds.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {p η : Ω → ℚ} {v vh : Ω → P → ℚ} {J Jhat : Ω → P} {π : P} {ε : ℚ}
        (hp : ∀ ω, 0 ≤ p ω)
        (herr : ∀ ω π, |v ω π - vh ω π| ≤ η ω)
        (hJ : ∀ ω π, v ω π ≤ v ω (J ω))
        (hJhat : ∀ ω π, vh ω π ≤ vh ω (Jhat ω))
        (hTR : ∑ ω, p ω * η ω ≤ ε) :
        |advantage p v J π - advantage p vh Jhat π| ≤ 2 * ε
