---
id: seed.adapter-certificates-exist.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.AdapterCertificates.exists_citedFunctional
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: seed.adapter-certificates-exist
---
## Statement
The declaration Workspace.Normativity.Contrib.AdapterCertificates.exists_citedFunctional is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `seed.adapter-certificates-exist` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 118).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.AdapterCertificates.exists_citedFunctional` (theorem) in lean/Workspace/Normativity/Contrib/AdapterCertificates.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (B : Bundle (Cite d) d) (ℓ : Fin d → ℚ) (v : ℚ)
        (h : ∀ y, B.Region y → ∑ j, ℓ j * y j ≤ v) :
        ∃ c : CitedFunctional d ℓ, c.CitesLive B ∧ c.cert.value ≤ v
