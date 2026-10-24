---
id: exposure.harvest-bound.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ExposureGeometry.exposure_harvest_bound
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: exposure.harvest-bound
---
## Statement
The declaration Workspace.Deference.Contrib.ExposureGeometry.exposure_harvest_bound is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `exposure.harvest-bound` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
Documentation: verification: prompts/2026-08-11-phase-ii-promotion/REPORT.md; context: prompts/2026-08-11-deference-densification/REPORT.md.
The signature of `Workspace.Deference.Contrib.ExposureGeometry.exposure_harvest_bound` (theorem) in lean/Workspace/Deference/Contrib/ExposureGeometry.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {F : ℕ → ℕ} {Ω Pset : Finset ℕ} {a : ℕ → ℚ} {M : ℚ}
        (ha : ∀ n, 0 ≤ a n) (hP : Pierces F Pset Ω) (hE : ∀ t, exposure F Ω a t ≤ M) :
        ∑ n ∈ Ω, a n ≤ Pset.card * M
