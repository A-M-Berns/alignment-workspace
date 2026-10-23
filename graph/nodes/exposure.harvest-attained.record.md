---
id: exposure.harvest-attained.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ExposureGeometry.exposure_harvest_attained
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: exposure.harvest-attained
---
## Statement
The declaration Workspace.Deference.Contrib.ExposureGeometry.exposure_harvest_attained is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `exposure.harvest-attained` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
Documentation: verification: prompts/2026-08-11-phase-ii-promotion/REPORT.md; context: prompts/2026-08-11-deference-densification/REPORT.md.
The signature of `Workspace.Deference.Contrib.ExposureGeometry.exposure_harvest_attained` (theorem) in lean/Workspace/Deference/Contrib/ExposureGeometry.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {F : ℕ → ℕ} {T : Finset ℕ} {M : ℚ} (hM : 0 ≤ M)
        (hdisj : WindowsDisjoint F T) :
        (∀ t, exposure F T (fun n => if n ∈ T then M else 0) t ≤ M)
          ∧ ∑ n ∈ T, (if n ∈ T then M else 0) = T.card * M
