---
id: exposure.greedy-duality.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ExposureGeometry.greedy_duality
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: exposure.greedy-duality
---
## Statement
The declaration Workspace.Deference.Contrib.ExposureGeometry.greedy_duality is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `exposure.greedy-duality` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
Documentation: verification: prompts/2026-08-11-phase-ii-promotion/REPORT.md; context: prompts/2026-08-11-deference-densification/REPORT.md.
The signature of `Workspace.Deference.Contrib.ExposureGeometry.greedy_duality` (theorem) in lean/Workspace/Deference/Contrib/ExposureGeometry.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {F : ℕ → ℕ} (hF : ∀ n, n < F n) (Ω : Finset ℕ) :
        ∃ Pset T : Finset ℕ, T ⊆ Ω ∧ Pierces F Pset Ω ∧ WindowsDisjoint F T ∧
          Pset.card = T.card
