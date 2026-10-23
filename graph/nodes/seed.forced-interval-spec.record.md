---
id: seed.forced-interval-spec.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.SeedStatics.forcedInterval_spec
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: seed.forced-interval-spec
---
## Statement
The declaration Workspace.Normativity.Contrib.SeedStatics.forcedInterval_spec is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `seed.forced-interval-spec` (class lean-proved, status active, origin round 2026-10-21-rebuttal-and-end-to-end; answers item 39).
Documentation: verification: projects/normativity/seed/rounds/2026-09-16-seed-statics/STATICS.md; context: projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md.
The signature of `Workspace.Normativity.Contrib.SeedStatics.forcedInterval_spec` (theorem) in lean/Workspace/Normativity/Contrib/SeedStatics.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {A : Type*} (S : Seed (m + 1) A) (W : List (SubItem (m + 1)))
        (st : DocketState) (F : Settlement (m + 1)) (φ : Fin (m + 1))
        (hne : ∃ x, forcedRegionR S W st F x) :
        (∀ x, forcedRegionR S W st F x →
          (((forcedInterval S W st F φ).1 : ℚ) : ℝ) ≤ x φ ∧
          x φ ≤ (((forcedInterval S W st F φ).2 : ℚ) : ℝ)) ∧
        (∃ x, forcedRegionR S W st F x ∧ x φ = (((forcedInterval S W st F φ).1 : ℚ) : ℝ)) ∧
        (∃ x, forcedRegionR S W st F x ∧ x φ = (((forcedInterval S W st F φ).2 : ℚ) : ℝ))
