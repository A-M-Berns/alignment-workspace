---
id: seed.independence-strict.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.SeedStatics.seed_independence_strict
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: seed.independence-strict
---
## Statement
The declaration Workspace.Normativity.Contrib.SeedStatics.seed_independence_strict is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `seed.independence-strict` (class lean-proved, status active, origin round 2026-10-21-rebuttal-and-end-to-end; answers item 117).
Documentation: verification: projects/normativity/seed/rounds/2026-09-16-seed-statics/CRITERION.md; context: projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md.
The signature of `Workspace.Normativity.Contrib.SeedStatics.seed_independence_strict` (theorem) in lean/Workspace/Normativity/Contrib/SeedStatics.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {Q : Type*} (B : Bundle Q d) (L₁ L₂ : List (Row d)) (φ : Fin d)
        (p : ℝ)
        (hne₁ : ∃ x, B.RegionR x ∧ ∀ r ∈ L₁, StrictSatR r x)
        (hpin : ∀ x, B.RegionR x → (∀ r ∈ L₁, StrictSatR r x) → x φ = p) :
        ∀ x, B.RegionR x → (∀ r ∈ L₂, StrictSatR r x) → x φ = p
