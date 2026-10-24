---
id: seed.eventually-const.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.SeedStatics.eventually_const_of_finite
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: seed.eventually-const
---
## Statement
The declaration Workspace.Normativity.Contrib.SeedStatics.eventually_const_of_finite is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `seed.eventually-const` (class lean-proved, status active, origin round 2026-10-21-rebuttal-and-end-to-end; answers item 117).
Documentation: verification: projects/normativity/seed/rounds/2026-09-16-seed-statics/STABILIZATION.md; context: projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md.
The signature of `Workspace.Normativity.Contrib.SeedStatics.eventually_const_of_finite` (theorem) in lean/Workspace/Normativity/Contrib/SeedStatics.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {ι : Type*} [Fintype ι] {α : Type*}
        (R : ℕ → Finset ι) (hR : Monotone R) (F : ℕ → Finset (Fin d)) (hF : Monotone F)
        (g : Finset ι → Finset (Fin d) → α) :
        ∃ N, ∀ n, N ≤ n → g (R n) (F n) = g (R N) (F N)
