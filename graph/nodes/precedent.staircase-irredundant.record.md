---
id: precedent.staircase-irredundant.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.PrecedentHolding.staircase_irredundant
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: precedent.staircase-irredundant
---
## Statement
The declaration Workspace.Normativity.Contrib.PrecedentHolding.staircase_irredundant is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `precedent.staircase-irredundant` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 117).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.PrecedentHolding.staircase_irredundant` (theorem) in lean/Workspace/Normativity/Contrib/PrecedentHolding.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (s : ℕ → ℚ) (hs : StrictMono s) (n i : ℕ) (hi : i < n) :
        ¬ Permitted (staircase s n) (against s i) ∧
          Permitted ((staircase s n).filter fun c => c ≠ step s i) (against s i)
