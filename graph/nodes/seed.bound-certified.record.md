---
id: seed.bound-certified.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.IncompatibilitySemantics.lowerBound_certified
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: seed.bound-certified
---
## Statement
The declaration Workspace.Normativity.Contrib.IncompatibilitySemantics.lowerBound_certified is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `seed.bound-certified` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 118).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.IncompatibilitySemantics.lowerBound_certified` (theorem) in lean/Workspace/Normativity/Contrib/IncompatibilitySemantics.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
        (F : Settlement d) (φ : Fin d) (c : ℚ) (h : LowerBound S W st F φ c) :
        ∃ m, ∃ cert : BoundCert d m φ (-1),
          (∀ i, (forcedBundle S W st F).Allowed (cert.row i)) ∧ c ≤ -cert.value
