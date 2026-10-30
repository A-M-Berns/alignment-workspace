---
id: integrity.multiplicity-witness.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness.distinct_fates
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: integrity.multiplicity-witness
---
## Statement
The declaration Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness.distinct_fates is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `integrity.multiplicity-witness` (class lean-proved, status active, origin round 2026-09-06-mathematical-consolidation; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md.
The signature of `Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness.distinct_fates` (theorem) in lean/Workspace/Normativity/Contrib/OccurrenceIntegrity.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    :
        (account 0 (Finset.mem_univ _)).fates ≠ (account 1 (Finset.mem_univ _)).fates
