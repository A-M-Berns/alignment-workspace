---
id: inductor.grounded-survivors.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.WarrantEntitlement.mem_survivors
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: inductor.grounded-survivors
---
## Statement
The declaration Workspace.Normativity.Contrib.WarrantEntitlement.mem_survivors is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `inductor.grounded-survivors` (class lean-proved, status active, origin round 2026-10-22-normative-inductor-integration; answers item 112).
Documentation: verification: projects/normativity/rounds/2026-10-22-normative-inductor-integration/THEOREM_STORY.md; context: projects/normativity/rounds/2026-10-22-normative-inductor-integration/HANDOFFS.md.
The signature of `Workspace.Normativity.Contrib.WarrantEntitlement.mem_survivors` (theorem) in lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {o : Occurrence d} :
        o ∈ G.survivors st F ↔
          o ∈ G ∧ ¬ undercut st o ∧ settleOutcome F o.form = .kept ∧
            ∀ j, o.cites = .occurrence j → ∃ o' ∈ G.survivors st F, o'.id = j
