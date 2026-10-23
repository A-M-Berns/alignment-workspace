---
id: region.patterns-complete.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_complete
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: region.patterns-complete
---
## Statement
The declaration Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_complete is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `region.patterns-complete` (class lean-proved, status active, origin round 2026-08-19-deductive-region; answers item 51).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: prompts/2026-08-19-deductive-region/REPORT.md.
The signature of `Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_complete` (theorem) in lean/Workspace/Normativity/Contrib/DeductiveRegion.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (D : Finset Sentence) (coords : List Sentence)
        (v : PCWorld) (hv : v.ConsistentWith D) :
        coords.map (ratPayout v) ∈ admissiblePatterns D coords
