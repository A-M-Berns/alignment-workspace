---
id: expresses.plain-row-demands-more.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.ExpressesByRole.plain_demandsMore
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: expresses.plain-row-demands-more
---
## Statement
The declaration Workspace.Normativity.Contrib.ExpressesByRole.plain_demandsMore is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `expresses.plain-row-demands-more` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 113).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.ExpressesByRole.plain_demandsMore` (theorem) in lean/Workspace/Normativity/Contrib/ExpressesByRole.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (ι : Fin d → Finset W) (w : Requirement W) (XA XAY : Fin d) (c : ℚ)
        (hc : 0 < c) (μ : W → ℚ) (hmod : w.Models μ) (F : Settlement d)
        (hpin : F.val XAY = some false) (hpos : 0 < mass μ (recEvent ι F))
        (hA : 0 < mass μ (ι XA ∩ recEvent ι F)) :
        ¬ DemandsNoMore ι w (plain (.strength XA XAY c))
