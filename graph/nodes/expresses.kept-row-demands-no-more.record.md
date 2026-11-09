---
id: expresses.kept-row-demands-no-more.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.ExpressesByRole.settled_demandsNoMore
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: expresses.kept-row-demands-no-more
---
## Statement
The declaration Workspace.Normativity.Contrib.ExpressesByRole.settled_demandsNoMore is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `expresses.kept-row-demands-no-more` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 128).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.ExpressesByRole.settled_demandsNoMore` (theorem) in lean/Workspace/Normativity/Contrib/ExpressesByRole.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (ι : Fin d → Finset W) (w : Requirement W) (XA XAY : Fin d)
        (c : ℚ) (hc : c ≤ w.c) (hA : ι XA = w.A) (hAY : ι XAY = w.A ∩ w.Y)
        (hU : ∀ F : Settlement d, settleOutcome F (.strength XA XAY c) = .kept → recEvent ι F ∈ w.U) :
        DemandsNoMore ι w (settled (.strength XA XAY c))
