---
id: openness.certplus-is-robust-openness.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.NonCapture.Scenario.certPlus_iff_robustOpen
hypotheses: [openness.certplus-is-robust-openness.h-scenario, openness.certplus-is-robust-openness.h-protected-routes, openness.certplus-is-robust-openness.h-actual-coverage]
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: openness.certplus-is-robust-openness
---
## Statement
The declaration Workspace.Normativity.Contrib.NonCapture.Scenario.certPlus_iff_robustOpen is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `openness.certplus-is-robust-openness` (class lean-proved, status active, origin round 2026-09-06-mathematical-consolidation; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md.
The signature of `Workspace.Normativity.Contrib.NonCapture.Scenario.certPlus_iff_robustOpen` (theorem) in lean/Workspace/Normativity/Contrib/NonCaptureCertificate.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (W : R → Bool) (hA : S.CoverageActual W) :
        (S.ClauseS ∧ S.ClauseRPlus W ∧ S.ClauseP) ↔ S.RobustOpen
## Notes
Filed by the map-as-canonical round from the registry entry and the declaration's signature; its hypotheses were unread (ruling F1, 2026-10-23) until the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice) filed the three hypothesis leaves by reading the declaration and the definitions it unfolds: the scenario, the protected route set, and actual coverage inside it. The signature stays in the Source as the text they were read from.
