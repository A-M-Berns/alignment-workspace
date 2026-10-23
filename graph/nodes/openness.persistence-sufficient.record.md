---
id: openness.persistence-sufficient.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.NonCapture.Scenario.robustOpenActual_of_persistence
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: openness.persistence-sufficient
---
## Statement
The declaration Workspace.Normativity.Contrib.NonCapture.Scenario.robustOpenActual_of_persistence is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `openness.persistence-sufficient` (class lean-proved, status active, origin round 2026-09-07-final-pressure-pass; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md.
The signature of `Workspace.Normativity.Contrib.NonCapture.Scenario.robustOpenActual_of_persistence` (theorem) in lean/Workspace/Normativity/Contrib/NonCaptureCertificate.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (W : R → Bool) (hcov : S.CoverageActual W)
        (hP₀ : S.actual.OpenTo) (hS : S.ClauseS) (ha : S.ClauseRa W) (hb : S.ClauseRb W)
        (hc : S.ClauseRc W) (hP : S.ClauseP) : S.RobustOpenActual
