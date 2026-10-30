---
id: openness.certplus-is-robust-openness.h-actual-coverage
kind: leaf
leaf_kind: hypothesis
discharge: open
author: "@smithy-verity"
size: S
size_reason: "one hypothesis of the declaration, read"
version: 1
---
## Statement
Where the concern is live on the actual prefix, some protected route is adequate there: coverage on the actual branch, witnessed inside the protected set.

## Source
projects/normativity/CLAIMS.md, entry `openness.certplus-is-robust-openness` (class lean-proved, status active, origin round 2026-09-06-mathematical-consolidation; answers item 78).
The signature of `Workspace.Normativity.Contrib.NonCapture.Scenario.certPlus_iff_robustOpen` and the definitions `CovState`, `Scenario`, `CoverageActual`, `ClauseS`, `ClauseRPlus`, `ClauseP` and `RobustOpen` in lean/Workspace/Normativity/Contrib/NonCaptureCertificate.lean; read by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice).

## Notes
The binder `hA : S.CoverageActual W`. Open: the equivalence is stated under it and nothing here derives it; an application certifies actual coverage, and without it the bill and Robust Openness come apart (the direction from the bill to openness uses it).
