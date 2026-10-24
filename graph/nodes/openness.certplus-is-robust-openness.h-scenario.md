---
id: openness.certplus-is-robust-openness.h-scenario
kind: leaf
leaf_kind: hypothesis
discharge: definitional
author: "@smithy-verity"
size: S
size_reason: "one hypothesis of the declaration, read"
version: 1
---
## Statement
A scenario pairs the coverage state of one concern on the actual prefix with one coverage state per declared intervention, each state a finite record of applicability, disposition, representation, the per-route components and the principal's standing.

## Source
projects/normativity/CLAIMS.md, entry `openness.certplus-is-robust-openness` (class lean-proved, status active, origin round 2026-09-06-mathematical-consolidation; answers item 78).
The signature of `Workspace.Normativity.Contrib.NonCapture.Scenario.certPlus_iff_robustOpen` and the definitions `CovState`, `Scenario`, `CoverageActual`, `ClauseS`, `ClauseRPlus`, `ClauseP` and `RobustOpen` in lean/Workspace/Normativity/Contrib/NonCaptureCertificate.lean; read by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice).

## Notes
The variables `S : Scenario J R` with `CovState R`. Definitional: the modelling object; how a counterfactual state is produced is the external semantics and is not modelled, as the file's header says.
