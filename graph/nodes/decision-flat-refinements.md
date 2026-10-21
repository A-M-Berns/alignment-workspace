---
id: decision-flat-refinements
kind: and
children: [decision-flat-refinements.record, decision-flat-refinements.bridge, pairwise-coupling-setting, decision-flat-refinements.complete]
author: "@smithy-verity"
size: S
size_reason: "one package report and one section"
version: 1
---
## Statement
A refinement of an agent's information is decision-flat, no coupling edge of
the utility crossing a cell, exactly when every cellwise assembly, updateful
across cells and updateless within each, is optimal for every utility
respecting the coupling graph.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/udt-endorse-policy/udt-endorse-policy-report.md:
decisionFlat_iff (pairwise coupling).

## Notes
The repository's one theorem of the form 'what to be updateful about'; it says
the answer is a property of the utility's coupling graph, not of the subject
matter (the filing session's reading). Pairwise coupling only; the hypergraph
extension is the sibling step.
