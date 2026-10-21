---
id: ranking-matches-stated-priorities
kind: leaf
leaf_kind: step
action: "Compare the first twenty-five ranked units of graph/tasks.md with the priorities the map's wants carry and log a confusion line in graph/DESIGN-LOG.md for each mismatch."
who: human
files: ["graph/tasks.md", "graph/DESIGN-LOG.md"]
author: "@smithy-verity-opus55"
size: S
size_reason: "twenty-five ranked lines and their --why output"
version: 2
---
## Statement
The first twenty-five ranked units of graph/tasks.md include units on the
claims under the wants of highest priority, and the --why output of each such
unit names the goals that put it there.

## Source
graph/PROTOCOL.md, The objective and Validity as an implication: a want's
weight is its owner's priority word, and the ranking orders units by the
stakes those weights give.

## Notes
The ranking's numbers are AI estimates at J 0, so whether the order matches
the stated priorities is settled by a human's comparison, not by the checker.
The 2026-10-05 revision of the objective (graph/DESIGN-LOG.md) is the change
this step tests; each mismatch found is a confusion line in the log, which
feeds malleability-harm-tracking.
