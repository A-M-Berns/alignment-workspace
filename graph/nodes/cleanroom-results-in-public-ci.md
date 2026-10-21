---
id: cleanroom-results-in-public-ci
kind: leaf
leaf_kind: step
given: port-rescope-after-pin-move
author: "@smithy-verity-opus55"
size: M
size_reason: "the intake README, the lake manifest and one decision entry"
version: 1
---
## Statement
Selected clean-room results build in this repository's CI-built lean/ tree on
its current FAF pin, each with a claims-registry entry.

## Source
projects/deference/faf-cleanroom-2026-10-02/README.md, This tree is not built
by this repository's CI: "Moving selected results into lean/ needs a FAF pin
bump there and is future work." lean/lake-manifest.json pins FAF at
307119d06ac882359f1e7d1773b295b55a9be5ee; the clean-room library is pinned to
FAF 159ec3f. DECISIONS.md, entry of 2026-10-02 on the FAF pin moving to that
repository's current main and the workspace reconciled to its consolidated
LogicalInduction surface.

## Notes
The pin has moved, so the open work is the port onto the current pin, not a
pin bump; the intake README's sentence naming FAF c0d885b as the CI pin is out
of date (port-rescope-after-pin-move corrects it). The li-deference trust line
files the port of the deference results as faf-pin-bump-and-port; this step
states the outcome for every area of the run (BLI, decision problems,
corrigibility, fixpoint) and leaves the action to that task.
