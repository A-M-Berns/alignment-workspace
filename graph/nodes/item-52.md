---
id: item-52
kind: leaf
leaf_kind: task
action: "Execute item 52 per its deliverable shape and acceptance check: Import the Cartesian-frames definitions and delete the mirror."
who: agent
item: "52"
title: "Import the Cartesian-frames definitions and delete the mirror"
section: "Deference line"
maintainer_order: 53
difficulty: "entry"
project: deference
dispatchable: true
item_status: open
deliverable: "the existing declarations, unchanged in statement, over the upstream types."
acceptance: "the Lean gate is green, the axiom audit is clean, and `CartesianFrameBridge.lean` defines no frame type of its own."
context: ["prompts/2026-08-12-cartesian-frames/"]
author: "@smithy-verity"
size: M
size_reason: "one item entry of 159 words"
version: 1
---
## Statement
Item 52, Import the Cartesian-frames definitions and delete the mirror, is delivered in the shape its entry states: the existing declarations, unchanged in statement, over the upstream types.

## Source
PRIORITIES.md, item 52 (Import the Cartesian-frames definitions and delete the mirror); its context: `prompts/2026-08-12-cartesian-frames/` and its `artifacts/`, which carry the hand-run cross-check and its re-verification command.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
`lean/Workspace/Deference/Contrib/CartesianFrameBridge.lean` mirrors about two
hundred lines of the upstream `CartesianFrames/` library, because the round that
needed it was dispatched while that library was on an unmerged upstream branch
and the pin could not reach it. The pin is now `c0d885bf`, a commit on the
upstream default branch that carries `CartesianFrames/`, so the mirror is a
second definition of objects the trust chain already supplies.

The item is to import the authoritative definitions, delete the mirror, and check
that every result the bridge states still holds against them — which puts inside
the `lean` gate the cross-check that round could only run by hand, and is the
concrete value of doing it.

*Deliverable shape:* the existing declarations, unchanged in statement, over the
upstream types.
*Acceptance check:* the Lean gate is green, the axiom audit is clean, and
`CartesianFrameBridge.lean` defines no frame type of its own.
*Context:* `prompts/2026-08-12-cartesian-frames/` and its `artifacts/`, which
carry the hand-run cross-check and its re-verification command.

---
