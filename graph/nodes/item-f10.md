---
id: item-f10
kind: leaf
leaf_kind: task
action: "Say in graph/PROTOCOL.md §2 or §5 what a research round files for itself on the map — a node of its own, or only the round pointers on its formal results and items — and have the checker or the render reflect the choice."
who: either
item: "F10"
title: "A research round has no node of its own on the map"
section: "Workspace friction"
maintainer_order: 144
project: none
dispatchable: true
item_status: open
deliverable: "one protocol paragraph naming the shape, and either a `round` node kind the checker accepts or a sentence saying the pointers are the record."
acceptance: "python3 -m checkers.graph passes on a round filed the stated way; the two research rounds filed since 2026-10-22 conform or are listed as not conforming."
context: ["graph/PROTOCOL.md", "AGENTS.md"]
author: "@smithy-verity"
size: S
size_reason: "one protocol paragraph and the checker's reading of it"
version: 1
---
## Statement
Item F10, A research round has no node of its own on the map, is answered as its entry specifies.

## Source
ATTENTION.md, item F10 (A research round has no node of its own on the map).

## Notes
Filed by the score-side-binding round (prompts/2026-11-07-score-side-binding), which hit the gap; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
A dispatch asks a research round to "file the round's node", and `graph/PROTOCOL.md` has no
node kind for a round: a round appears only as a `work` pointer of kind `round` on the nodes
that stand for its results, items and decisions (§2, *Task leaves and work pointers*), and the
two research rounds landed since the map became canonical filed no node for themselves. The
score-side-binding round did the minimum the checker requires — a formal result per registered
claim with the round pointer, the item nodes it narrowed or filed, and the anchor lines of its
decisions — and improvised no structure. Wanted: the protocol to say which shape a research
round takes on the map, so that the next dispatch and the next round read the same rule.

*Deliverable shape:* one protocol paragraph naming the shape, and either a `round` node kind the
checker accepts or a sentence saying the pointers are the record.
*Acceptance check:* `python3 -m checkers.graph` passes on a round filed the stated way; the two
research rounds filed since 2026-10-22 conform or are listed as not conforming.
*Context:* `graph/PROTOCOL.md` §2; `AGENTS.md`, *The argument map under `graph/`*.
