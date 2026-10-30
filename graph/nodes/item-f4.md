---
id: item-f4
kind: leaf
leaf_kind: task
action: "Execute item F4 once the maintainers have specified it: A pointer into a superseded source tree still resolves — *closed*."
who: either
item: "F4"
title: "A pointer into a superseded source tree still resolves — *closed*"
section: "Workspace friction"
maintainer_order: 125
project: none
dispatchable: false
item_status: closed
author: "@smithy-verity"
size: S
size_reason: "one item entry of 58 words"
version: 1
---
## Statement
Item F4, A pointer into a superseded source tree still resolves — *closed*, is answered as its entry specifies.

## Source
PRIORITIES.md, item F4 (A pointer into a superseded source tree still resolves — *closed*).

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
Closed by `tests/dead_pointers.py`, which checks that every rooted path a live
document cites resolves and that a citation into a tree declared disposable or
superseded says which. Both failures were invisible to every other gate, because
both are files that exist. The corpus-reconciliation round paid the second by hand
across seven pointers, one of which had materially changed.
