---
id: item-36
kind: leaf
leaf_kind: task
action: "Execute item 36 once the maintainers have specified it: The wiki's source in the repository, synced outward."
who: either
item: "36"
title: "The wiki's source in the repository, synced outward"
section: "Infrastructure"
maintainer_order: 135
difficulty: "entry"
heading_notes: " — *answered by the wiki-in-repo round*"
project: none
dispatchable: false
item_status: closed
author: "@smithy-verity"
size: S
size_reason: "one item entry of 58 words"
version: 1
---
## Statement
Item 36, The wiki's source in the repository, synced outward, is answered as its entry specifies.

## Source
PRIORITIES.md, item 36 (The wiki's source in the repository, synced outward).

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
Answered by the wiki-in-repo round. `wiki/` is the source, the hosted wiki
is a build artifact force-pushed from it on every merge that touches the
directory, and the sync job re-clones and fails unless what it serves matches what
was pushed. `wiki/` is specification layer, so a contributor pull request touching
it fails `path-gate`.
*Record:* `prompts/2026-08-16-wiki-in-repo-sync/REPORT.md`; `DECISIONS.md`,
2026-08-16.
