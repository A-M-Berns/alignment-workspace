---
id: item-38
kind: leaf
leaf_kind: task
action: "Execute item 38 per its deliverable shape and acceptance check: Enforce the write-scope conditions and the job enumeration."
who: agent
item: "38"
title: "Enforce the write-scope conditions and the job enumeration"
section: "Infrastructure"
maintainer_order: 137
difficulty: "entry"
heading_notes: " — *answered by the wiki-in-repo round*"
project: none
dispatchable: true
item_status: closed
author: "@smithy-verity"
size: S
size_reason: "one item entry of 75 words"
version: 1
---
## Statement
Item 38, Enforce the write-scope conditions and the job enumeration, is answered as its entry specifies.

## Source
PRIORITIES.md, item 38 (Enforce the write-scope conditions and the job enumeration).

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
Answered by the wiki-in-repo round. `tests/workflow_scope.py` reads the
write-scope job enumeration out of `AGENTS.md`'s *Security* section and enforces
three of the four conditions over every workflow, plus both directions of the
enumeration's own failure — a write grant absent from the list, and an entry
naming a job no workflow defines. Condition 2 is checked only in the form a script
can see: that a write-granting job's context is not a required check.
*Record:* `prompts/2026-08-16-wiki-in-repo-sync/REPORT.md`.
