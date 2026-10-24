---
id: item-13
kind: leaf
leaf_kind: task
action: "Execute item 13 per its deliverable shape and acceptance check: Scaffolding self-verification."
who: agent
item: "13"
title: "Scaffolding self-verification"
section: "Infrastructure"
maintainer_order: 134
difficulty: "entry"
heading_notes: " — *satisfied, kept open*"
project: none
dispatchable: true
item_status: open
work:
  - {kind: decision, ref: 2026-08-11--setup-scrub-reports-removed-root}
author: "@smithy-verity"
size: S
size_reason: "one item entry of 68 words"
version: 1
---
## Statement
Item 13, Scaffolding self-verification, is answered as its entry specifies.

## Source
PRIORITIES.md, item 13 (Scaffolding self-verification).

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
Satisfied by the scaffolding rounds and kept open. The Lean chain compiles
and audits, and the house harness, the registries and the CI job that runs them
are exercised end to end by `smoke.faf-asymp-refl`, `smoke.chain-compiles` and
`simplex.rational-points-sum-to-one`. It stays filed because the registry's demand
rule means every entry answers an item, including these, and because a future
change to the harness reopens exactly this question.
*Record:* `projects/normativity/CLAIMS.md`; `checkers/`.
