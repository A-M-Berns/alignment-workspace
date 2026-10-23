---
id: item-f1
kind: leaf
leaf_kind: task
action: "Execute item F1 once the maintainers have specified it: Job names in prose, and root documents that classify into no layer."
who: either
item: "F1"
title: "Job names in prose, and root documents that classify into no layer"
section: "Workspace friction"
maintainer_order: 122
project: none
dispatchable: false
item_status: open
author: "@smithy-verity"
size: M
size_reason: "one item entry of 168 words"
version: 1
---
## Statement
Item F1, Job names in prose, and root documents that classify into no layer, is answered as its entry specifies.

## Source
PRIORITIES.md, item F1 (Job names in prose, and root documents that classify into no layer).

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The residue of a merged entry whose first half is now a gate. A count or a job
name repeated in prose drifts from `.github/branch-protection.json` with nothing
to catch it, and it has bitten twice: three documents claimed eight gates where
seven ran, and the read-back in `.github/apply-branch-protection.sh` hardcoded
`8` and would have reported correct protection as wrong. Separately, an unlisted
root-level document defaults to the proof layer — the right default, failing
silently in the granting direction, as `RESEARCH_STATE.md` did while
contributor-editable with every gate green.

Two checks: every CI job name in prose appears in
`.github/branch-protection.json`, and every root-level `*.md` classifies into
exactly one layer. Neither can pass vacuously.

The half that is done: `tests/dead_pointers.py` checks that every rooted path a
live document cites resolves, which covers the documented-command case that opened
this entry. Audited by hand on 2026-08-17 and clean on both remaining halves, so
this stays insurance rather than repair — worth building alongside other work in
the same area, not on its own.
