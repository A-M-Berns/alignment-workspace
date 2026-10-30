---
id: item-f7
kind: leaf
leaf_kind: task
action: "Execute item F7 once the maintainers have specified it: A round cannot record a dependency on an unindexed research checkpoint."
who: either
item: "F7"
title: "A round cannot record a dependency on an unindexed research checkpoint"
section: "Workspace friction"
maintainer_order: 128
project: none
dispatchable: false
item_status: open
author: "@smithy-verity"
size: M
size_reason: "one item entry of 212 words"
version: 1
---
## Statement
Item F7, A round cannot record a dependency on an unindexed research checkpoint, is answered as its entry specifies.

## Source
PRIORITIES.md, item F7 (A round cannot record a dependency on an unindexed research checkpoint).

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
`state/rounds.json` requires every `depends_on` id to resolve, and
`workspace_state --check` fails on one that does not. Several research checkpoints on
`main` — the Progress research, witness-bridge, consolidation and liability-hard-pass
rounds, and the liability-theory round beside them — landed with round directories and
round-local provenance but no `state/rounds.json` record and no `prompts/` entry.

A later round that genuinely takes their results as hypotheses therefore has two
options, both wrong: name them and fail the checker, or index itself while claiming to
depend on nothing. The Normative Affordability round hit the question and escaped it —
it reads those checkpoints and refutes one of their hypotheses, but consumes none of
their results, so `depends_on: []` is accurate rather than convenient. The next round
that actually builds on one of them will not have that escape.

The rule the index enforces is right; what is missing is a way to say *depends on an
unindexed checkpoint*. Three candidate fixes: index the checkpoints retroactively,
which is history and cheap; allow a `depends_on_unindexed` field carrying paths rather
than ids, which is a schema change and specification layer; or rule that a research
checkpoint must be indexed at merge, which is a convention change binding future rounds
only. The choice is specification layer and was not taken here.
