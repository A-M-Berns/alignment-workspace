---
id: item-f12
kind: leaf
leaf_kind: task
action: "Have checkers/graph.py take its version baseline from graph/versions.json as committed, or say in graph/PROTOCOL.md that a plain run mints a version and a later uncommitted edit is a revision."
who: either
item: "F12"
title: "A node's Statement edited twice before its first commit is refused"
section: "Workspace friction"
maintainer_order: 173
project: none
dispatchable: true
item_status: open
deliverable: "either `checkers/graph.py` reading `graph/versions.json` as committed for its baseline, with a null-input case, or one sentence of `graph/PROTOCOL.md` saying that a plain run mints version 1 and what a round does on a second edit before it commits."
acceptance: "`python3 -m checkers.graph --root .` run twice on a new node whose Statement is edited between the runs, neither run committed, passes without a version bump, or refuses with a message naming the rule the protocol states."
context: ["checkers/graph.py", "graph/PROTOCOL.md"]
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
author: "@claude-fable-5-2"
size: S
size_reason: "one comparison in the checker or one protocol sentence"
version: 1
---
## Statement
Item F12, A node's Statement edited twice before its first commit is refused, is answered as its entry specifies.

## Source
ATTENTION.md, item F12 (A node's Statement edited twice before its first commit is refused).

## Notes
Filed by the twenty-second follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-22.md), which hit it; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
The plain run of `checkers/graph.py` writes `graph/versions.json`, recording version 1 of a
new node's Statement. A round that files a node, runs the checker, corrects the node's
Statement and runs the checker again before committing is refused (`Statement changed
without a version bump`), though no version of the node has been committed. The
twenty-second follow-up of the legitimacy prosecution round hit this on item 160 and
restored the three committed generated files from `HEAD` before running the checker again,
so that the node ships at version 1. The other way through is a bump to version 2, which
records a first version that never shipped. Wanted: one of the two behaviours stated, so
that a round does not choose.

*Deliverable shape:* either `checkers/graph.py` reading `graph/versions.json` as committed for its baseline, with a null-input case, or one sentence of `graph/PROTOCOL.md` saying that a plain run mints version 1 and what a round does on a second edit before it commits.
*Acceptance check:* `python3 -m checkers.graph --root .` run twice on a new node whose Statement is edited between the runs, neither run committed, passes without a version bump, or refuses with a message naming the rule the protocol states.
*Context:* `checkers/graph.py`; `graph/PROTOCOL.md`.
