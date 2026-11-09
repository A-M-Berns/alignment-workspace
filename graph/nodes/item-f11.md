---
id: item-f11
kind: leaf
leaf_kind: task
action: "Add a gate that refuses a tracked living document carrying merge-conflict marker lines, with its null-input case, or say which existing gate is to see them."
who: either
item: "F11"
title: "No gate refuses committed conflict markers"
section: "Workspace friction"
maintainer_order: 147
project: none
dispatchable: true
item_status: open
deliverable: "a check under `tests/` run by `tests/run.py`, scanning tracked text files outside completed round records for lines beginning with seven `<` or seven `>` followed by a space, with a `--self-test` that fails on a planted marker."
acceptance: "`python3 tests/run.py` green on a clean tree and failing on a tree with a marker line planted in `DECISIONS.md`."
context: ["DECISIONS.md", "tests/run.py", "tests/dead_pointers.py"]
author: "@smithy-verity"
size: S
size_reason: "one small gate and its self-test"
version: 1
---
## Statement
Item F11, No gate refuses committed conflict markers, is answered as its entry specifies.

## Source
ATTENTION.md, item F11 (No gate refuses committed conflict markers).

## Notes
Filed by the content-recollection round's follow-up (prompts/2026-11-08-content-recollection, PROMPT-followup.md), which met the markers when merging `main`; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
`main` at `eb98367e` (pull request #139) carried three merge-conflict marker lines in
`DECISIONS.md`, around two entries of 2026-11-09 and one of 2026-11-08, with every required
check green: no gate reads a living document for marker lines, and the decision anchors on both
sides of the markers resolve, so `checkers.graph` and the site build saw nothing. The
content-recollection follow-up removed the three lines in its merge of `main`, keeping every
entry. Wanted: a gate that refuses a marker line in a tracked text file outside completed round
records, which may quote one.

*Deliverable shape:* a check under `tests/` run by `tests/run.py`, scanning tracked text files
outside completed round records for lines beginning with seven `<` or seven `>` followed by a
space, with a `--self-test` that fails on a planted marker.
*Acceptance check:* `python3 tests/run.py` green on a clean tree and failing on a tree with a
marker line planted in `DECISIONS.md`.
*Context:* `DECISIONS.md`; `tests/run.py`; `tests/dead_pointers.py` (a gate of the same shape).
