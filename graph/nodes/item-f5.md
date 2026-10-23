---
id: item-f5
kind: leaf
leaf_kind: task
action: "Execute item F5 once the maintainers have specified it: Agent worktrees live inside the repository and nothing ignores them — *closed*."
who: either
item: "F5"
title: "Agent worktrees live inside the repository and nothing ignores them — *closed*"
section: "Workspace friction"
maintainer_order: 126
project: none
dispatchable: false
item_status: closed
author: "@smithy-verity"
size: S
size_reason: "one item entry of 60 words"
version: 1
---
## Statement
Item F5, Agent worktrees live inside the repository and nothing ignores them — *closed*, is answered as its entry specifies.

## Source
PRIORITIES.md, item F5 (Agent worktrees live inside the repository and nothing ignores them — *closed*).

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
Closed by the `.claude/` entry in `.gitignore`. Without it `git add -A` staged
another session's worktree as an embedded repository, which git reports in a hint
rather than an error and which every gate here passed. The maintainer ruled that an
ignore rule does not need a gate behind it; the gitlink check the entry also
proposed is not built.
