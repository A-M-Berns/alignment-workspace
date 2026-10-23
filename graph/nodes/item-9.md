---
id: item-9
kind: leaf
leaf_kind: task
action: "Restate each squeeze headline per PRIORITIES item 9 with strictly weaker hypotheses and a typechecking witness term."
who: either
files: ["lean/Workspace/Deference/Contrib/"]
item: "9"
title: "Forcing headlines that are squeezes"
section: "Deference line"
maintainer_order: 52
difficulty: "substantial"
project: deference
dispatchable: true
item_status: open
deliverable: "`lean-proved` restatements whose hypotheses are strictly weaker than their conclusions, each with an inhabitation witness."
acceptance: "The Lean gate is green and each restated theorem ships a typechecking witness term."
context: ["projects/deference/note-dump-2026-08-11/lean-deference/AUDIT.md"]
work:
  - {kind: decision, ref: 2026-08-12--deference-line-s-current-source-material}
author: "@smithy-verity-opus55"
size: L
size_reason: "several headlines restated with witnesses"
version: 1
---
## Statement
Each forcing headline of the public deference development is restated with
hypotheses strictly weaker than its conclusion and an inhabitation witness, or
the squeeze is shown unavoidable.

## Source
PRIORITIES.md item 9, "Forcing headlines that are squeezes": "A squeeze is a
theorem whose hypothesis already contains its conclusion; it is not false, it
is empty."

## Notes
The clean room's no-squeeze standard and N+ witnesses address the same defect
in its own library.

## Item
The audit's §3.3 is "The forcing headlines are squeezes over hypotheses
equivalent to their conclusions". A squeeze is a theorem whose hypothesis already
contains its conclusion; it is not false, it is empty.

*Deliverable shape:* `lean-proved` restatements whose hypotheses are strictly weaker than their conclusions, each with an inhabitation witness.
*Acceptance check:* The Lean gate is green and each restated theorem ships a typechecking witness term.

*Context:* `projects/deference/note-dump-2026-08-11/lean-deference/AUDIT.md` §3.3, and §5's
severity ranking.
*A solution ships:* restated theorems whose hypotheses are strictly weaker than
their conclusions, with the gap displayed — or a demonstration that the squeeze
is unavoidable, which is itself a result.
