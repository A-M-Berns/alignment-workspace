---
id: item-8
kind: leaf
leaf_kind: question
action: "Characterize the doubly-soft weight class or find a separating instance, per PRIORITIES item 8."
who: either
item: "8"
title: "The doubly-soft weight class"
section: "Deference line"
maintainer_order: 51
difficulty: "open"
project: deference
dispatchable: true
item_status: open
deliverable: "`lean-proved`, or `witness-checked` for a negative answer."
acceptance: "The Lean gate is green; or the `witness` checker accepts the separating instance."
context: ["projects/deference/note-dump-2026-08-11/lean-deference/AUDIT.md"]
work:
  - {kind: decision, ref: 2026-08-12--deference-line-s-current-source-material}
author: "@smithy-verity-opus55"
size: M
size_reason: "one audit finding"
version: 1
---
## Statement
The class of doubly-soft weights legal as trader weights is characterized in
the intended terms.

## Source
PRIORITIES.md item 8, "The doubly-soft weight class" (open): the audit's §3.2,
"one leak closed, the class still open".

projects/deference/note-dump-2026-08-11/lean-deference/AUDIT.md §3.2.

## Notes
A negative answer (a witness that the class is not characterizable in the
intended terms) settles the item too.

## Item
The audit's §3.2 is "The doubly-soft weight: one leak closed, the class still
open".

*Deliverable shape:* `lean-proved`, or `witness-checked` for a negative answer.
*Acceptance check:* The Lean gate is green; or the `witness` checker accepts the separating instance.

*Context:* `projects/deference/note-dump-2026-08-11/lean-deference/AUDIT.md` §3.2.
*A solution ships:* a characterization of the class, or a witness that it is not
characterizable in the intended terms.
