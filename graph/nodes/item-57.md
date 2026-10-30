---
id: item-57
kind: leaf
leaf_kind: task
action: "Execute item 57 per its deliverable shape and acceptance check: A checker for the applicability-in-source convention."
who: agent
item: "57"
title: "A checker for the applicability-in-source convention"
section: "Normativity line — legitimacy"
maintainer_order: 34
difficulty: "entry"
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "a checker plus the claim it certifies, registered `contributor-checked`, or a house checker if the maintainer reads it."
acceptance: "`python3 -m checkers.run` accepts the entry, and the checker fails on a ledger containing one violating occurrence and on an empty ledger it was told to check."
author: "@smithy-verity"
size: M
size_reason: "one item entry of 163 words"
version: 1
---
## Statement
Item 57, A checker for the applicability-in-source convention, is delivered in the shape its entry states: a checker plus the claim it certifies, registered `contributor-checked`, or a house checker if the maintainer reads it.

## Source
PRIORITIES.md, item 57 (A checker for the applicability-in-source convention); its context: `.../2026-08-23-reason-representation/MEMO.md`, Convention 1; `.../2026-08-23-transition-certificates/README.md`.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
An occurrence applying a schema to a case view must carry the applicability claim
among its sources. The reason state depends on it: with the convention, an
undercutter is an ordinary reason against the applicability claim and needs no
attack primitive; without it, the enabling relation is wrong in a way the substrate
cannot report.

The convention is stated and nothing enforces it. A checker over a reason ledger
that fails an occurrence whose sources omit its own applicability claim is small,
prospective, and exactly the shape `checkers/contrib/` is open for.

*Deliverable shape:* a checker plus the claim it certifies, registered
`contributor-checked`, or a house checker if the maintainer reads it.
*Acceptance check:* `python3 -m checkers.run` accepts the entry, and the checker
fails on a ledger containing one violating occurrence and on an empty ledger it was
told to check.
*Context:* `.../2026-08-23-reason-representation/MEMO.md`, Convention 1;
`.../2026-08-23-transition-certificates/README.md`.
*Consumed by:* any round treating applicability-in-source as enforced rather than
declared. The transition round's certificate layer already does.
