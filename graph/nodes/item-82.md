---
id: item-82
kind: leaf
leaf_kind: task
action: "Execute item 82 per its deliverable shape and acceptance check: Aggregation laws with several parents."
who: agent
item: "82"
title: "Aggregation laws with several parents"
section: "Deference line — second wave"
maintainer_order: 78
difficulty: "entry"
project: normativity
dispatchable: true
item_status: open
deliverable: "the extended law and the three re-proved lemmas, with a witness in which two occurrences are jointly closed by one successor and neither alone."
acceptance: "the module audits clean and `python3 tests/run.py` is green."
work:
  - {kind: decision, ref: 2026-09-07--local-laws-unary-parent-aggregation-deferred}
author: "@smithy-verity"
size: M
size_reason: "one item entry of 191 words"
version: 1
---
## Statement
A solution to item 82 ships the extension, or a statement that no application needs it.

## Source
PRIORITIES.md, item 82 (Aggregation laws with several parents); its context: `READINESS.md` §1 of the final pressure pass; `OccurrenceIntegrity.lean`, the `LocalLaw` docstring.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
`OccurrenceIntegrity.LocalLaw` transforms one requirement into successors with maps
of resolution witnesses in both directions. A genuine aggregation `(r₁, r₂) ↦ c` —
one successor resolved only by resolving both parents jointly — is not expressible:
each parent would need its own law, and the no-growth map of each demands that the
parent alone resolves `c`. No landed theorem or application needs aggregation; it is
filed so that the limitation is a recorded boundary rather than a discovered one.

Settle whether an application needs it. If so, add a law with a finite family of
parents, a joint no-growth map from the parents' witnesses to the successor's, and a
faithful-carry map back to each parent, and re-prove `Program.evaluate_subst`,
`terminals_subst` and `livePorts_subst` for accounts that share such a node across
occurrences.

*Deliverable shape:* the extended law and the three re-proved lemmas, with a witness
in which two occurrences are jointly closed by one successor and neither alone.
*Acceptance check:* the module audits clean and `python3 tests/run.py` is green.

*Context:* `READINESS.md` §1 of the final pressure pass;
`OccurrenceIntegrity.lean`, the `LocalLaw` docstring.
*A solution ships:* the extension, or a statement that no application needs it.
