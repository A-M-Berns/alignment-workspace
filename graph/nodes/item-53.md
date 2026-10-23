---
id: item-53
kind: leaf
leaf_kind: task
action: "Execute item 53 per its deliverable shape and acceptance check: The `May`-rule-to-scope compiler."
who: agent
item: "53"
title: "The `May`-rule-to-scope compiler"
section: "Normativity line — legitimacy"
maintainer_order: 30
difficulty: "open"
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported` at minimum — a compiler from a versioned `May` rule set to certificate-checkable scopes, with a soundness statement and its counterexamples."
acceptance: "the transition round's certificate fixtures run against compiled scopes rather than declared ones, and every self-certification and laundering attack in that round's suite still fails."
context: ["projects/normativity/legitimacy/rounds/2026-08-23-transition-certificates/MEMO.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry of 143 words"
version: 1
---
## Statement
Item 53, The `May`-rule-to-scope compiler, is delivered in the shape its entry states: `test-supported` at minimum — a compiler from a versioned `May` rule set to certificate-checkable scopes, with a soundness statement and its counterexamples.

## Source
PRIORITIES.md, item 53 (The `May`-rule-to-scope compiler); its context: `projects/normativity/legitimacy/rounds/2026-08-23-transition-certificates/MEMO.md` §6 (i), §8.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
A transition certificate cites an `AuthorityAct` carrying a `scope`, and `scope` is
a stand-in. The real object is the record's versioned `May` rules, and nothing
compiles those into scopes a certificate checker can test a cited act against. This
is where substantive authorization content actually lives: with a stand-in scope,
the certificate layer's guarantees are about citation discipline and say nothing
about what the authority permitted.

*Deliverable shape:* `test-supported` at minimum — a compiler from a versioned
`May` rule set to certificate-checkable scopes, with a soundness statement and its
counterexamples.
*Acceptance check:* the transition round's certificate fixtures run against
compiled scopes rather than declared ones, and every self-certification and
laundering attack in that round's suite still fails.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-23-transition-certificates/MEMO.md`
§6 (i), §8.
*Consumed by:* the successor to the transition-certificates round, which cannot
state what a licensed act was licensed *to do* without it.
