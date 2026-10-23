---
id: item-126
kind: leaf
leaf_kind: task
action: "Execute item 126 per its deliverable shape and acceptance check: The bankroll across repeated reopenings."
who: agent
item: "126"
title: "The bankroll across repeated reopenings"
section: "Deference line — second wave"
maintainer_order: 119
difficulty: "substantial"
project: normativity
dispatchable: true
item_status: open
deliverable: "`lean-proved` on `OddsBankroll.Account`."
acceptance: "the Lean audit clean; the one-reopening theorem recovered as `k = 1`."
context: ["lean/Workspace/Normativity/Contrib/OddsBankroll.lean"]
author: "@smithy-verity"
size: S
size_reason: "one item entry of 109 words"
version: 1
---
## Statement
Item 126, The bankroll across repeated reopenings, is delivered in the shape its entry states: `lean-proved` on `OddsBankroll.Account`.

## Source
PRIORITIES.md, item 126 (The bankroll across repeated reopenings); its context: `lean/Workspace/Normativity/Contrib/OddsBankroll.lean`; item 123.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
`OddsBankroll.Account.netWorth_ge_neg_odds_reopened` gives `−cap·ρ(2 + ρ)` across one
reopening from a slack world before and one after. A run with `k` rebuttals needs `k + 1`
slack worlds and a bound; iterating the one-step argument suggests `−cap·ρ·(2 + ρ)^k` or
better, and nothing is proved. Wanted: the `k`-reopening bankroll on the abstract account, and
whether a settlement-time accounting of the reopened mass (item 123) makes it linear in `k`.

*Deliverable shape:* `lean-proved` on `OddsBankroll.Account`.
*Acceptance check:* the Lean audit clean; the one-reopening theorem recovered as `k = 1`.
*Context:* `lean/Workspace/Normativity/Contrib/OddsBankroll.lean`; item 123.
*Consumed by:* any run with more than one rebuttal; the asymptotic corollary of
`.../THEOREM_STORY.md` §F beyond one revision.
