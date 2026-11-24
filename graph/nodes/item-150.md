---
id: item-150
kind: leaf
leaf_kind: task
action: "Execute item 150 per its deliverable shape and acceptance check: The legitimacy model composed with the sequential corrigibility theorems."
who: agent
item: "150"
title: "The legitimacy model composed with the sequential corrigibility theorems"
section: "Normativity line — legitimacy"
maintainer_order: 162
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`lean-proved` — in a contribution namespace under `lean/Workspace/Deference/Contrib/`, a structure instantiating `DeconfusingCorrigibility.Sequential` from a sequence of `LegitimacyModel.Model`s, one for each decision, with the gate of `LegitimacyModel.legitScoring`; `Sequential.theorem3a` and `Sequential.theorem3b` applied to it; the hypothesis relating his picture at each decision to the realised evaluation stated as a predicate and taken by the theorems that use it; a term inhabiting the whole hypothesis package; and an instance on which that hypothesis alone fails and the conclusion fails."
acceptance: "The `lean` job green: the file builds, every theorem is under `#print axioms` within `[propext, Classical.choice, Quot.sound]`, no `sorry`, no `maxHeartbeats` option; the inhabitation witness and the necessity instance are declarations of the file; row 31 of `account/LEDGER.md` of the prosecution round names each declaration."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-24--legitimacy-statement-working-positions}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_STATEMENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md", "lean/Workspace/Deference/Contrib/LegitimacyModel.lean", "lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 2
---
## Statement
Item 150, The legitimacy model composed with the sequential corrigibility theorems, is delivered in the shape its entry states: `lean-proved` — in a contribution namespace under `lean/Workspace/Deference/Contrib/`, a structure instantiating `DeconfusingCorrigibility.Sequential` from a sequence of `LegitimacyModel.Model`s, one for each decision, with the gate of `LegitimacyModel.legitScoring`; `Sequential.theorem3a` and `Sequential.theorem3b` applied to it; the hypothesis relating his picture at each decision to the realised evaluation stated as a predicate and taken by the theorems that use it; a term inhabiting the whole hypothesis package; and an instance on which that hypothesis alone fails and the conclusion fails.

## Source
ATTENTION.md, item 150 (The legitimacy model composed with the sequential corrigibility theorems); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_STATEMENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md`, `lean/Workspace/Deference/Contrib/LegitimacyModel.lean`, `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`.

## Notes
Filed by the fifteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-15.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
Row 31 of `account/LEDGER.md`.

`LegitimacyModel.legitScoring` turns the legitimacy predicate into the scoring of the
corrigibility result for one decision, with no authority violation. The sequential theorems
(`Sequential.theorem3a`, `theorem3b` in `DeconfusingCorrigibility.lean`) are about realised
evaluations over many decisions; `Model` is one episode as the adviser pictures it. Nothing
relates the two. Wanted: the composition in Lean, with whatever must be assumed about his
picture against the facts named as a hypothesis and shown necessary. A Lean headline
registers at merge.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/LEGITIMACY_STATEMENT.md` and `account/LEDGER.md` in the round directory;
`lean/Workspace/Deference/Contrib/LegitimacyModel.lean`, `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`.
*Consumed by:* item 145 (the audit as a design, over more than one decision), and the round that writes the account up.
