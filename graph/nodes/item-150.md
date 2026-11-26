---
id: item-150
kind: leaf
leaf_kind: task
action: "Execute item 150 per its deliverable shape and acceptance check: The legitimacy statement composed with the sequential corrigibility theorems."
who: agent
item: "150"
title: "The legitimacy statement composed with the sequential corrigibility theorems"
section: "Normativity line — legitimacy"
maintainer_order: 162
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`lean-proved` — in a contribution namespace under `lean/Workspace/Deference/Contrib/`, a structure instantiating `DeconfusingCorrigibility.Sequential` from a sequence of `LegitimacyStatement.Episode`s, one for each decision, with the gate of `LegitimacyStatement.legitScoring`; `Sequential.theorem3a` and `Sequential.theorem3b` applied to it; one theorem whose hypotheses are those of the sequential theorems and whose conclusion is theirs together with the two long-run bounds of `LegitimacyStop.long_run_stop_informed` and `long_run_stop_reference`; the hypothesis relating his picture at each decision to the realised evaluation stated as a predicate and taken by the theorems that use it; a term inhabiting the whole hypothesis package; and an instance on which that hypothesis alone fails and the conclusion fails."
acceptance: "The `lean` job green: the file builds, every theorem is under `#print axioms` within `[propext, Classical.choice, Quot.sound]`, no `sorry`, no `maxHeartbeats` option; the inhabitation witness and the necessity instance are declarations of the file; rows 53 and 67 of `account/LEDGER.md` of the prosecution round name each declaration."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-26--legitimacy-statement-at-the-level-of-its-words}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_STATEMENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md", "lean/Workspace/Deference/Contrib/LegitimacyStatement.lean", "lean/Workspace/Deference/Contrib/LegitimacyGate.lean", "lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CONNECTING_THEOREM.md", "lean/Workspace/Deference/Contrib/LegitimacyStop.lean"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 4
---
## Statement
Item 150, The legitimacy statement composed with the sequential corrigibility theorems, is delivered in the shape its entry states: `lean-proved` — in a contribution namespace under `lean/Workspace/Deference/Contrib/`, a structure instantiating `DeconfusingCorrigibility.Sequential` from a sequence of `LegitimacyStatement.Episode`s, one for each decision, with the gate of `LegitimacyStatement.legitScoring`; `Sequential.theorem3a` and `Sequential.theorem3b` applied to it; one theorem whose hypotheses are those of the sequential theorems and whose conclusion is theirs together with the two long-run bounds of `LegitimacyStop.long_run_stop_informed` and `long_run_stop_reference`; the hypothesis relating his picture at each decision to the realised evaluation stated as a predicate and taken by the theorems that use it; a term inhabiting the whole hypothesis package; and an instance on which that hypothesis alone fails and the conclusion fails.

## Source
ATTENTION.md, item 150 (The legitimacy statement composed with the sequential corrigibility theorems); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_STATEMENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md`, `lean/Workspace/Deference/Contrib/LegitimacyStatement.lean`, `lean/Workspace/Deference/Contrib/LegitimacyGate.lean`, `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CONNECTING_THEOREM.md`, `lean/Workspace/Deference/Contrib/LegitimacyStop.lean`.

## Notes
Filed by the fifteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-15.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
Rows 53 and 67 of `account/LEDGER.md`.

`LegitimacyStatement.legitScoring` turns the legitimacy predicate into the scoring of the
corrigibility result for one decision, with no authority violation. The sequential theorems
(`Sequential.theorem3a`, `theorem3b` in `DeconfusingCorrigibility.lean`) are about realised
evaluations over many decisions; an `Episode` is one stretch as the adviser pictures it.
`LegitimacyStop.long_run_stop_informed` and `long_run_stop_reference` answer part of this:
with the three sentences' hypotheses at every decision of a sequence and accuracy hypotheses
of the form of `UnbiasedFromFeedback`, the two bounds on her failing to stop him hold of
long-run averages. They are not an instance of `Sequential`, their accuracy hypotheses are
assumed (item 158 asks for a model that yields them), and no statement gives an adviser who
satisfies the corrigibility hypotheses with this legitimacy test both guarantees at once.
Wanted: that joint statement in Lean, with whatever must be assumed about his picture
against the facts named as a hypothesis and shown necessary. A Lean headline registers at
merge.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/LEGITIMACY_STATEMENT.md`, `account/LEDGER.md` and `account/CONNECTING_THEOREM.md` in the round directory;
`LegitimacyStatement.lean`, `LegitimacyGate.lean`, `LegitimacyStop.lean` and `DeconfusingCorrigibility.lean` under `lean/Workspace/Deference/Contrib/`.
*Consumed by:* item 145 (the audit as a design, over more than one decision), and the round that writes the account up.
