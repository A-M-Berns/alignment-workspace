---
id: item-158
kind: leaf
leaf_kind: task
action: "Execute item 158 per its deliverable shape and acceptance check: A feedback model for the long-run form of the connecting theorem."
who: agent
item: "158"
title: "A feedback model for the long-run form of the connecting theorem"
section: "Normativity line — legitimacy"
maintainer_order: 170
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`lean-proved` — in a file beside `lean/Workspace/Deference/Contrib/LegitimacyStop.lean`: a model of a run of her decisions in which, after each, he observes a stated signal, her answer at a check-in included; the three events of `long_run_stop_informed` and `long_run_stop_reference` (she does not stop though told all that is untold she would; she does not stop though her reference self would; her judgement has parted) defined in the model as labels fixed before his forecast and before any check-in; a stated condition on the signal, separating measurement from influence and making outstanding feedback and measurement error vanish on average, under which the two `UnbiasedAbove` hypotheses are proved for a stated class of forecasters; her reference self at one decision defined from that at the decision before and what she has since seen and heard; the two long-run theorems applied with their accuracy hypotheses discharged; a term inhabiting the whole hypothesis package; and an instance in which her check-in answer is one he can move, the condition fails and a conclusion fails."
acceptance: "The `lean` job green: the file builds, every theorem is under `#print axioms` within `[propext, Classical.choice, Quot.sound]`, no `sorry`, no `maxHeartbeats` option; the inhabitation witness and the failing instance are declarations of the file; rows 71 and 74 of `account/LEDGER.md` of the prosecution round each closed with its declarations named, or open with what was found."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-26--legitimacy-twenty-first-followup-connecting-theorem}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CONNECTING_THEOREM.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_STATEMENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md", "lean/Workspace/Deference/Contrib/LegitimacyStop.lean", "lean/Workspace/Deference/Contrib/LegitimacyStatement.lean", "lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean", "prompts/2026-11-10-legitimacy-definition-prosecution/REVIEW-astra-followup-21.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 1
---
## Statement
Item 158, A feedback model for the long-run form of the connecting theorem, is delivered in the shape its entry states: `lean-proved` — in a file beside `lean/Workspace/Deference/Contrib/LegitimacyStop.lean`: a model of a run of her decisions in which, after each, he observes a stated signal, her answer at a check-in included; the three events of `long_run_stop_informed` and `long_run_stop_reference` (she does not stop though told all that is untold she would; she does not stop though her reference self would; her judgement has parted) defined in the model as labels fixed before his forecast and before any check-in; a stated condition on the signal, separating measurement from influence and making outstanding feedback and measurement error vanish on average, under which the two `UnbiasedAbove` hypotheses are proved for a stated class of forecasters; her reference self at one decision defined from that at the decision before and what she has since seen and heard; the two long-run theorems applied with their accuracy hypotheses discharged; a term inhabiting the whole hypothesis package; and an instance in which her check-in answer is one he can move, the condition fails and a conclusion fails.

## Source
ATTENTION.md, item 158 (A feedback model for the long-run form of the connecting theorem); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CONNECTING_THEOREM.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_STATEMENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md`, `lean/Workspace/Deference/Contrib/LegitimacyStop.lean`, `lean/Workspace/Deference/Contrib/LegitimacyStatement.lean`, `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`, `prompts/2026-11-10-legitimacy-definition-prosecution/REVIEW-astra-followup-21.md`.

## Notes
Filed by the twenty-first follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-21.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
Rows 71 and 74 of `account/LEDGER.md`.

`LegitimacyStop.long_run_stop_informed` and `long_run_stop_reference` bound the long-run
frequency with which she fails to stop him, given that at every decision the three
sentences' hypotheses hold on his picture and that two accuracy hypotheses hold: on average
his weights are not below the frequency of her failing to stop, and his weights on her
judgement having parted are not above the frequency of that. Both are assumed. The events
are counterfactual or inner (what she would rate if told, how her reference self rates,
what she would have taken), so nothing reveals them to him unless something is built to;
the fifteenth outside review adds that an answer she gives at a check-in may report a state
the question changed, that eventual revelation alone gives no average guarantee, and that
the two directions differ, an adviser who over-weights her parting satisfying the first and
breaking the second. The theorems also take her reference self afresh at each decision.
Wanted: a model of what he observes after each decision under which the accuracy hypotheses
are theorems, and which says how one settled decision hands over to the next. A Lean
headline registers at merge.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/CONNECTING_THEOREM.md`, `account/LEGITIMACY_STATEMENT.md` and `account/LEDGER.md` in the round directory;
`LegitimacyStop.lean`, `LegitimacyStatement.lean` and `DeconfusingCorrigibility.lean` under `lean/Workspace/Deference/Contrib/`;
`REVIEW-astra-followup-21.md` in the round's prompts directory.
*Consumed by:* item 150 (the joint statement with the corrigibility theorems), item 147 (what an overseer can observe), and the round that writes the account up.
