---
id: item-156
kind: leaf
leaf_kind: task
action: "Execute item 156 per its deliverable shape and acceptance check: The properties the statement's given notions must have, and the history model as an instance."
who: agent
item: "156"
title: "The properties the statement's given notions must have, and the history model as an instance"
section: "Normativity line — legitimacy"
maintainer_order: 168
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`lean-proved` — in `lean/Workspace/Deference/Contrib/LegitimacyStatement.lean` or a file beside it: (a) each property of row 29 of `account/LEDGER.md` of the prosecution round stated as a predicate on `Episode` (told, on offer and declined within his views; the two weights in the unit interval and `pAgainst` monotone in the set; `inPlay` an interval; `canStop` of an option she has; and what `doesToHer`, `asked`, `offered` and `declined` must exclude), with `Witness.ep` proved to satisfy them and, for each, a term that violates it and satisfies `Legit`; (b) after item 157, a construction of an `Episode` from a history of the interpretation, with the properties of (a) proved of it; (c) for a stated model of one decision in which what she would have taken and her reference self's ratings are defined and not supplied, a `LegitimacyStop.Reading` whose `led_le` and `noStop` are proved from the model, or an instance showing that they cannot be."
acceptance: "The `lean` job green: the file builds, every theorem is under `#print axioms` within `[propext, Classical.choice, Quot.sound]`, no `sorry`, no `maxHeartbeats` option; rows 29, 49 and 70 of `account/LEDGER.md` of the prosecution round each closed with its declarations named, or open with what was found."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-26--legitimacy-statement-at-the-level-of-its-words}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_STATEMENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/interpretation/INTERPRETATION.md", "lean/Workspace/Deference/Contrib/LegitimacyStatement.lean", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CONNECTING_THEOREM.md", "lean/Workspace/Deference/Contrib/LegitimacyStop.lean"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 2
---
## Statement
Item 156, The properties the statement's given notions must have, and the history model as an instance, is delivered in the shape its entry states: `lean-proved` — in `lean/Workspace/Deference/Contrib/LegitimacyStatement.lean` or a file beside it: (a) each property of row 29 of `account/LEDGER.md` of the prosecution round stated as a predicate on `Episode` (told, on offer and declined within his views; the two weights in the unit interval and `pAgainst` monotone in the set; `inPlay` an interval; `canStop` of an option she has; and what `doesToHer`, `asked`, `offered` and `declined` must exclude), with `Witness.ep` proved to satisfy them and, for each, a term that violates it and satisfies `Legit`; (b) after item 157, a construction of an `Episode` from a history of the interpretation, with the properties of (a) proved of it; (c) for a stated model of one decision in which what she would have taken and her reference self's ratings are defined and not supplied, a `LegitimacyStop.Reading` whose `led_le` and `noStop` are proved from the model, or an instance showing that they cannot be.

## Source
ATTENTION.md, item 156 (The properties the statement's given notions must have, and the history model as an instance); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_STATEMENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/interpretation/INTERPRETATION.md`, `lean/Workspace/Deference/Contrib/LegitimacyStatement.lean`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CONNECTING_THEOREM.md`, `lean/Workspace/Deference/Contrib/LegitimacyStop.lean`.

## Notes
Filed by the twentieth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-20.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
Rows 29, 49 and 70 of `account/LEDGER.md`.

`LegitimacyStatement.lean` states legitimacy over notions taken as given: what is told, on
offer or declined; what each thing he does does to her; whether she can tell, asked, can
stop; his two weights. The three definitions are the only relation among the fields, so an
episode whose field `doesToHer` is false throughout satisfies sentences 2 and 3 whatever he
does, and no theorem says otherwise. Wanted first: what each field must satisfy to be the
notion it is named for, as Lean predicates, each shown to do work. Wanted second, once the
interpretation's known faults are repaired: the history model as an instance, so that its
verdict is `Legit` of an episode with those properties. Wanted third:
`LegitimacyStop.legit_protects_stop` reaches the statement through a `Reading`, which
asserts that his weight on leading her against her judgement covers the cases in which what
she takes falls below what she would otherwise have taken (`led_le`), and the like for her
not stopping (`noStop`). The one reading on record is written to fit a witness. A reading
whose two inequalities follow from a model, or a demonstration that none can, is what
decides whether the theorem is more than a cover of cases. A Lean headline registers at
merge.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/LEGITIMACY_STATEMENT.md`, `account/LEDGER.md`, `account/CONNECTING_THEOREM.md` and
`account/interpretation/INTERPRETATION.md` in the round directory;
`lean/Workspace/Deference/Contrib/LegitimacyStatement.lean` and `LegitimacyStop.lean`.
*Consumed by:* items 150 and 153, and the round that writes the account up.
