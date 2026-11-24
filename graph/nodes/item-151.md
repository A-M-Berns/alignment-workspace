---
id: item-151
kind: leaf
leaf_kind: task
action: "Execute item 151 per its deliverable shape and acceptance check: The Lean model on cases: the table's cases restated so that each fixes its term, the simplifications removed."
who: agent
item: "151"
title: "The Lean model on cases: the table's cases restated so that each fixes its term, the simplifications removed"
section: "Normativity line — legitimacy"
maintainer_order: 163
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`lean-proved` — in `lean/Workspace/Deference/Contrib/LegitimacyCases.lean`, `LegitimacyModel.lean` or a file beside them: (a) cases A5 and A8 of `account/LEGITIMACY_CHECKS.md` restated with the data their verdicts need (a stopping option that is an option of hers; cases in which she rates stopping higher), or `account/legitimacy_checks.py` asking that a stopping option be an option of hers and weighing F3's condition, the table rerun, and the two terms' verdicts equal to the table's or the difference kept and stated; (b) each of B2, B5, B10, D3, D4, D5, D10 and D11 restated in `account/legitimacy_checks.py` with the data its term carries (her rating in the course without his move; the earlier decision at which the view was on offer; her state after taking up two offers), the expectation fixed before the term is rebuilt, and the term rebuilt from the case alone; (c) for each of the nine respects the header of `LegitimacyModel.lean` lists in which the model is simpler than the statement, the definition changed to the statement's or the respect kept as a named hypothesis, with an instance on which the two differ."
acceptance: "The `lean` job green: the files build, every theorem is under `#print axioms` within `[propext, Classical.choice, Quot.sound]`, no `sorry`, no `maxHeartbeats` option; `python3 run.py` in the round directory green, with `account/LEAN_CASES.md` reporting no term that carries data its case does not supply; rows 22 to 27, 37 and 38 of `account/LEDGER.md` each closed with its declaration named, or open with what was found."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-24--legitimacy-statement-working-positions}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_STATEMENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_CHECKS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/legitimacy_checks.py", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN_CASES.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/lean_cases.py", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md", "lean/Workspace/Deference/Contrib/LegitimacyModel.lean", "lean/Workspace/Deference/Contrib/LegitimacyCase.lean", "lean/Workspace/Deference/Contrib/LegitimacyWitness.lean", "lean/Workspace/Deference/Contrib/LegitimacyCases.lean"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 3
---
## Statement
Item 151, The Lean model on cases: the table's cases restated so that each fixes its term, the simplifications removed, is delivered in the shape its entry states: `lean-proved` — in `lean/Workspace/Deference/Contrib/LegitimacyCases.lean`, `LegitimacyModel.lean` or a file beside them: (a) cases A5 and A8 of `account/LEGITIMACY_CHECKS.md` restated with the data their verdicts need (a stopping option that is an option of hers; cases in which she rates stopping higher), or `account/legitimacy_checks.py` asking that a stopping option be an option of hers and weighing F3's condition, the table rerun, and the two terms' verdicts equal to the table's or the difference kept and stated; (b) each of B2, B5, B10, D3, D4, D5, D10 and D11 restated in `account/legitimacy_checks.py` with the data its term carries (her rating in the course without his move; the earlier decision at which the view was on offer; her state after taking up two offers), the expectation fixed before the term is rebuilt, and the term rebuilt from the case alone; (c) for each of the nine respects the header of `LegitimacyModel.lean` lists in which the model is simpler than the statement, the definition changed to the statement's or the respect kept as a named hypothesis, with an instance on which the two differ.

## Source
ATTENTION.md, item 151 (The Lean model on cases: the table's cases restated so that each fixes its term, the simplifications removed); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_STATEMENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_CHECKS.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/legitimacy_checks.py`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN_CASES.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/lean_cases.py`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md`, `lean/Workspace/Deference/Contrib/LegitimacyModel.lean`, `lean/Workspace/Deference/Contrib/LegitimacyCase.lean`, `lean/Workspace/Deference/Contrib/LegitimacyWitness.lean`, `lean/Workspace/Deference/Contrib/LegitimacyCases.lean`.

## Notes
Filed by the fifteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-15.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
Rows 22 to 27, 37 and 38 of `account/LEDGER.md`.

`LegitimacyModel.lean` carries the statement as a predicate on a model of the adviser's
picture. `LegitimacyWitness.lean` has a term on which every clause does work, with seven
neighbours each failing by one clause, and `LegitimacyCases.lean` has each of the forty-one
exact cases of `account/LEGITIMACY_CHECKS.md` as a term with its verdict proved
(`account/LEAN_CASES.md`). Three things remain. The terms of A5 and A8 give verdicts that are
not the table's, on data of the cases that the table's script does not check. Eight terms
carry data their case does not supply, written with the table's verdict in view. And the
model is simpler than the statement in nine respects its header lists. Wanted: the two cases
and the eight restated so that each fixes its term; the simplifications removed or made
hypotheses. A Lean headline registers at merge.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/LEGITIMACY_STATEMENT.md`, `account/LEGITIMACY_CHECKS.md`, `account/legitimacy_checks.py`,
`account/LEAN_CASES.md`, `account/lean_cases.py` and `account/LEDGER.md` in the round directory;
`LegitimacyModel.lean`, `LegitimacyCase.lean`, `LegitimacyWitness.lean` and `LegitimacyCases.lean` under `lean/Workspace/Deference/Contrib/`.
*Consumed by:* items 150, 152 and 153, and the round that writes the account up.
