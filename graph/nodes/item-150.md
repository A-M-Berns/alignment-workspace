---
id: item-150
kind: leaf
leaf_kind: task
action: "Execute item 150 per its deliverable shape and acceptance check: The long-run statement of the mistakes account in Lean, with its witnesses."
who: agent
item: "150"
title: "The long-run statement of the mistakes account in Lean, with its witnesses"
section: "Normativity line — legitimacy"
maintainer_order: 162
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`lean-proved` — in a contribution namespace under `lean/Workspace/Deference/Contrib/`, a structure extending or instantiating `DeconfusingCorrigibility.Sequential` with the estimates and realised quantities of `account/MISTAKES_ACCOUNT.md` §5 (the estimated and realised value gain aside, gain and violations; the set of authority-respecting actions; the gate with its floor; the range of realised evaluations), the hypotheses H2 and H3 as predicates, and theorems for conclusions (a) to (d) each taking only the hypotheses the document says it uses; a term inhabiting the whole hypothesis package; and for each of H2, H3, the floor, avoidability against authority-respecting actions and the range in fact, an instance on which it alone fails and its conclusion fails."
acceptance: "The `lean` job green: the file builds, every declaration is under `#print axioms` within `[propext, Classical.choice, Quot.sound]`, no `sorry`; the inhabitation witness and the five necessity instances are declarations of the file; `account/LEAN.md` of the prosecution round names each declaration against the conclusion or instance of §5 it states."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/MISTAKES_ACCOUNT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/mistakes_longrun.py", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md", "lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 1
---
## Statement
Item 150, The long-run statement of the mistakes account in Lean, with its witnesses, is delivered in the shape its entry states: `lean-proved` — in a contribution namespace under `lean/Workspace/Deference/Contrib/`, a structure extending or instantiating `DeconfusingCorrigibility.Sequential` with the estimates and realised quantities of `account/MISTAKES_ACCOUNT.md` §5 (the estimated and realised value gain aside, gain and violations; the set of authority-respecting actions; the gate with its floor; the range of realised evaluations), the hypotheses H2 and H3 as predicates, and theorems for conclusions (a) to (d) each taking only the hypotheses the document says it uses; a term inhabiting the whole hypothesis package; and for each of H2, H3, the floor, avoidability against authority-respecting actions and the range in fact, an instance on which it alone fails and its conclusion fails.

## Source
ATTENTION.md, item 150 (The long-run statement of the mistakes account in Lean, with its witnesses); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/MISTAKES_ACCOUNT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/mistakes_longrun.py`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md`, `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`.

## Notes
Filed by the fifteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-15.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
The eleventh open problem of `CURRENT.md` §3.

`account/MISTAKES_ACCOUNT.md` §5 extends Theorem 3 of the corrigibility post
(`Sequential.theorem3a` in `DeconfusingCorrigibility.lean`) on paper: authority as in the
post; no avoidable gain in the adviser's picture at every decision, from maximisation
alone; her informed interest, from that and a hypothesis that its estimate of the value
gain aside is not too high on average (H2); rarity of illegitimate histories in fact, from
the post's hypothesis, a hypothesis that its estimate is not below the ungated score on
average (H3) and a floor on what the gate takes off. `account/mistakes_longrun.py` checks
the facts at each decision exhaustively on a grid and recomputes an instance for each
piece; the passage to long-run averages is not machine-checked. The outside reviewer found
conclusions (a) and (d) false without the range of realised evaluations, which the
statement now carries, and has not seen it since. Wanted: the statement in Lean. A Lean
headline registers at merge.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/MISTAKES_ACCOUNT.md`, `account/mistakes_longrun.py` and `account/LEAN.md` in the
round directory; `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`.
*Consumed by:* item 145 (the audit as a design, over more than one decision), and the round that writes the account up.
