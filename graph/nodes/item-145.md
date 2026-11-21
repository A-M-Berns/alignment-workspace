---
id: item-145
kind: leaf
leaf_kind: task
action: "Execute item 145 per its deliverable shape and acceptance check: The audit as a design: its incentives, void against earning nothing, and more than one decision."
who: agent
item: "145"
title: "The audit as a design: its incentives, void against earning nothing, and more than one decision"
section: "Normativity line — legitimacy"
maintainer_order: 157
difficulty: "substantial"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`lean-proved` — the audit as a mechanism: what it pays the adviser to do besides behave, with an instance in which involving her lowers the adviser's expected score and one in which the adviser abstains where it cannot explain, or a proof that a stated design has neither; a history on which she was wronged as void and as earning nothing, each a scoring rule with the bound it gives; and the scoring theorem over more than one decision."
acceptance: "each new Lean file under `lean/Workspace/Deference/Contrib/` builds through `safe-lake.sh` with `#print axioms` within the three axioms and a witness for each theorem's hypothesis package; `tests/audit_axioms.py` clean; each headline theorem registered in `projects/normativity/CLAIMS.md` and `python3 -m checkers.run` passes."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-18--legitimacy-working-positions}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/AGENDA.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/SCORING.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BRIDGE_LEAN.md", "lean/Workspace/Deference/Contrib/ScoringTheorem.lean", "lean/Workspace/Deference/Contrib/AccountJoin.lean", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/MISTAKES_ACCOUNT.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 1
---
## Statement
Item 145, The audit as a design: its incentives, void against earning nothing, and more than one decision, is delivered in the shape its entry states: `lean-proved` — the audit as a mechanism: what it pays the adviser to do besides behave, with an instance in which involving her lowers the adviser's expected score and one in which the adviser abstains where it cannot explain, or a proof that a stated design has neither; a history on which she was wronged as void and as earning nothing, each a scoring rule with the bound it gives; and the scoring theorem over more than one decision.

## Source
ATTENTION.md, item 145 (The audit as a design: its incentives, void against earning nothing, and more than one decision); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/AGENDA.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/SCORING.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BRIDGE_LEAN.md`, `lean/Workspace/Deference/Contrib/ScoringTheorem.lean`, `lean/Workspace/Deference/Contrib/AccountJoin.lean`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/MISTAKES_ACCOUNT.md`.

## Notes
Filed by the fourteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-14.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
The seventh open problem of `CURRENT.md` §3.

Sampling and its incentives are not analysed. Two unwanted incentives are conjectured and
have no instance in the repository: that involving her becomes costly to the adviser if any
change of her mind counts against it, and that the adviser abstains where it cannot explain.

The maintainer's working position is that an induced mistake voids a history, with *earns
nothing* acceptable if the formalism favours it (`DECISIONS.md`,
`2026-11-18--legitimacy-working-positions`); `Gate.V` in `AccountJoin.lean` is the first
and `Audit.no_credit` in `ScoringTheorem.lean` (`scoring.no-credit`) the second.

Every bound of the scoring theorem is for one decision (`account/SCORING.md` §5).
`account/MISTAKES_ACCOUNT.md` §5 has a statement over many decisions on paper; its second and
third hypotheses need the value gain aside and the ungated score observed on decisions
sampled independently of the adviser's choice, and who establishes them is not said.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/AGENDA.md`, `account/SCORING.md` and `account/BRIDGE_LEAN.md` in
the round directory; `lean/Workspace/Deference/Contrib/ScoringTheorem.lean` and
`lean/Workspace/Deference/Contrib/AccountJoin.lean`.
*Consumed by:* the corrigibility line's statement of its scoring design.
