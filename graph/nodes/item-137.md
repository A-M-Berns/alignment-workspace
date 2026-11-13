---
id: item-137
kind: leaf
leaf_kind: task
action: "Execute item 137 per its deliverable shape and acceptance check: The aim-relative condition in Lean: legitimacy of one action against another, its strict implication from aim-freedom, and `legitScoring`."
who: agent
item: "137"
title: "The aim-relative condition in Lean: legitimacy of one action against another, its strict implication from aim-freedom, and `legitScoring`"
section: "Normativity line — legitimacy"
maintainer_order: 149
difficulty: "moderate"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`lean-proved` — a file under `lean/Workspace/Deference/Contrib/` (namespace provisional) with a `Candidate` structure, `best`, `gap`, and `LegitAgainst` (no part harmed, subverted or forced by one action against another); the lemma that `LegitAgainst a a'` gives every part a best at least, a gap at most and a got at least what it has under `a'`, with equality when each is legitimate against the other; the theorem that an adviser rule constant in its aim is legitimate at every aim; two instances showing the converse fails and that legitimacy at every aim neither implies nor follows from `ReasonMediatedAuthorship.SelectionBlind` of her evaluation; `legitScoring`, a `Scoring` from a decidable predicate, an evaluation in `[0, 1]` and a window in `[−δ, 0)`; a nonvacuity witness for each hypothesis package."
acceptance: "the `lean` job green: the build, `#print axioms` on every new declaration auditing to `[propext, Classical.choice, Quot.sound]`, and each witness typechecking; `conservativity` unchanged."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-10--legitimacy-prosecution-readings}
  - {kind: decision, ref: 2026-11-11--legitimacy-purpose-first-direction}
  - {kind: decision, ref: 2026-11-11--purpose-first-account-readings}
  - {kind: decision, ref: 2026-11-12--decomposition-account-readings}
  - {kind: decision, ref: 2026-11-12--scored-account-readings}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/scored/THEOREMS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/scored/ACCOUNT.md", "lean/Workspace/Deference/Contrib/TransparentChannel.lean", "lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean", "prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry, one fixture of context"
version: 4
---
## Statement
Item 137, The aim-relative condition in Lean: legitimacy of one action against another, its strict implication from aim-freedom, and `legitScoring`, is delivered in the shape its entry states: `lean-proved` — a file under `lean/Workspace/Deference/Contrib/` (namespace provisional) with a `Candidate` structure, `best`, `gap`, and `LegitAgainst` (no part harmed, subverted or forced by one action against another); the lemma that `LegitAgainst a a'` gives every part a best at least, a gap at most and a got at least what it has under `a'`, with equality when each is legitimate against the other; the theorem that an adviser rule constant in its aim is legitimate at every aim; two instances showing the converse fails and that legitimacy at every aim neither implies nor follows from `ReasonMediatedAuthorship.SelectionBlind` of her evaluation; `legitScoring`, a `Scoring` from a decidable predicate, an evaluation in `[0, 1]` and a window in `[−δ, 0)`; a nonvacuity witness for each hypothesis package.

## Source
ATTENTION.md, item 137 (The aim-relative condition in Lean: legitimacy of one action against another, its strict implication from aim-freedom, and `legitScoring`); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/scored/THEOREMS.md` (statements 5 and 9), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/scored/ACCOUNT.md` (§6 and §7), `lean/Workspace/Deference/Contrib/TransparentChannel.lean` (`Realizes`, `blind_of_realizes`, `selectionBlind_of_realizes`), `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean` (`Scoring`, `Decision`), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` (I3 and I4).

## Notes
Filed by the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution) under its prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py. Rewritten by that round's fourth follow-up (PROMPT-followup-4.md) under the ruling 2026-11-11--legitimacy-purpose-first-direction, to ask what the account of scored/ACCOUNT.md needs.

## Item
In the account of `scored/ACCOUNT.md` of the prosecution round an adviser is a rule from what it knows and
what it aims at to an action, and its influence on a part of the principal is illegitimate when the action
harms, subverts or forces that part against the action another aim would have taken. The fourth follow-up
proves on paper, and checks by enumeration on one scene, three things a kernel can hold
(`scored/THEOREMS.md`, statement 5): an action legitimate against another leaves every part with a best at
least, a gap at most and so a got at least what the other leaves it, with equality when each is legitimate
against the other; a rule that takes one action at every aim is legitimate at every aim; and the converse
fails, as does either implication between legitimacy at every aim and her evaluation being the same at
every aim (`ReasonMediatedAuthorship.SelectionBlind`, the conclusion of
`TransparentChannel.selectionBlind_of_realizes`). The witnesses are framing between options her goal ranks
equal, and a true statement given a false reason.

Wanted: those statements in Lean, with `legitScoring` as before. Everything about weights — which
candidate the predicate is evaluated under — waits on the ruling of what a purpose predicts (`DECISIONS.md`,
*Awaiting the author*, 2026-11-12) and on item 136, and is not part of this item

*Deliverable shape:* `lean-proved` — a file under `lean/Workspace/Deference/Contrib/` (namespace provisional) with a `Candidate` structure, `best`, `gap`, and `LegitAgainst` (no part harmed, subverted or forced by one action against another); the lemma that `LegitAgainst a a'` gives every part a best at least, a gap at most and a got at least what it has under `a'`, with equality when each is legitimate against the other; the theorem that an adviser rule constant in its aim is legitimate at every aim; two instances showing the converse fails and that legitimacy at every aim neither implies nor follows from `ReasonMediatedAuthorship.SelectionBlind` of her evaluation; `legitScoring`, a `Scoring` from a decidable predicate, an evaluation in `[0, 1]` and a window in `[−δ, 0)`; a nonvacuity witness for each hypothesis package.
*Acceptance check:* the `lean` job green: the build, `#print axioms` on every new declaration auditing to `[propext, Classical.choice, Quot.sound]`, and each witness typechecking; `conservativity` unchanged.
*Context:* `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/scored/THEOREMS.md` (statements 5 and 9), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/scored/ACCOUNT.md` (§6 and §7), `lean/Workspace/Deference/Contrib/TransparentChannel.lean` (`Realizes`, `blind_of_realizes`, `selectionBlind_of_realizes`), `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean` (`Scoring`, `Decision`), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` (I3 and I4).
