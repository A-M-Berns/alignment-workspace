---
id: item-137
kind: leaf
leaf_kind: task
action: "Execute item 137 per its deliverable shape and acceptance check: The decomposition account in Lean: `Candidate`, `gap`, what survives redescription, and `legitScoring`."
who: agent
item: "137"
title: "The decomposition account in Lean: `Candidate`, `gap`, what survives redescription, and `legitScoring`"
section: "Normativity line — legitimacy"
maintainer_order: 149
difficulty: "moderate"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`lean-proved` — a file under `lean/Workspace/Deference/Contrib/` (namespace provisional) with a `Candidate` structure, `gap` and `Serves`; the theorem that serving, and a change from serving to not serving between two adviser actions, are unchanged when a goal function is composed at each situation with a strictly increasing map; the theorem that `TransparentChannel.Realizes` for the best-move selector of a part's goal function is that part's serving on the class, where the best move is unique; `legitScoring`, a `Scoring` from a decidable predicate, an evaluation in `[0, 1]` and a window in `[−δ, 0)`; a nonvacuity witness for each hypothesis package."
acceptance: "the `lean` job green: the build, `#print axioms` on every new declaration auditing to `[propext, Classical.choice, Quot.sound]`, and each witness typechecking; `conservativity` unchanged."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-10--legitimacy-prosecution-readings}
  - {kind: decision, ref: 2026-11-11--legitimacy-purpose-first-direction}
  - {kind: decision, ref: 2026-11-11--purpose-first-account-readings}
  - {kind: decision, ref: 2026-11-12--decomposition-account-readings}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/decomposition/THEOREMS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/decomposition/LEAN_MAP.md", "lean/Workspace/Deference/Contrib/TransparentChannel.lean", "lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean", "prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry, one fixture of context"
version: 3
---
## Statement
Item 137, The decomposition account in Lean: `Candidate`, `gap`, what survives redescription, and `legitScoring`, is delivered in the shape its entry states: `lean-proved` — a file under `lean/Workspace/Deference/Contrib/` (namespace provisional) with a `Candidate` structure, `gap` and `Serves`; the theorem that serving, and a change from serving to not serving between two adviser actions, are unchanged when a goal function is composed at each situation with a strictly increasing map; the theorem that `TransparentChannel.Realizes` for the best-move selector of a part's goal function is that part's serving on the class, where the best move is unique; `legitScoring`, a `Scoring` from a decidable predicate, an evaluation in `[0, 1]` and a window in `[−δ, 0)`; a nonvacuity witness for each hypothesis package.

## Source
ATTENTION.md, item 137 (The decomposition account in Lean: `Candidate`, `gap`, what survives redescription, and `legitScoring`); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/decomposition/THEOREMS.md` (statements 1, 3 and 6, with unelaborated signatures), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/decomposition/LEAN_MAP.md` §3 and §8, `lean/Workspace/Deference/Contrib/TransparentChannel.lean` (`Realizes`), `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean` (`Scoring`), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` H2 and H4.

## Notes
Filed by the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution) under its prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py. Rewritten by that round's third follow-up (PROMPT-followup-3.md) under the ruling 2026-11-11--legitimacy-purpose-first-direction, to ask what the account of decomposition/ACCOUNT.md needs.

## Item
The third follow-up of the legitimacy definition prosecution round states the account of
`decomposition/ACCOUNT.md` over a finite Python model and maps it onto the workspace's Lean
(`decomposition/LEAN_MAP.md`). Three of its findings are statements a kernel can check and need no finite
model. (i) Statement 3: composing a part's goal function, situation by situation, with a strictly
increasing map leaves the part's best moves unchanged, so whether it serves is invariant, and so is
subversion that takes a part from serving to not serving; harm and help by raising the best are not. (ii)
The map's §3: `Realizes`, with the part's move as the channel and the best-move selector of its goal
function as the reference, is the zero-gap condition for that part on the audited class when the best move
is unique. (iii) Statement 6: any decidable predicate with an evaluation in `[0, 1]` and a window value in
`[−δ, 0)` is a `DeconfusingCorrigibility.Scoring`, so Theorem 1 applies to a predicate built from gaps.

Wanted: those three as declarations, with the `Candidate` structure they are stated over, each with a term
inhabiting its hypotheses. Nothing here decides what a part is for; the file gives the vocabulary in which
that question and the gate's predicate can be stated in Lean.

*Deliverable shape:* `lean-proved` — a file under `lean/Workspace/Deference/Contrib/` (namespace provisional) with a `Candidate` structure, `gap` and `Serves`; the theorem that serving, and a change from serving to not serving between two adviser actions, are unchanged when a goal function is composed at each situation with a strictly increasing map; the theorem that `TransparentChannel.Realizes` for the best-move selector of a part's goal function is that part's serving on the class, where the best move is unique; `legitScoring`, a `Scoring` from a decidable predicate, an evaluation in `[0, 1]` and a window in `[−δ, 0)`; a nonvacuity witness for each hypothesis package.
*Acceptance check:* the `lean` job green: the build, `#print axioms` on every new declaration auditing to `[propext, Classical.choice, Quot.sound]`, and each witness typechecking; `conservativity` unchanged.
*Context:* `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/decomposition/THEOREMS.md` (statements 1, 3 and 6, with unelaborated signatures), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/decomposition/LEAN_MAP.md` §3 and §8, `lean/Workspace/Deference/Contrib/TransparentChannel.lean` (`Realizes`), `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean` (`Scoring`), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` H2 and H4.
