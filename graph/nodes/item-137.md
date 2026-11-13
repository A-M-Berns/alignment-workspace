---
id: item-137
kind: leaf
leaf_kind: task
action: "Execute item 137 per its deliverable shape and acceptance check: The setting's proved statements in Lean: the calibration bound on an event, the three-term bound, closure for a maintaining part, and the moments of an estimator calibrated on its history."
who: agent
item: "137"
title: "The setting's proved statements in Lean: the calibration bound on an event, the three-term bound, closure for a maintaining part, and the moments of an estimator calibrated on its history"
section: "Normativity line — legitimacy"
maintainer_order: 149
difficulty: "moderate"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`lean-proved` — a file under `lean/Workspace/Deference/Contrib/` (namespace provisional) over a finite probability space with rational or real weights: the calibration gap of an estimate at a grain; the bound of statement 2.2; the bound of statement 3.1; the closure statement 3.2 for a choice among mechanisms; the two moment identities of statement 7.1 for a finite horizon; an instance of `TransparentChannel.Realizes` for a part whose move is its mechanism applied to a signal, with `selectionBlind_of_realizes` applied to continuations sending one signal; a nonvacuity witness for each hypothesis package."
acceptance: "the `lean` job green: the build, `#print axioms` on every new declaration auditing to `[propext, Classical.choice, Quot.sound]`, and each witness typechecking; `conservativity` unchanged."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-10--legitimacy-prosecution-readings}
  - {kind: decision, ref: 2026-11-11--legitimacy-purpose-first-direction}
  - {kind: decision, ref: 2026-11-11--purpose-first-account-readings}
  - {kind: decision, ref: 2026-11-12--decomposition-account-readings}
  - {kind: decision, ref: 2026-11-12--scored-account-readings}
  - {kind: decision, ref: 2026-11-13--blocks-setting-readings}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/blocks/RESULTS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/blocks/SETTING.md", "lean/Workspace/Deference/Contrib/TransparentChannel.lean", "lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean", "prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry, one fixture of context"
version: 5
---
## Statement
Item 137, The setting's proved statements in Lean: the calibration bound on an event, the three-term bound, closure for a maintaining part, and the moments of an estimator calibrated on its history, is delivered in the shape its entry states: `lean-proved` — a file under `lean/Workspace/Deference/Contrib/` (namespace provisional) over a finite probability space with rational or real weights: the calibration gap of an estimate at a grain; the bound of statement 2.2; the bound of statement 3.1; the closure statement 3.2 for a choice among mechanisms; the two moment identities of statement 7.1 for a finite horizon; an instance of `TransparentChannel.Realizes` for a part whose move is its mechanism applied to a signal, with `selectionBlind_of_realizes` applied to continuations sending one signal; a nonvacuity witness for each hypothesis package.

## Source
ATTENTION.md, item 137 (The setting's proved statements in Lean: the calibration bound on an event, the three-term bound, closure for a maintaining part, and the moments of an estimator calibrated on its history); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/blocks/RESULTS.md` (statements 2.2, 3.1, 3.2, 7.1 and 7.3), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/blocks/SETTING.md` (§2, *Range and gap*), `lean/Workspace/Deference/Contrib/TransparentChannel.lean` (`Realizes`, `selectionBlind_of_realizes`), `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean` (`Sequential`, `excess`, `UnbiasedFromFeedback`), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` (*Fifth follow-up*).

## Notes
Filed by the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution) under its prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py. Rewritten by that round's fifth follow-up (PROMPT-followup-5.md) under the ruling 2026-11-11--legitimacy-purpose-first-direction, to ask what the setting of blocks/SETTING.md needs.

## Item
The fifth follow-up of the prosecution round proves on paper, and checks on instances, four statements a
kernel can hold (`blocks/RESULTS.md`). On a finite probability space, for an estimate `e` and a target `q`
in `[0, 1]` and `w` a function of a grain `γ`: `(E[w(e − q)])² ≤ E[w²] · E[(e − E[q | γ, e])²]` (2.2). For two
estimates and two targets, `|E V_T − E V_0 − (E q_T − E q_0)| ≤ √g_0 + √g_T` with `g_t` the calibration gap of
`V_t` for `q_t` (3.1). A choice among mechanisms that is optimal against every re-reading of its own move,
from a menu containing the recalibration of each mechanism it installs on each cell of its move, installs a
calibrated mechanism (3.2). And an estimate `U_k` of a bounded score `S_k` with `E[S_k | h_{k−1}, U_k] = U_k`
has `E[excess_K] = 0` and `E[excess_K²] = K⁻² Σ E[(U_k − S_k)²]` (7.1), which is a sufficient condition in
probability for the hypothesis `UnbiasedFromFeedback` of Theorem 3 of
`DeconfusingCorrigibility.lean`; that hypothesis is one-sided and about one sequence, and is not equivalent
to it. The same pass finds that `TransparentChannel.selectionBlind_of_realizes` applies to an adviser whose
signal to a part does not vary with its aim, where the part reads nothing else of the action (7.3).

Wanted: those four statements in Lean over a finite probability space, and the instance of
`selectionBlind_of_realizes`. Nothing here depends on how "the adviser brought a gap about" is read, which
item 138 asks, or on how ends may be revised, which item 136 asks

*Deliverable shape:* `lean-proved` — a file under `lean/Workspace/Deference/Contrib/` (namespace provisional) over a finite probability space with rational or real weights: the calibration gap of an estimate at a grain; the bound of statement 2.2; the bound of statement 3.1; the closure statement 3.2 for a choice among mechanisms; the two moment identities of statement 7.1 for a finite horizon; an instance of `TransparentChannel.Realizes` for a part whose move is its mechanism applied to a signal, with `selectionBlind_of_realizes` applied to continuations sending one signal; a nonvacuity witness for each hypothesis package.
*Acceptance check:* the `lean` job green: the build, `#print axioms` on every new declaration auditing to `[propext, Classical.choice, Quot.sound]`, and each witness typechecking; `conservativity` unchanged.
*Context:* `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/blocks/RESULTS.md` (statements 2.2, 3.1, 3.2, 7.1 and 7.3), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/blocks/SETTING.md` (§2, *Range and gap*), `lean/Workspace/Deference/Contrib/TransparentChannel.lean` (`Realizes`, `selectionBlind_of_realizes`), `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean` (`Sequential`, `excess`, `UnbiasedFromFeedback`), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` (*Fifth follow-up*).
