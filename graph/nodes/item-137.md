---
id: item-137
kind: leaf
leaf_kind: task
action: "Execute item 137 per its deliverable shape and acceptance check: The account's proved statements in Lean: no inflation, deferring, avoidable loss, drift between time-slices, and the true-score form of Theorem 3(b)."
who: agent
item: "137"
title: "The account's proved statements in Lean: no inflation, deferring, avoidable loss, drift between time-slices, and the true-score form of Theorem 3(b)"
section: "Normativity line — legitimacy"
maintainer_order: 149
difficulty: "moderate"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`lean-proved` — one file under `lean/Workspace/Deference/Contrib/`, in a contribution namespace, stating and proving on a finite probability space, with the workspace's `expectR`: statement 1.1 of `estimates/RESULTS.md` (the squared mean error of an estimate is at most its miscalibration, at any information); 1.2 (the loss of deciding now less the loss of deferring); 1.3 with the constant `√2` and the equality case of 1.4; 4.2 (the drift bound between two estimates of one quantity); 5.1; and, against `DeconfusingCorrigibility.Sequential`, `trueScore_noRegret` as stated in 1.11; each with a nonvacuity witness, the last on `Witness.sequential` with a true-utility sequence that differs from `V` at every step."
acceptance: "the `lean` job green on the file, sorry-free, with `#print axioms` on every declaration auditing to `[propext, Classical.choice, Quot.sound]`; a registered witness inhabiting each theorem's hypothesis package; `conservativity` unchanged."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-10--legitimacy-prosecution-readings}
  - {kind: decision, ref: 2026-11-11--legitimacy-purpose-first-direction}
  - {kind: decision, ref: 2026-11-11--purpose-first-account-readings}
  - {kind: decision, ref: 2026-11-12--decomposition-account-readings}
  - {kind: decision, ref: 2026-11-12--scored-account-readings}
  - {kind: decision, ref: 2026-11-13--blocks-setting-readings}
  - {kind: decision, ref: 2026-11-14--estimates-account-readings}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/RESULTS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/checks.py", "lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean", "lean/Workspace/Deference/Contrib/ThinLegitimacy.lean", "prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry, one fixture of context"
version: 6
---
## Statement
Item 137, The account's proved statements in Lean: no inflation, deferring, avoidable loss, drift between time-slices, and the true-score form of Theorem 3(b), is delivered in the shape its entry states: `lean-proved` — one file under `lean/Workspace/Deference/Contrib/`, in a contribution namespace, stating and proving on a finite probability space, with the workspace's `expectR`: statement 1.1 of `estimates/RESULTS.md` (the squared mean error of an estimate is at most its miscalibration, at any information); 1.2 (the loss of deciding now less the loss of deferring); 1.3 with the constant `√2` and the equality case of 1.4; 4.2 (the drift bound between two estimates of one quantity); 5.1; and, against `DeconfusingCorrigibility.Sequential`, `trueScore_noRegret` as stated in 1.11; each with a nonvacuity witness, the last on `Witness.sequential` with a true-utility sequence that differs from `V` at every step.

## Source
ATTENTION.md, item 137 (The account's proved statements in Lean: no inflation, deferring, avoidable loss, drift between time-slices, and the true-score form of Theorem 3(b)); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/RESULTS.md` (statements 1.1–1.4, 1.11, 1.12, 4.2, 5.1; question 7), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/checks.py` (`c1`, `c2`, `c3`, `c3_tight`, `c5`, `a_drift`, `b_bound`), `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean` (`Sequential`, `LimsupLE`, `theorem3b`, `Witness.sequential`), `lean/Workspace/Deference/Contrib/ThinLegitimacy.lean` (`Correct`, `Value`), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` (*Sixth follow-up*).

## Notes
Filed by the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution) under its prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py. Rewritten by that round's sixth follow-up (PROMPT-followup-6.md) under the ruling 2026-11-11--legitimacy-purpose-first-direction, to ask what the account of estimates/SETTING.md needs.

## Item
The sixth follow-up of the prosecution round proves on paper, and checks on seeded random finite cases,
the statements a kernel can hold (`estimates/RESULTS.md`). On a finite probability space, for an estimate `x`
of `X` and information `I`: `(E[x] − E[X])² ≤ E[(x − E[X | x, I])²]` (1.1). For a user with information `F`:
the loss of deciding now less the loss of deferring to `x` is
`E[(E[X|x,F] − E[X|F])²] − E[(x − E[X|x,F])²]` (1.2). For estimates `u_a` of `U*_a`, references
`ū_a = E[U*_a | F]`, `M = Σ_a E[(u_a − ū_a)²]` and regret `R = max_a u_a − u_chosen`:
`E[max_a ū_a − ū_chosen] ≤ E[R] + √(2M)`, with equality attained (1.3, 1.4). For two estimates of one
quantity with miscalibrations `m_0`, `m_T`: `|E u_T − E u_0| ≤ √m_0 + √m_T` (4.2). The expected long-run
inflation of a verdict is at most the root of its expected long-run miscalibration (5.1); for a realized
sequence it is not (5.5, a counterexample to carry as a witness). And in the sequential setting of
`DeconfusingCorrigibility.lean`, with a sequence `Ustar` and `LimsupLE` of the average of `V − Ustar` at
most `β`, the average of `U_k a'_k − (Ustar_k − λ N_k)` is `LimsupLE` at most `β` for every available
sequence (1.11, stated there in Lean syntax; the proof is `theorem3b` and `LimsupLE.add`).

Wanted: these in Lean, each with a witness. The belief side of the account is already there:
`ThinLegitimacy.Correct` is calibration at her information under the actual process and `Value` is warranted
self-trust (`estimates/RESULTS.md`, question 7); the port adds the squared-error forms and the true score,
and takes her true utility as a hypothesis of each statement that uses it

*Deliverable shape:* `lean-proved` — one file under `lean/Workspace/Deference/Contrib/`, in a contribution namespace, stating and proving on a finite probability space, with the workspace's `expectR`: statement 1.1 of `estimates/RESULTS.md` (the squared mean error of an estimate is at most its miscalibration, at any information); 1.2 (the loss of deciding now less the loss of deferring); 1.3 with the constant `√2` and the equality case of 1.4; 4.2 (the drift bound between two estimates of one quantity); 5.1; and, against `DeconfusingCorrigibility.Sequential`, `trueScore_noRegret` as stated in 1.11; each with a nonvacuity witness, the last on `Witness.sequential` with a true-utility sequence that differs from `V` at every step.
*Acceptance check:* the `lean` job green on the file, sorry-free, with `#print axioms` on every declaration auditing to `[propext, Classical.choice, Quot.sound]`; a registered witness inhabiting each theorem's hypothesis package; `conservativity` unchanged.
*Context:* `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/RESULTS.md` (statements 1.1–1.4, 1.11, 1.12, 4.2, 5.1; question 7), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/checks.py` (`c1`, `c2`, `c3`, `c3_tight`, `c5`, `a_drift`, `b_bound`), `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean` (`Sequential`, `LimsupLE`, `theorem3b`, `Witness.sequential`), `lean/Workspace/Deference/Contrib/ThinLegitimacy.lean` (`Correct`, `Value`), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` (*Sixth follow-up*).
