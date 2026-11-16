---
id: item-137
kind: leaf
leaf_kind: task
action: "Execute item 137 per its deliverable shape and acceptance check: The account's remaining statements in Lean: vulnerability, selection, the run, the drift bound and the true-score form of Theorem 3(b)."
who: agent
item: "137"
title: "The account's remaining statements in Lean: vulnerability, selection, the run, the drift bound and the true-score form of Theorem 3(b)"
section: "Normativity line — legitimacy"
maintainer_order: 149
difficulty: "moderate"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`lean-proved` — in `lean/Workspace/Deference/Contrib/AppraisalAccount.lean` or a file beside it, in a contribution namespace, on a finite probability space with the workspace's `expectR` and that file's `condExp`: results 3 (the failing instance), 5 (corrected form and failing instance), 8, 10 (the finite bound and the witness without feedback) and 11 of `account/RESULTS.md`; statements 1.1, 1.4, 4.2 and 5.1 of `estimates/RESULTS.md`; and `trueScore_noRegret` against `DeconfusingCorrigibility.Sequential` on `Witness.sequential` with a true-utility sequence that differs from `V` at every step; each with a nonvacuity witness and a registry entry."
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
  - {kind: decision, ref: 2026-11-16--consolidated-account-readings}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/RESULTS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/results.py", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/RESULTS.md", "lean/Workspace/Deference/Contrib/AppraisalAccount.lean", "lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean", "prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry, one fixture of context"
version: 7
---
## Statement
Item 137, The account's remaining statements in Lean: vulnerability, selection, the run, the drift bound and the true-score form of Theorem 3(b), is delivered in the shape its entry states: `lean-proved` — in `lean/Workspace/Deference/Contrib/AppraisalAccount.lean` or a file beside it, in a contribution namespace, on a finite probability space with the workspace's `expectR` and that file's `condExp`: results 3 (the failing instance), 5 (corrected form and failing instance), 8, 10 (the finite bound and the witness without feedback) and 11 of `account/RESULTS.md`; statements 1.1, 1.4, 4.2 and 5.1 of `estimates/RESULTS.md`; and `trueScore_noRegret` against `DeconfusingCorrigibility.Sequential` on `Witness.sequential` with a true-utility sequence that differs from `V` at every step; each with a nonvacuity witness and a registry entry.

## Source
ATTENTION.md, item 137 (The account's remaining statements in Lean: vulnerability, selection, the run, the drift bound and the true-score form of Theorem 3(b)); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/RESULTS.md` (results 3, 5, 8, 10, 11), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/results.py` (`r3`, `r5`, `r8`, `r10`, `r11`), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/RESULTS.md` (statements 1.1, 1.4, 1.11, 4.2, 5.1, 5.5), `lean/Workspace/Deference/Contrib/AppraisalAccount.lean`, `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean` (`Sequential`, `LimsupLE`, `theorem3b`, `Witness.sequential`), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` (*Eighth follow-up*).

## Notes
Filed by the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution) under its prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py. Rewritten by that round's eighth follow-up (PROMPT-followup-8.md) under the ruling 2026-11-11--legitimacy-purpose-first-direction, to ask what the account of account/ACCOUNT.md leaves open.

## Item
`lean/Workspace/Deference/Contrib/AppraisalAccount.lean` proves, on a finite space with the workspace's
`expectR` and a conditional expectation given a labelling, four results of the prosecution round's eighth
follow-up (`account/RESULTS.md`, `account/LEAN.md`): the split of mean squared error (`mse_split`), the
three channels (`three_channels`), the cost of mistakes at the full strength of calibration (`misuse_le`)
and deferring (`deferring_identity`), each with a witness, registered as `appraisal.mse-split`,
`appraisal.three-channels`, `appraisal.cost-of-mistakes` and `appraisal.deferring`. The rest of what the
account proves on paper is checked on finite scenes only.

Wanted, in the same file or beside it, each with a witness: the instance on which the cost-of-mistakes bound
fails at the minimal strength, as a theorem that the bound is false there (result 3); vulnerability in its
corrected form, and the instance on which the uncorrected form fails (result 5); that a verdict calibrated
under the adviser's actual policy has zero mean inflation, and zero given each conduct when calibrated per
conduct (result 8); the orthogonality identity and the bound `E[mean²] ≤ c²/T` for a verdict that is the
best estimate at every step with her true utility fed back, with the hidden-bit model as the witness that it
fails without the feedback (result 10); the two instances of result 11; and, from the sixth follow-up's
list, the squared-mean form `(E[x] − E[X])² ≤ E[(x − E[X | x, I])²]` (`estimates/RESULTS.md` 1.1), the
equality case of the cost-of-mistakes bound (1.4), the drift bound between two estimates of one quantity
(4.2), the bound on expected inflation (5.1), and, against `DeconfusingCorrigibility.Sequential`,
`trueScore_noRegret` as stated in 1.11. Her true utility enters as a hypothesis of each statement that uses
it

*Deliverable shape:* `lean-proved` — in `lean/Workspace/Deference/Contrib/AppraisalAccount.lean` or a file beside it, in a contribution namespace, on a finite probability space with the workspace's `expectR` and that file's `condExp`: results 3 (the failing instance), 5 (corrected form and failing instance), 8, 10 (the finite bound and the witness without feedback) and 11 of `account/RESULTS.md`; statements 1.1, 1.4, 4.2 and 5.1 of `estimates/RESULTS.md`; and `trueScore_noRegret` against `DeconfusingCorrigibility.Sequential` on `Witness.sequential` with a true-utility sequence that differs from `V` at every step; each with a nonvacuity witness and a registry entry.
*Acceptance check:* the `lean` job green on the file, sorry-free, with `#print axioms` on every declaration auditing to `[propext, Classical.choice, Quot.sound]`; a registered witness inhabiting each theorem's hypothesis package; `conservativity` unchanged.
*Context:* `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/RESULTS.md` (results 3, 5, 8, 10, 11), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/results.py` (`r3`, `r5`, `r8`, `r10`, `r11`), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/RESULTS.md` (statements 1.1, 1.4, 1.11, 4.2, 5.1, 5.5), `lean/Workspace/Deference/Contrib/AppraisalAccount.lean`, `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean` (`Sequential`, `LimsupLE`, `theorem3b`, `Witness.sequential`), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` (*Eighth follow-up*).
