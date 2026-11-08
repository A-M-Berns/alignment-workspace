---
id: item-133
kind: leaf
leaf_kind: task
action: "State the robust reading of a warrant as a Form-level rule — a constraint on the model over the undefeated extensions of its anchor — give its compile to rows, and prove it agrees with settleForm where the extension set is settlement-generated."
who: agent
item: "133"
title: "The robust reading of a warrant as a Form-level rule"
section: "Deference line — second wave"
maintainer_order: 143
difficulty: "open"
heading_notes: ""
project: normativity
dispatchable: true
item_status: open
deliverable: "`lean-proved`; the rule on `Form`, its compile, the agreement theorem with `settleForm` on settlement-generated extensions, and the eight-world fixture recovered under the rule."
acceptance: "the Lean audit clean; `RobustWarrant.robustStrength_all`, `robust_sound` and `WarrantSolvency.suspect_in_bundle` recovered as instances; `WarrantInductorWitness.survivors_eq` unchanged."
work:
  - {kind: decision, ref: open--exposure-rule-proposal}
  - {kind: decision, ref: 2026-11-07--conduct-binds-on-score-warrants-on-prices}
context: ["lean/Workspace/Normativity/Contrib/RobustWarrant.lean", "lean/Workspace/Normativity/Contrib/WarrantSolvency.lean", "projects/normativity/rounds/2026-11-07-score-side-binding/REPORT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry, two Lean modules of context"
version: 1
---
## Statement
Item 133, The robust reading of a warrant as a Form-level rule, is delivered in the shape its entry states: `lean-proved`; the rule on `Form`, its compile, the agreement theorem with `settleForm` on settlement-generated extensions, and the eight-world fixture recovered under the rule.

## Source
ATTENTION.md, item 133 (The robust reading of a warrant as a Form-level rule); its context: `lean/Workspace/Normativity/Contrib/RobustWarrant.lean`, `lean/Workspace/Normativity/Contrib/WarrantSolvency.lean`, the score-side-binding round's report.

## Notes
Filed by the score-side-binding round (prompts/2026-11-07-score-side-binding), which proved the fixture and the definition; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
A strength row `P(X∧A∧Y) ≥ c · P(X∧A)` read at the posterior of whatever record the warrant is
undefeated at can be false while nothing withdraws it: on the eight-world model
(`RobustWarrant`) the row at `3/4` is exact at the signal and false after a contrary challenge,
`settleOutcome` keeps the form because the challenge pins neither antecedent nor consequent,
the quiet docket undercuts nothing, and registering the challenge as an opposing warrant makes
the rows infeasible although the answer `3/5` is determinate. The repair the round defines is
the **robust reading** (`RobustWarrant.Robust`): the warrant constrains her model over the
undefeated extensions of its anchor, `Pr(Y | A ∧ E) ≥ c` for every undefeated `E`; its
strength is the least such conditional (`3/5` here, `3/4` with the contrary challenge a
defeater), it is sound at every undefeated record (`robust_sound`), and sound rows cannot
conflict (`WarrantSolvency.suspect_in_bundle`), so a valid conflict certificate under it proves a
mis-admission. Wanted: the reading as a rule on `Form` with its compile to rows; the theorem
that it agrees with `settleForm` when the extension set is the one the settlement generates;
and the fixture recovered under the rule. What is settled is the fixture and the definition;
no general defeat semantics is built here.

*Deliverable shape:* `lean-proved`; the rule on `Form`, its compile, the agreement theorem with
`settleForm` on settlement-generated extensions, and the eight-world fixture recovered under
the rule.
*Acceptance check:* the Lean audit clean; `RobustWarrant.robustStrength_all`, `robust_sound`
and `WarrantSolvency.suspect_in_bundle` recovered as instances;
`WarrantInductorWitness.survivors_eq` unchanged.
*Context:* `lean/Workspace/Normativity/Contrib/RobustWarrant.lean`;
`lean/Workspace/Normativity/Contrib/WarrantSolvency.lean`;
`projects/normativity/rounds/2026-11-07-score-side-binding/REPORT.md`.
*Consumed by:* item 127 (an undercutter that is itself defeasible is an extension this reading
prices); the queue entries on M1 and M2.
