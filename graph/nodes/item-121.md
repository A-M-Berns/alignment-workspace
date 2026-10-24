---
id: item-121
kind: leaf
leaf_kind: task
action: "Execute item 121 per its deliverable shape and acceptance check: Transitive retirement, and the closure a settlement must carry."
who: agent
item: "121"
title: "Transitive retirement, and the closure a settlement must carry"
section: "Deference line — second wave"
maintainer_order: 114
difficulty: "entry"
heading_notes: " — *answered 2026-10-22: the grounded rule propagates retirement, vacuity, rebuttal and undercut along citation chains of every length without a closure on the settlement (`mem_survivors`)*"
project: normativity.seed
dispatchable: true
item_status: closed
deliverable: "the chosen rule as a `def`, the re-proved monotonicity lemmas, and the chain-of-three fixture under it."
acceptance: "Lean green; the round's `tests/run.py` extended and green."
context: ["DECISIONS.md", "projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/REBUTTAL.md"]
work:
  - {kind: decision, ref: 2026-10-21--rule-specialization-step-form-vacuity-before}
  - {kind: decision, ref: 2026-10-22--survivors-grounded-fixed-point-defeaters-shared}
author: "@smithy-verity"
size: M
size_reason: "one item entry of 151 words"
version: 1
---
## Statement
Item 121, Transitive retirement, and the closure a settlement must carry, is delivered in the shape its entry states: the chosen rule as a `def`, the re-proved monotonicity lemmas, and the chain-of-three fixture under it.

## Source
PRIORITIES.md, item 121 (Transitive retirement, and the closure a settlement must carry); its context: `projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/REBUTTAL.md` A1; `DECISIONS.md` 2026-10-21 (M2).

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The rule `settleForm` (`lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean`,
`Grounds.survivors`) retires a premise whose sentence is pinned false and removes, one step
along `cites`, the occurrences that cite it; conditional forms further down a chain leave
only when the settlement's closure pins their antecedent false. The round's fixtures carry
their closure (`X` false pins `X∧A`, `X∧A∧Y` false) and the rule reaches the whole warrant;
without closure a chain of three keeps its last link
(`projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/tests/test_rebuttal.py::test_retirement_needs_closure`). Wanted: either the transitive
closure of citation as the retirement rule (a terminating recursion on the finite grounds,
with `survivors_anti` re-proved), or the closure requirement on settlements as a stated
hypothesis of the statics, with the theorem that a propositionally closed settlement makes
the one-step rule complete.

*Deliverable shape:* the chosen rule as a `def`, the re-proved monotonicity lemmas, and the
chain-of-three fixture under it.
*Acceptance check:* Lean green; the round's `tests/run.py` extended and green.
*Context:* `projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/REBUTTAL.md` A1; `DECISIONS.md` 2026-10-21 (M2).
