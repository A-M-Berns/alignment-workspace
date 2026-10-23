---
id: item-63
kind: leaf
leaf_kind: question
action: "Work PRIORITIES item 63: give Sigma_n as a computable deductive process or show where it fails to be."
who: agent
item: "63"
title: "`Sigma_n` as a computable deductive process"
section: "Normativity line — legitimacy"
maintainer_order: 39
difficulty: "open"
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`lean-proved` for the union case — given `ComputableDeductiveProcess D` and a primitive-recursive `sem_L` over an enumerable ledger, the union is a `ComputableDeductiveProcess`."
acceptance: "the `lean` job; the witness is a settled ledger with a decidable reading."
context: ["projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/SETTLEMENT_SEMANTICS.md"]
author: "@smithy-verity-opus55"
size: M
size_reason: "an open work order"
version: 1
---
## Statement
The deductive process Σ_n used by the repository's constructions is
computable.

## Source
PRIORITIES.md: "`Sigma_n` as a computable deductive process"

## Notes
PRIORITIES #63, open.

## Item
`IsLogicalInductor` is stated against a process carrying
`ComputableDeductiveProcess`. The slice's `Sigma_n = D_n union Sem_L(L_n)` is
computable by construction and no computability statement is made about it, so
E3 in the slice's assumption list is declared rather than discharged. The same
gap covers `RationalConstraintSchedule.Computation` for the schedules the slice
generates.

*Deliverable shape:* `lean-proved` for the union case — given
`ComputableDeductiveProcess D` and a primitive-recursive `sem_L` over an
enumerable ledger, the union is a `ComputableDeductiveProcess`.
*Acceptance check:* the `lean` job; the witness is a settled ledger with a
decidable reading.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/SETTLEMENT_SEMANTICS.md`
§1 and §9.
*Consumed by:* any round quoting `IsLogicalInductor` over a record-fed substrate.
