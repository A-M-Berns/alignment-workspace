---
id: item-136
kind: leaf
leaf_kind: task
action: "Execute item 136 per its deliverable shape and acceptance check: The equivalence forms of factorization: sufficiency, betting, offers-only."
who: agent
item: "136"
title: "The equivalence forms of factorization: sufficiency, betting, offers-only"
section: "Normativity line — legitimacy"
maintainer_order: 148
difficulty: "substantial"
heading_notes: ""
project: normativity.legitimacy
dispatchable: false
item_status: open
deliverable: "`test-supported` at the ceiling — one module per form in the prosecution round's layout, each claimed equivalence a pointwise check over the frozen bank and each separation a named case; a Lean port is a later item."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with the forms' modules wired in; every equivalence checked pointwise over the bank, every separation a banked case."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-10--legitimacy-prosecution-readings}
  - {kind: decision, ref: 2026-11-10--steering-follow-up-stipulations}
context: ["prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CASE_BANK.md", "prompts/2026-11-10-legitimacy-definition-prosecution/PROMPT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry, one fixture of context"
version: 1
---
## Statement
Item 136, The equivalence forms of factorization: sufficiency, betting, offers-only, is delivered in the shape its entry states: `test-supported` at the ceiling — one module per form in the prosecution round's layout, each claimed equivalence a pointwise check over the frozen bank and each separation a named case; a Lean port is a later item.

## Source
ATTENTION.md, item 136 (The equivalence forms of factorization: sufficiency, betting, offers-only); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CASE_BANK.md`, `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` §3 (the replay form), the prompt's §6, `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` F4–F5 (C5, C6).

## Notes
Filed by the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution) under its prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
**Waits on the second follow-up of the legitimacy definition prosecution round** (`prompts/2026-11-10-legitimacy-definition-prosecution/PROMPT-followup-2.md`). The ruling `2026-11-11--legitimacy-purpose-first-direction` in `DECISIONS.md` set aside the mathematics this entry was filed against, and the entry is not dispatchable as written; what it asks of the purpose-first account is stated when that pass's results are in.

The prosecution round states L1 in its pairwise form — over a named class `V`, coupled runs with
equal licensed traces have equal `Z`-traces — which is equivalent to the existence of some `F`
with `Z* = F(e, L)` on `V` and says nothing about `F`. Three other forms were named and none
proved: a sufficiency form (`L` a sufficient statistic for `Z*` given `e` over the class); a
betting form (no policy in `V` moves `Z*` beyond what its licensed trace buys); an offers-only
normal form (every `π` in `V` has an offerings-only `π'` with the same licensed trace and the
same `Z*`). The round's fixture also exhibits the canonical replay `F` — the principal run with
the advisor replaced by a player of the licensed trace — and finds `Z* = F_replay(e, L)` to be a
single-run condition that by itself convicts B1, B2, B3, T1, T4, T5 and T10, absorbing L0 and L3
on the frozen bank; the pairwise form keeps them separate. Wanted: each form stated over the
round's finite objects, and for each either an equivalence to the pairwise form over the bank or
the fixture separating them — in particular whether the replay form is the sufficiency form, and
what it says of T2, where the accepted option is licensed content.

The round's steering follow-up computed the replay form against L1, L0–L3 ∧ W and its two
standards over 38 variants (`steering/THEOREMS.md`, C5 and C6): the replay form is comparable
with none of them, and it fails on a write the principal authorized in advance (N5), which is
not in `L`. Wanted in addition: whether an authorized write belongs in the licensed trace, and
the replay form restated accordingly.

*Deliverable shape:* `test-supported` at the ceiling — one module per form in the prosecution round's layout, each claimed equivalence a pointwise check over the frozen bank and each separation a named case; a Lean port is a later item.
*Acceptance check:* `python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with the forms' modules wired in; every equivalence checked pointwise over the bank, every separation a banked case.
*Context:* `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CASE_BANK.md`, `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` §3 (the replay form), the prompt's §6, `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` F4–F5 (C5, C6).
