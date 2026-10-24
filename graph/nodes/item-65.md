---
id: item-65
kind: leaf
leaf_kind: task
action: "Execute item 65 per its deliverable shape and acceptance check: Whether `L_min(V)` is needed in its strong form."
who: agent
item: "65"
title: "Whether `L_min(V)` is needed in its strong form"
section: "Normativity line — legitimacy"
maintainer_order: 41
difficulty: "entry"
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "either such a case, with what it forces `L_min(V)` to contain, or an argument that the weak relationship is closed under the architecture's operations."
acceptance: "the slice's compiler runs on the case unchanged, or the round states exactly which of its functions must newly read `V`."
context: ["projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/FINDINGS.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry of 171 words"
version: 1
---
## Statement
Item 65, Whether `L_min(V)` is needed in its strong form, is delivered in the shape its entry states: either such a case, with what it forces `L_min(V)` to contain, or an argument that the weak relationship is closed under the architecture's operations.

## Source
PRIORITIES.md, item 65 (Whether `L_min(V)` is needed in its strong form); its context: `projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/FINDINGS.md` §3.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The slice never required an LI sentence whose meaning is a reason: reasons are
consumed by identifier comparison and the compiler never sees `V`. So the
relationship it used is weaker than `L in Ext(L_min(V))` — `L` must code the
value layer's query vocabulary and the settlement layer's readings, and `V` is
otherwise opaque.

Whether the stronger relationship is needed is untested, because nothing in the
toy asked the market to price a claim *about* a reason. A case that does — a
value query whose answer depends on what the record has recognised as a reason —
would settle it.

*Deliverable shape:* either such a case, with what it forces `L_min(V)` to
contain, or an argument that the weak relationship is closed under the
architecture's operations.
*Acceptance check:* the slice's compiler runs on the case unchanged, or the round
states exactly which of its functions must newly read `V`.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/FINDINGS.md`
§3.
*Consumed by:* the round taking these waists to real normative practice, which is
where open-textured reasons first arrive.
