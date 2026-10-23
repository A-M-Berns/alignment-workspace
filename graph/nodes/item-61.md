---
id: item-61
kind: leaf
leaf_kind: task
action: "Execute item 61 per its deliverable shape and acceptance check: A normative source with summable enforcement liability."
who: agent
item: "61"
title: "A normative source with summable enforcement liability"
section: "Normativity line — legitimacy"
maintainer_order: 37
difficulty: "substantial"
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported` at minimum — a normative source with an explicit settlement trajectory and presentation schedule, and either a proof that the sum converges or a witness that it does not for a source the architecture would call legitimate."
acceptance: "a runner drives the slice's `trajectories` harness over the declared trajectory, computes `D_t` per date through `LiveDeficitCertificate.by_enumeration`, and reports the partial sums against a stated bound."
context: ["projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/FINDINGS.md", "projects/normativity/rounds/2026-08-16-traderized-enforcement/FUNDING_AND_SAFETY.md"]
work:
  - {kind: decision, ref: 2026-09-08--inertness-dichotomy-next-step-entry-retired}
author: "@smithy-verity"
size: L
size_reason: "one item entry of 405 words"
version: 1
---
## Statement
Item 61, A normative source with summable enforcement liability, is delivered in the shape its entry states: `test-supported` at minimum — a normative source with an explicit settlement trajectory and presentation schedule, and either a proof that the sum converges or a witness that it does not for a source the architecture would call legitimate.

## Source
PRIORITIES.md, item 61 (A normative source with summable enforcement liability); its context: `projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/FINDINGS.md` §6 and its `src/trajectories.py`, which carries four synthetic trajectories, two convergent and two not; `projects/normativity/rounds/2026-08-16-traderized-enforcement/FUNDING_AND_SAFETY.md` §9.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The end-to-end slice establishes that the unconditional traderization theorem's
admissibility hypothesis holds exactly for injunctions that change nothing about
the prices, so every operative injunction with content depends on the charged
branch. The condition that branch needs is

```text
sum_t (eps_t + M_t) * D_t / delta_t  <  infinity
```

where `D_t = max over omega live at t of sum_j d_{t,j}(omega)` is
`outflow.LiveDeficitCertificate.by_enumeration`'s sharp aggregate, computed for
the **exact day-`t` compiled force request** over the **exact live-world
assessment state**. No source in this repository is shown to satisfy it, which
makes this the single condition the architecture's safety claim rests on.

Four things the slice established that constrain what an answer may look like,
and that a round taking this item should not have to rediscover:

1. **`D_t` is not monotone across days.** A frozen injunction over `Expect(X)`
   compiles to a different row system each day, and the precision-`k` reading of
   a value is `ceil(x*k)/k`, which is not monotone in `k`. The slice exhibits
   `D_1 = 0` and `D_2 = 1/6` on one injunction with a strictly growing stage. An
   argument that settlement drives the sum down must therefore say something
   about the mesh, not only about the worlds.
2. **The charge is presentation-dependent.** `D_t` sums across rows, so stating
   one demand twice doubles it while enforcing the same prices. The condition is
   about a schedule of presentations.
3. **The tolerance route is bounded.** While `delta_t <= 1` — and a looser
   promise is vacuous on prices in `[0,1]` — the charge dominates
   `(eps_t + M_t) * D_t`, so summability requires
   `sum_t (eps_t + M_t) * D_t < infinity`.
4. **Two of the three factors therefore have to carry it**, and the slice
   exhibits both routes working synthetically: the deficit going to zero under
   settlement, and the ordinary aggregate's bound decaying.

*Deliverable shape:* `test-supported` at minimum — a normative source with an
explicit settlement trajectory and presentation schedule, and either a proof
that the sum converges or a witness that it does not for a source the
architecture would call legitimate.
*Acceptance check:* a runner drives the slice's `trajectories` harness over the
declared trajectory, computes `D_t` per date through
`LiveDeficitCertificate.by_enumeration`, and reports the partial sums against a
stated bound.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/FINDINGS.md`
§6 and its `src/trajectories.py`, which carries four synthetic trajectories, two
convergent and two not;
`projects/normativity/rounds/2026-08-16-traderized-enforcement/FUNDING_AND_SAFETY.md`
§9.
*Consumed by:* any round claiming the normative layer preserves the
logical-induction guarantee, which is every downstream round.
