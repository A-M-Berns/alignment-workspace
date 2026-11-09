---
id: item-135
kind: leaf
leaf_kind: task
action: "Define the state a reasoner with bounded memory retains — the live docket, the specialized rows on unsettled coordinates, the holding on a finite universe of reason sets, the receipts of closed accounts — with the theorem that forced intervals and permissions computed from it equal those of the full record, a space bound or the fixture showing none, and the rule for a live coordinate."
who: agent
item: "135"
title: "Bounded memory: the state a forgetting reasoner retains"
section: "Deference line — second wave"
maintainer_order: 146
difficulty: "open"
heading_notes: ""
project: normativity
dispatchable: true
item_status: open
deliverable: "`lean-proved`; the retained state as a type, the forgetting step on it, the exactness theorem against the full record, and either a space bound in the live coordinates, live items and reason sets or the fixture showing none."
acceptance: "the Lean audit clean; `Forgetting.forget_settled`, `Forgetting.live_forget_cost` and `PrecedentHolding.permitted_append_congr` recovered as instances of the exactness theorem and its failure."
work:
  - {kind: round, ref: projects/normativity/rounds/2026-11-08-content-recollection}
  - {kind: decision, ref: 2026-11-09--forgetting-is-projection-settled-safe-live-not}
  - {kind: decision, ref: open--broken-commitment-bars-or-accounts}
context: ["lean/Workspace/Normativity/Contrib/Forgetting.lean", "lean/Workspace/Normativity/Contrib/PrecedentHolding.lean", "lean/Workspace/Normativity/Contrib/VocabularyAct.lean", "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry, three Lean modules of context"
version: 1
---
## Statement
Item 135, Bounded memory: the state a forgetting reasoner retains, is delivered in the shape its entry states: `lean-proved`; the retained state as a type, the forgetting step on it, the exactness theorem against the full record, and either a space bound in the live coordinates, live items and reason sets or the fixture showing none.

## Source
ATTENTION.md, item 135 (Bounded memory: the state a forgetting reasoner retains); its context: `lean/Workspace/Normativity/Contrib/Forgetting.lean`, `lean/Workspace/Normativity/Contrib/PrecedentHolding.lean`, `lean/Workspace/Normativity/Contrib/VocabularyAct.lean`, the content-recollection round's report.

## Notes
Filed by the content-recollection round's follow-up (prompts/2026-11-08-content-recollection, PROMPT-followup.md), which proved the pieces separately and built no retained state; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
Integrity keeps everything entered, and thin legitimacy's sufficiency needs the later record to
contain the earlier. A reasoner with bounded memory keeps less. The pieces are proved
separately: a settled coordinate may be dropped, the rows specialized at its settlement and
restricted to the other coordinates giving the projection of the forced region under every
later docket state and settlement (`Forgetting.forget_settled`, registered
`content.forget-settled`); a case base may be replaced by its holding, which permission reads
through its reach and which is eventually constant over a finite universe of reason sets
(`PrecedentHolding.permitted_append_congr`, `reachSet_eventually_const`, registered
`precedent.permitted-iff-reach`); an account with no live port keeps its receipts and its
denotation under every later substitution (`OccurrenceIntegrity.Program.closed_subst`); loss
composes as slack along a schedule (`Forgetting.schedule_slack`, registered
`memory.schedule-slack`). Two things are not safe: dropping an unsettled coordinate is exact at
the time and costs the later forced interval, `[3/4, 1]` against `[0, 1]`
(`Forgetting.live_forget_cost`, registered `memory.live-forget-cost`), and a reasoner choosing
what to drop after seeing the record obtains `[0, 1]` where each choice fixed in advance leaves
`[3/4, 1]` on one record (`selective_forgetting`, registered `memory.selective-forgetting`).
No object holds the retained state. Wanted: (a) the retained state as a type over
`WarrantInductor.NormState` or `OpenIntegrityEvolution.ObligationState` — the docket state, the
specialized and restricted rows with their ports and ids, the settlement on the unsettled
coordinates, the reach on a declared finite set of reason sets, and for each closed account its
terminals and the resolution it denotes — with the forgetting step that produces it; (b) the
theorem that every forced interval on a retained coordinate and every permission over the
declared reason sets computed from the retained state equals the full record's, under every
later docket state, settlement and continuation; (c) a space bound in the numbers of unsettled
coordinates, live items and declared reason sets, or the fixture showing none — one
elimination step can square the number of rows, a staircase of cases is irredundant
(`precedent.staircase-irredundant`), and a receipt stores the history prefix it was issued at
(`OccurrenceIntegrity.Authority.atHistory`); (d) the rule for an unsettled coordinate — when it
may be dropped and what is charged for it — stated against the three readings of
`VocabularyAct` (`Bars`, `Accounted`, `Split`), none of which registers the shedding of a live
obligation by a retelling under which its antecedent cannot occur (`zero_admitted`); (e) the
choice of what to forget as an owned occurrence (`VocabularyAct.VocabularyChange`) with a
challenge that stays open as the record grows, so that the choice `selective_forgetting`
exhibits is answerable.

*Deliverable shape:* `lean-proved`; the retained state as a type, the forgetting step on it, the
exactness theorem against the full record, and either a space bound in the live coordinates,
live items and reason sets or the fixture showing none.
*Acceptance check:* the Lean audit clean; `Forgetting.forget_settled`,
`Forgetting.live_forget_cost` and `PrecedentHolding.permitted_append_congr` recovered as
instances of the exactness theorem and its failure.
*Context:* `lean/Workspace/Normativity/Contrib/Forgetting.lean`;
`lean/Workspace/Normativity/Contrib/PrecedentHolding.lean`;
`lean/Workspace/Normativity/Contrib/VocabularyAct.lean`;
`projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md`.
*Consumed by:* item 134 (a vocabulary change that drops coordinates is a forgetting step);
item 117 (a sealed selection is a holding that may not be forgotten); the queue entry on broken
commitments.
