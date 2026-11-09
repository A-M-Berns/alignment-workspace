---
id: item-134
kind: leaf
leaf_kind: task
action: "Attach a vocabulary change to the accounted state: a transition of the normative state carrying a translation, the theorem that an entitlement and no broken commitment before it give an entitlement after it, a defeasible form for a pulled-back row, and a procedure computing the image of a forced region."
who: agent
item: "134"
title: "Content across a vocabulary change, on the accounted state"
section: "Deference line — second wave"
maintainer_order: 145
difficulty: "open"
heading_notes: ""
project: normativity
dispatchable: true
item_status: open
deliverable: "`lean-proved`; the transition, the transport theorem for `Entitlement`, and the split fixture run through it with one kept and one broken commitment."
acceptance: "the Lean audit clean; `Conservativity.bad_not_conservative` and `Recollection.split_broken` recovered as instances of the transition's verdict."
work:
  - {kind: round, ref: projects/normativity/rounds/2026-11-08-content-recollection}
  - {kind: decision, ref: 2026-11-08--vocabulary-change-is-translation-conservativity-criterion}
  - {kind: decision, ref: open--broken-commitment-bars-or-accounts}
context: ["lean/Workspace/Normativity/Contrib/Conservativity.lean", "lean/Workspace/Normativity/Contrib/Recollection.lean", "lean/Workspace/Normativity/Contrib/ExpressesByRole.lean", "projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry, three Lean modules of context"
version: 1
---
## Statement
Item 134, Content across a vocabulary change, on the accounted state, is delivered in the shape its entry states: `lean-proved`; the transition, the transport theorem for `Entitlement`, and the split fixture run through it with one kept and one broken commitment.

## Source
ATTENTION.md, item 134 (Content across a vocabulary change, on the accounted state); its context: `lean/Workspace/Normativity/Contrib/Conservativity.lean`, `lean/Workspace/Normativity/Contrib/Recollection.lean`, `lean/Workspace/Normativity/Contrib/ExpressesByRole.lean`, the content-recollection round's report.

## Notes
Filed by the content-recollection round (prompts/2026-11-08-content-recollection), which proved the criterion on regions and left its attachment to the accounted state; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
A vocabulary change is a translation of rows (`Conservativity.Translation`): each old coordinate
is a rational linear form in the new ones, an old row pulls back to a new row, and the change
refines, adds nothing or is conservative according to how the image of the new region sits
against the old (`refines_iff`, `addsNothing_iff`, `conservative_iff`, registered
`content.conservative-iff-image`). A stochastic map between world spaces is the case on
world-distribution coordinates (`Recollection`), its broken commitments the old rows whose
pullback the new region does not force (`no_broken_iff`). None of this is attached to the
accounted state. `OpenIntegrityEvolution.Step` changes a boundary and its accounts and carries
no translation; `WarrantInductor.Entitlement` is stated at one state over one fragment; and the
pullback of a leverage form along a translation that is not a coordinate map is a row, so a
recollected commitment enters the new seed as a structural row with no docket port. Wanted:
(a) a transition of the normative state (`WarrantInductor.NormState`) carrying a translation,
with the theorem that an entitlement before it and no broken commitment give an entitlement
after it, `Expresses` read as `ExpressesByRole.ExpressesNoMore` against the interpretation
composed with the translation; (b) a defeasible form for a pulled-back row — the port of the
form it came from — with the theorem that defeat commutes with pullback, or the fixture showing
it cannot; (c) a procedure computing the image of a forced region under a coordinate map from
the elimination of `SeedStatics.project`, so that conservativity is decided and not only
characterized.

*Deliverable shape:* `lean-proved`; the transition, the transport theorem for `Entitlement`, and
the split fixture (`Recollection.split`) run through it with one kept and one broken commitment.
*Acceptance check:* the Lean audit clean; `Conservativity.bad_not_conservative` and
`Recollection.split_broken` recovered as instances of the transition's verdict.
*Context:* `lean/Workspace/Normativity/Contrib/Conservativity.lean`;
`lean/Workspace/Normativity/Contrib/Recollection.lean`;
`lean/Workspace/Normativity/Contrib/ExpressesByRole.lean`;
`projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md`.
*Consumed by:* item 115 (transport of `Licensed` across record transitions is the case with the
vocabulary fixed); item 128, clause (c); the queue entry on broken commitments.
