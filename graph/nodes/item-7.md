---
id: item-7
kind: leaf
leaf_kind: task
action: "Continue PRIORITIES item 7 in Workspace.Deference.Contrib: connect the criterion's application to FAF's market, trader and no-exploit objects and ship the inhabitation witness."
who: either
files: ["lean/Workspace/Deference/Contrib/"]
item: "7"
title: "Model the market and the traders"
section: "Deference line"
maintainer_order: 50
difficulty: "substantial"
heading_notes: " — *partially closed Stage V*"
project: deference
dispatchable: true
item_status: open
deliverable: "`lean-proved` in `Workspace.Deference.Contrib`, with an inhabitation witness for the hypothesis package."
acceptance: "The Lean gate is green, the axiom audit is clean, and the nonvacuity witness typechecks."
context: ["projects/deference/note-dump-2026-08-11/lean-deference/AUDIT.md"]
work:
  - {kind: decision, ref: 2026-08-12--deference-line-s-current-source-material}
  - {kind: decision, ref: 2026-08-24--queue-triaged-rulings-rounds-recommended}
  - {kind: decision, ref: 2026-10-02--write-scope-behind-schedule-security-condition}
author: "@smithy-verity-opus55"
size: L
size_reason: "a Lean model and a witness"
version: 1
---
## Statement
The public Lean deference development contains a market and trader model under
which the logical induction criterion's application is a proof, with an
inhabitation witness for the hypothesis package.

## Source
PRIORITIES.md item 7, "Model the market and the traders": "The development
takes the Logical Induction theorems as named hypotheses and proves what
follows"; partially closed Stage V.

projects/deference/note-dump-2026-08-11/lean-deference/AUDIT.md §3.1.

## Notes
The public line's item; the clean room states every deference package over
FAF's criterion, which addresses the same defect.

## Item
The audit's §3.1 is "The market and traders are entirely unmodeled". The
development takes the Logical Induction theorems as named hypotheses and proves
what follows; the inference from the criterion to the forcing inequality is
nowhere in it, because the objects that inference is about are absent.

*Deliverable shape:* `lean-proved` in `Workspace.Deference.Contrib`, with an inhabitation witness for the hypothesis package.
*Acceptance check:* The Lean gate is green, the axiom audit is clean, and the nonvacuity witness typechecks.

*Context:* `projects/deference/note-dump-2026-08-11/lean-deference/AUDIT.md` §3.1.
*A solution ships:* a minimal market and trader model in
`Workspace.Deference.*`, enough that the criterion's application is a proof
rather than a hypothesis, with the axiom audit clean.

*Stage V status:* the actual FAF market, strategy, trader, net-worth and
`IsLogicalInductor.noExploit` objects are now connected. The signed-error forcing
chain derives trader efficiency from `RpnSentenceCodes`; faithful acceleration
uses actual FAF wealth and criterion semantics. The residue is cross-process:
polynomial emission for the other process's quote sequence, cross-market
calibration, and generic deductive-process non-vacuity. See
`projects/deference/notes/LI_NATIVE_DEFERENCE.md`.
