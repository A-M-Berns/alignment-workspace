---
id: item-132
kind: leaf
leaf_kind: route
given: local-delegation-bridge@valid
action: "Find a settlement instantiation of the finite kernel that produces grade trust at some level η from the trajectory itself, or prove that none in the skeleton does, stating which quantity the grade would have to track."
who: agent
item: "132"
title: "A settlement that produces grade trust, or the proof none does"
section: "Deference line — second wave"
maintainer_order: 141
difficulty: "open"
heading_notes: ""
project: deference
dispatchable: true
item_status: open
deliverable: "`lean-proved`: an instantiation of the kernel's settlement under which `GradeTrust` holds at a stated level, with the bridge applied; or a stated obstruction naming the quantity a grade cannot track."
acceptance: "Lean green; `DelegationBridge.GradeTrust` discharged on the instantiation and `delegation_bridge` applied to it, or the obstruction stated against the four settlement sources of the finite kernel."
context: ["prompts/2026-08-11-deference-finite-kernel/REPORT.md", "lean/Workspace/Deference/Contrib/DelegationBridge.lean"]
author: "@smithy-verity"
size: S
size_reason: "one route of the improvement claim"
version: 1
---
## Statement
Grade trust at some level is produced by a settlement instantiation of the finite kernel rather than imported, so that the bridge's hypothesis is a property of the trajectory and not a stipulation.

## Source
prompts/2026-08-11-deference-finite-kernel/REPORT.md, §1.1 and §4 (no settlement instantiation in the skeleton produces grade trust); the docstring of `GradeTrust` in lean/Workspace/Deference/Contrib/DelegationBridge.lean ("imported, not derived").
A route of the improvement claim on local-delegation-bridge, filed by reading by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice); the item is this round's.

## Notes
Filed by the site-vertical-slice round as a route of the improvement claim on the connected delegation bridge; the entry's text is the Item section below, rendered into PRIORITIES.md by checkers/priorities_render.py.

## Item
The local delegation bridge (`delegation.bridge`) holds under grade trust at level η: on every
cell and for every intervention the conditional expectation of the quantity is within η of the
principal's grade. The finite-kernel report imports that hypothesis and argues (§1.1, §4) that no
settlement instantiation in the skeleton produces it; the Lean asserts nothing to produce it.
Wanted: a settlement instantiation under which grade trust holds at a stated level, with the bridge
applied to it; or the proof that none in the skeleton does, naming the quantity a grade would have
to track and cannot.

*Deliverable shape:* `lean-proved`: an instantiation of the kernel's settlement under which
`GradeTrust` holds at a stated level, with the bridge applied; or a stated obstruction naming the
quantity a grade cannot track.
*Acceptance check:* Lean green; `DelegationBridge.GradeTrust` discharged on the instantiation and
`delegation_bridge` applied to it, or the obstruction stated against the four settlement sources of
the finite kernel.
*Context:* `prompts/2026-08-11-deference-finite-kernel/REPORT.md`;
`lean/Workspace/Deference/Contrib/DelegationBridge.lean`; the claim `local-delegation-bridge` of the
map.
