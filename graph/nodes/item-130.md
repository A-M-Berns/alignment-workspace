---
id: item-130
kind: leaf
leaf_kind: route
given: split-bill-is-robust-openness@valid
action: "State an intervention semantics for Robust Openness indexed by the accounted state (the docket, the ports and the accounts), producing for each state and concern the actual coverage data and the data under each declared intervention, and check the non-capture certificate against it."
who: agent
item: "130"
title: "An intervention semantics for Robust Openness, read off the accounted state"
section: "Normativity line — legitimacy"
maintainer_order: 139
difficulty: "substantial"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "a declared intervention class and semantics over the accounted state, with the certificate theorems instantiated on it, or a stated reason the semantics belongs to the application alone."
acceptance: "Lean green; `Scenario.cf` produced by the semantics on at least one accounted fixture, with `certPlus_iff_robustOpen` and `robustOpen_of_persistence` instantiated there."
context: ["wiki/Openness-Coverage-and-Non-Capture.md", "lean/Workspace/Normativity/Contrib/NonCaptureCertificate.lean"]
author: "@smithy-verity"
size: S
size_reason: "one route of the improvement claim"
version: 1
---
## Statement
An intervention semantics indexed by the accounted state produces, for each state and concern, the actual coverage data and the coverage data under each declared intervention, so that the scenario the certificate theorems quantify over is read off the record rather than supplied by hand.

## Source
wiki/Openness-Coverage-and-Non-Capture.md, Robust Openness ("The semantics is indexed by the accounted state, so it can read the docket, the ports and the accounts"); the header of lean/Workspace/Normativity/Contrib/NonCaptureCertificate.lean ("how `cf j` is produced is the external semantics and is not modelled here").
A route of the improvement claim on split-bill-is-robust-openness, filed by reading by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice); the item is this round's.

## Notes
Filed by the site-vertical-slice round as a route of the improvement claim on the connected openness claim; the entry's text is the Item section below, rendered into PRIORITIES.md by checkers/priorities_render.py.

## Item
The non-capture certificate theorems (`NonCaptureCertificate.lean`) quantify over a scenario: the
coverage state of a concern on the actual prefix and one state per declared intervention. How a
counterfactual state is produced is the external semantics, and the Lean does not model it; the wiki
says the semantics is indexed by the accounted state, so that it can read the docket, the ports and
the accounts. Wanted: a declared intervention class and a semantics over the accounted state that
produces the scenario, with the certificate theorems (`certPlus_iff_robustOpen`,
`robustOpen_of_persistence`) instantiated on at least one accounted fixture; or a stated reason the
semantics belongs to the application and not to the theory.

*Deliverable shape:* a declared intervention class and semantics over the accounted state, with the
certificate theorems instantiated on it, or a stated reason the semantics belongs to the application
alone.
*Acceptance check:* Lean green; `Scenario.cf` produced by the semantics on at least one accounted
fixture, with `certPlus_iff_robustOpen` and `robustOpen_of_persistence` instantiated there.
*Context:* `wiki/Openness-Coverage-and-Non-Capture.md`;
`lean/Workspace/Normativity/Contrib/NonCaptureCertificate.lean`; the claim
`split-bill-is-robust-openness` of the map.
