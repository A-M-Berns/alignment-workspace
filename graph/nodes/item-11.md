---
id: item-11
kind: leaf
leaf_kind: task
action: "Execute item 11 per its deliverable shape and acceptance check: Verification-register presence check in CI."
who: agent
item: "11"
title: "Verification-register presence check in CI"
section: "Infrastructure"
maintainer_order: 132
difficulty: "entry"
project: none
dispatchable: true
item_status: open
deliverable: "A change to `.github/workflows/ci.yml` and a check script — **specification layer**."
acceptance: "The check runs in CI, passes on a compliant directory and fails on one missing its verification register."
context: ["AGENTS.md"]
author: "@smithy-verity"
size: S
size_reason: "one item entry of 80 words"
version: 1
---
## Statement
A solution to item 11 ships the check, a passing case, and a failing case proving it bites.

## Source
PRIORITIES.md, item 11 (Verification-register presence check in CI); its context: `AGENTS.md`, register statement; `.github/workflows/ci.yml`.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
`AGENTS.md` requires every substantive deliverable to ship a verification
register in the repository. A heuristic gate checking new results directories is
cheap once "results directory" is defined.

*Deliverable shape:* A change to `.github/workflows/ci.yml` and a check script — **specification layer**.
*Acceptance check:* The check runs in CI, passes on a compliant directory and fails on one missing its verification register.

*Context:* `AGENTS.md`, register statement; `.github/workflows/ci.yml`.
*A solution ships:* the check, a passing case, and a failing case proving it bites.
