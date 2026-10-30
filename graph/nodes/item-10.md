---
id: item-10
kind: leaf
leaf_kind: task
action: "Execute item 10 per its deliverable shape and acceptance check: Build the Lean in CI."
who: agent
item: "10"
title: "Build the Lean in CI"
section: "Infrastructure"
maintainer_order: 131
difficulty: "entry"
project: none
dispatchable: true
item_status: open
deliverable: "A change to `.github/workflows/ci.yml` — **specification layer**, so a maintainer act; contributors propose via issue."
acceptance: "The `lean` job's wall time falls, measured across two consecutive pushes that change neither the pin nor the toolchain."
context: ["prompts/2026-08-10-repo-scaffolding/REPORT.md"]
work:
  - {kind: decision, ref: 2026-08-11--setup-scrub-reports-removed-root}
author: "@smithy-verity"
size: S
size_reason: "one item entry of 89 words"
version: 1
---
## Statement
Item 10, Build the Lean in CI, is delivered in the shape its entry states: A change to `.github/workflows/ci.yml` — **specification layer**, so a maintainer act; contributors propose via issue.

## Source
PRIORITIES.md, item 10 (Build the Lean in CI); its context: `.github/workflows/ci.yml`; the measured times are recorded in `prompts/2026-08-10-repo-scaffolding/REPORT.md`.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The Lean gate compiles in CI with a cached `.lake/`; if that cache proves too
slow or too large for the runner, the gate needs restructuring rather than
disabling. Anyone who improves the cache hit rate or the build time has
contributed.

*Deliverable shape:* A change to `.github/workflows/ci.yml` — **specification layer**, so a maintainer act; contributors propose via issue.
*Acceptance check:* The `lean` job's wall time falls, measured across two consecutive pushes that change neither the pin nor the toolchain.

*Context:* `.github/workflows/ci.yml`; the measured times are recorded in
`prompts/2026-08-10-repo-scaffolding/REPORT.md`.
