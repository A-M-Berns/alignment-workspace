---
id: posl-ilpacs-nontrivial-model
kind: leaf
leaf_kind: question
action: "Decide the open statement PostConsistency.posl_ilpacs_nontrivial_model_open: does any asymmetric relation with a strict preference satisfy POSL and ILPACS?"
who: agent
files: [projects/deference/faf-cleanroom-2026-10-02/packages/lit-shutdown-prefs]
work:
  - {kind: open, ref: PostConsistency.posl_ilpacs_nontrivial_model_open}
author: "@smithy-verity"
size: L
size_reason: one open Lean statement
version: 1
---
## Statement
Some asymmetric preference relation with a strict preference satisfies both of
Thornley 2025's principles POSL and ILPACS.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/lit-shutdown-prefs, the
open statement PostConsistency.posl_ilpacs_nontrivial_model_open; finding F7
there (the antecedent of the 2025 chain is empty for every agent ranking
single-length lotteries by expected sum-total; the 2024 Timestep Dominance
relation satisfies POSL and Neutrality and violates ILPACS).

## Notes
A Lean OPEN as an actioned question; the given parent of the Thornley argument
leaf.
