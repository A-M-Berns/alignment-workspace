---
id: task-gated-update-truthstar
kind: leaf
leaf_kind: task
action: "Prove gatedUpdate_fails_at_truthStar_open: the gated update identity fails at a non-generable pseudorandom gate, establishing that gates must be generable for the gated chain (condition C4's side condition) at the LI register."
who: agent
files: [projects/deference/faf-cleanroom-2026-10-02/Cleanroom/Trust/LegitLiRegister/]
author: "@smithy-verity"
size: M
size_reason: "one open declaration with its witness named"
version: 1
---
## Statement
In Lean the gated update identity fails at a non-generable pseudorandom gate,
so gates in the gated chain must be generable.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/legit-li-register/legit-li-register-ledger.md,
gatedUpdate_fails_at_truthStar_open; the pseudorandom gate truthStar comes from
the def-self-trust package.

## Notes
Attached as a route of the improvement claim legit-v1-improvable: it fixes the
side condition the enforcement half needs.
