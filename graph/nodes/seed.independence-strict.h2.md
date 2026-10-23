---
id: seed.independence-strict.h2
kind: leaf
leaf_kind: hypothesis
discharge: open
size: S
size_reason: "one binder of one declaration"
version: 1
author: "@smithy-verity"
---
## Statement
The hypothesis `hpin : ∀ x, B.RegionR x → (∀ r ∈ L₁, StrictSatR r x) → x φ = p` of the declaration holds.

## Source
The signature of `Workspace.Normativity.Contrib.SeedStatics.seed_independence_strict` in lean/Workspace/Normativity/Contrib/SeedStatics.lean.
Binder: `hpin : ∀ x, B.RegionR x → (∀ r ∈ L₁, StrictSatR r x) → x φ = p`.
