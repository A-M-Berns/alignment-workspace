---
id: coherence.modulus-net-cover.h10
kind: leaf
leaf_kind: hypothesis
discharge: open
size: S
size_reason: "one binder of one declaration"
version: 1
author: "@smithy-verity"
---
## Statement
The hypothesis `hcover : ∀ c : κ → ℚ, l1 coords c ≤ 1 → ∃ c' ∈ net, l1 coords (fun k => c k - c' k) ≤ mesh` of the declaration holds.

## Source
The signature of `Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_net_cover` in lean/Workspace/Normativity/Contrib/CoherenceModulus.lean.
Binder: `hcover : ∀ c : κ → ℚ, l1 coords c ≤ 1 → ∃ c' ∈ net, l1 coords (fun k => c k - c' k) ≤ mesh`.
