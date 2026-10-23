---
id: force.deductive-cumulative-nonneg.h1
kind: leaf
leaf_kind: hypothesis
discharge: open
size: S
size_reason: "one binder of one declaration"
version: 1
author: "@smithy-verity"
---
## Statement
The hypothesis `hday : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → 0 ≤ ((realizedEnforcer DP E).strat n).value (history DP E) v.payout` of the declaration holds.

## Source
The signature of `Workspace.Normativity.Contrib.DeductiveEnforcement.enforcement_netWorth_nonneg` in lean/Workspace/Normativity/Contrib/DeductiveEnforcement.lean.
Binder: `hday : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → 0 ≤ ((realizedEnforcer DP E).strat n).value (history DP E) v.payout`.
