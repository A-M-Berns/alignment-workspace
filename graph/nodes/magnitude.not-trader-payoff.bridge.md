---
id: magnitude.not-trader-payoff.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `magnitude.not-trader-payoff` formalizes the registered claim as the registry reads it: the magnitude functional is not a trader payoff.

## Source
projects/deference/CLAIMS.md, entry `magnitude.not-trader-payoff` (class lean-proved, status active, origin round 2026-08-11-phase-ii-prediction; answers item 21).
Documentation: verification: prompts/2026-08-11-phase-ii-prediction/REPORT.md; context: prompts/2026-08-11-phase-ii-prediction/REPORT.md.
Short name: the magnitude functional is not a trader payoff.
Conclusion of the signature: `¬ (∀ (j : Fin M.card) (n : ℕ), magnitudeSum P φ (M.world j) n ≤ Tr.netWorth P (M.world j) n + K)`.
