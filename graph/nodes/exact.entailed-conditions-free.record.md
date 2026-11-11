---
id: exact.entailed-conditions-free.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.deductive_exact
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: exact.entailed-conditions-free
---
## Statement
The declaration Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.deductive_exact is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `exact.entailed-conditions-free` (class lean-proved, status active, origin round 2026-11-10-exact-conditions-capital; answers item 137).
Documentation: verification: projects/normativity/rounds/2026-11-10-exact-conditions-capital/THEOREM.md; context: projects/normativity/rounds/2026-11-10-exact-conditions-capital/REPORT.md.
The signature of `Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.deductive_exact` (theorem) in lean/Workspace/Normativity/Contrib/ExactConditions.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (DP : DeductiveProcess)
        (hLive : ∀ n v, M.L.Live n v ↔ v.ConsistentWith (DP.D n))
        (coords : ℕ → List Sentence)
        (hreg : ∀ n (x : Sentence → ℝ), (∀ φ, 0 ≤ x φ ∧ x φ ≤ 1) →
          (M.C.Holds n x ↔ deductiveRegion (DP.D n) (coords n) x)) :
        (∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits M.P DP) ∧
          ∀ n, deductiveRegion (DP.D n) (coords n) (M.P n)
