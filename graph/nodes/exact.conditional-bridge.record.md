---
id: exact.conditional-bridge.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.ExactConditions.Bridge.bridge
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: exact.conditional-bridge
---
## Statement
The declaration Workspace.Normativity.Contrib.ExactConditions.Bridge.bridge is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `exact.conditional-bridge` (class lean-proved, status active, origin round 2026-11-10-exact-conditions-capital; answers item 138).
Documentation: verification: projects/normativity/rounds/2026-11-10-exact-conditions-capital/THEOREM.md; context: projects/normativity/rounds/2026-11-10-exact-conditions-capital/REPORT.md.
The signature of `Workspace.Normativity.Contrib.ExactConditions.Bridge.bridge` (theorem) in lean/Workspace/Normativity/Contrib/ExactConditionsReserve.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hγ : 0 < γ)
        (hx : ∀ n, 0 ≤ x n ∧ x n ≤ 1) (hmu : ∀ n, 0 ≤ mu n)
        (hceil : ∀ n, prior c x mu n + mu n * (1 - c) ≤ U)
        (hfreq : Frequency c U γ x mu) :
        Summable (ratio c U x mu) ∧ (∃ Ymax, ∀ n, margin c U x mu n ≤ Ymax) ∧ Summable mu ∧
          ∀ (S : Finset ℕ) (y : ℕ → ℝ), (∀ n, 0 ≤ y n) →
            -(c * ∑' i, mu i) ≤ ∑ i ∈ S, mu i * (y i - c)
