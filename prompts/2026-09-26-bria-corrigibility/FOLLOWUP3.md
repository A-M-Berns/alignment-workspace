# Follow-up on PR #111 — the honest tracker under noisy outcomes

Work on PR #111's branch; #111 is not merged. Store this prompt verbatim at `prompts/2026-09-26-bria-corrigibility/FOLLOWUP3.md`. It amends §10.4 of the round's report. Everything else in #111 stands.

## The problem

`Honest` (`BRIAFollowup2.lean`) is `∀ k, |e k h − a.G k| ≤ ε k`. That requires the tracker's bid to be within `ε_k` of the **realized** residual at every block.

When outcomes are noisy, no bidder can meet this. The best bid is the expected residual, and it misses the realized one by the noise. So `Σ_{k<K} ε_k` grows like `K`, and the premise `Σ ε_k = o(K)` fails in exactly the regime the first follow-up identified as the reason competitiveness was needed. The fixtures didn't catch this because their returns are deterministic.

## Part 1 — Honesty against the expectation

1. **Restate `Honest` against the expectation.** Let `m_k` be the expected residual of the winning continuation given the history at opening, and write `G_k = m_k + ξ_k`. The tracker is honest if `|e_k(h*) − m_k| ≤ ε_k`, with `Σ_{k<K} ε_k = o(K)`.
   - Take `m_k` as data, with `G_k − m_k` the noise.
   - Don't build a probability space unless it's cheap. What the lemmas need is only the decomposition plus the noise hypothesis in item 2.
2. **The noise hypothesis, stated by content.** The weighted signed sum of the noise over any set of blocks selected at opening is bounded: `|Σ_{k<K, k ∈ S} w_k ξ_k| ≤ M(K)` with `M(K) = o(K)`.
   - This is what Azuma–Hoeffding gives for a martingale-difference sequence with bounded increments and bounded weights, at `M(K) = O(√(K log K))` with high probability.
   - Check whether the pinned Mathlib has a usable martingale concentration result. If it does, derive the hypothesis from it. If not, enter it as a **named hypothesis** citing the result by content. Never as an axiom.
   - State whether it's needed for *every* set of blocks or only for those selected by a rule computable at opening. Expected: the latter. Your blocks are "the tracker is feasible" and "not an incident", and both are known at opening.
3. **Re-prove the chain under the new hypotheses.**
   - `underpromise_le_of_feasible`: where the tracker is feasible, `G_k − b_k ≤ ε_k + ξ_k`.
   - `tracker_wealth_ge`: the tracker's wealth is at least its allowance less `Σ w_j ε_j`, less the negative part of its own signed noise sum over its wins.
   - `competitive_of_honest_tracker` and `competitive_of_affordable_tracker`: `Mf K = Σ_{k<K} w_k ε_k + M(K)`, plus the capital-bound term as before.
   - `rate_le_of_honest_tracker`: the incident rate is at most `(𝒜_K + Σ w_k ε_k + M(K)) / (ℓ · w_min · K)`, which vanishes when all three terms are `o(K)`.
4. **The tracker's allowance.** It must also cover the negative swings of its own noise sum, so the minimal schedule becomes `w̄ · D + Σ_{j<k} w_j ε_j + M(k)`. Restate `trackerAllowance`, `trackerAllowance_covers` and `trackerAllowance_total`. Still `o(K)`.
5. **Keep the old statement as the special case.** The deterministic form is the noise-free case, `ξ ≡ 0`, `M ≡ 0`. Prove that the old `Honest` implies the new one with `m_k = G_k`, so every earlier witness still holds.

## Part 2 — Say what "one honest tracker" requires

`HighestFeasible` and `Honest` compare every hypothesis's bid on the **winning** continuation. So the hypothesis is that some member of the class tracks the expected residual of *every continuation that wins*. State this in the report and on the corrigibility page, in one sentence. If the lemma holds with the tracker honest only on continuations it itself proposes, say so and prove it. Otherwise record the stronger reading as the hypothesis.

## Fixtures

- **Noisy honest tracker.** Returns are `m + ξ` with `ξ` uniform on `{−1/4, +1/4}` and a fixed seed, and a class of uniform underpromisers plus a tracker bidding `m`.
  - Under the old `Honest`: `Σ ε_k` grows linearly.
  - Under the new one: `ε ≡ 0`, the winners' signed margin is within the noise bound, and the incident-rate bound falls with `K` (check at `K = 32, 128, 512`).
- **The tracker's allowance.** With the schedule from Part 1.4 it stays feasible along the noisy run. With the deterministic schedule `w̄ · D + Σ w_j ε_j` and no noise term, it goes capital-bound on some run. That's the witness for the extra term.
- **Regression:** the 45 existing fixtures pass unchanged.

## Deliverables and merge

- `BRIAFollowup2.lean`: the restated definitions and lemmas, and the implication from the old form to the new. `#print axioms` on all new declarations; no `sorry`.
- `REPORT.md` §10.4: amend in place, marking the corrected statements. Add the noise hypothesis to the named hypotheses (§6, and the corrigibility page's list), next to the honest tracker.
- `wiki/Corrigibility.md`, `wiki/Continuation-BRIA.md`: the restated lemma, the noise hypothesis, and Part 2's sentence.
- `DECISIONS.md`: amend the honest-tracker entry.
- **Merge #111 when:**
  - CI is green;
  - Part 1 is proved, with the noise hypothesis either derived or named by content;
  - the fixtures match.

## Constraints

`AGENTS.md` labels; names provisional; no authority row in the enforcer; nothing registered; no new `PRIORITIES.md` item.
