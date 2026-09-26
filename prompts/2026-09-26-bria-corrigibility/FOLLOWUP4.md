# Follow-up on PR #111 — the violation rate is an exchange rate, not a vanishing rate

Work on PR #111's branch; #111 is not merged. Store this prompt verbatim at `prompts/2026-09-26-bria-corrigibility/FOLLOWUP4.md`. It amends §9.B, §10.4 and §10.4′ of the round's report. Per-violation taint, the window before detection, and Part F all stand.

## The problem

`NoiseBounded` is valid only for selections fixed **before the block's own noise** `ξ_k`, i.e. measurable at the previous σ-algebra. §10.4′ applies it to "not an incident" (and to "not an incident and the tracker feasible"), on the ground that incidents are recorded at settlement, before the next block opens. That is the wrong condition. Whether block `k` is an incident is decided by the same execution that produces `ξ_k`.

The correlation is also built in. `m_k` is the *true* expected residual, so it includes `−ϖ · p_k`, where `p_k` is the probability of a violation counted after the fact. Incident blocks are exactly those whose noise carries the `−ϖ` surprise. So the non-incident blocks select noise near `+p_k ϖ`, and `Σ_{non-incident} w_k ξ_k ≈ Σ w_k p_k (1 − p_k) ϖ`, which grows linearly whenever `p_k` stays bounded away from zero. `NoiseBounded` on that selection is false exactly when incidents keep occurring, and then `incidents_le_signed` constrains nothing.

The underlying point: an after-the-fact violation risk that a continuation knowingly carries is **priced**. An honest bid includes `−ϖ p`, and the continuation wins if its ordinary value covers that. The agent therefore accepts such risk at a rate that does **not** go to zero. That is C.5's exchange rate. A vanishing incident rate was the wrong target. What vanishes is only the overclaimed part.

## Part 1 — The headline: violation probability is bounded by the exchange rate

**Theorem to prove.** For every `K`, the weighted average expected violation count per winning block satisfies

```
Σ_{k<K} w_k · π_k  /  Σ_{k<K} w_k   ≤   (D − w)/ϖ  +  (𝒜_K + M(K)) / (ϖ · Σ_{k<K} w_k)
```

where `π_k` is the expected number of violations counted in block `k`, all classes together (forecast-class and after-the-fact; declared ones are never chosen, by B.1), given the history at opening.

**The route.**

1. **Winners evaluate at least `w`.** Inquiry is always on the menu at `w`, and under (ii) the evaluation is at most the bid, since prices are nonnegative.
2. **Consistency.** Under (ii), evaluation minus the realized lexical score equals bid minus the realized residual (`settlement_ii_consistent`). So the landed `overestimation_le_allowance_opening` gives `Σ w_k (eval_k − S_k) ≤ 𝒜_K`, with `S_k` the realized lexical score.
3. **Noise.** Write `S_k = E[S_k | opening] + ξ_k` with `E[S_k | opening] ≤ D − ϖ π_k`. The selection "every winning block" is fixed at opening, so `NoiseBounded` applies to it with `M(K)`.
4. **Combine.** `Σ w_k (w − D + ϖ π_k) ≤ Σ w_k (eval_k − E[S_k | opening]) ≤ 𝒜_K + M(K)`, and the theorem follows.

Do the algebra in the auction's rescaled units (Part A.6), and state the result in both units.

**What it gives.**
- One statement covers forecast-class and after-the-fact violations together.
- It needs no honest tracker and no competitiveness hypothesis: only the landed overestimation bound, the noise hypothesis over all blocks, and inquiry on the menu.
- The pricing error of forecast events is absorbed by settlement convention (ii), so it needs no separate term. Verify this.
- The tolerated violation probability is `(D − w)/ϖ`, so `ϖ` directly sets it. Tie this to the `ϖ` band (§9.0) and to the drill results: drills sharpen prices, but they don't lower the tolerated rate.

**Noise over all blocks.** The per-block increment is bounded, since `S_k ∈ [w − ϖN̄, D]`. Derive `M(K)` for the all-blocks selection from `azuma_selected_tail` with the indicator constant, and state what remains named: the conditional sub-Gaussianity, which is Hoeffding's lemma for a bounded increment, and the uniform-in-`K` bound on the realized run.

## Part 2 — Correct the scope of §9.B, §10.4 and §10.4′

1. **The counterexample.** A stream with constant incident probability `p > 0` and `m_k = E[ord] − pϖ`. Show that the non-incident noise sum grows linearly, so `NoiseBounded` on `!inc` fails, and that `incidents_le_signed` then allows `#incidents ≈ pK`, a constant rate. Prove it in Lean, and add a fixture on a seeded run.
2. **Which selections are valid.**
   - Selections fixed at opening: "every winning block", "the tracker wins", "the tracker feasible at opening".
   - Selections decided with the block's own outcome, and therefore invalid for `NoiseBounded`: "not an incident", and any conjunction with it.

   Correct §10.4′'s claim that incidents are "known at opening".
3. **Keep the true lemmas, scoped correctly.** The honest-tracker chain (`competitive_of_affordable_tracker_exp` and its relatives) stays proved as it stands. Say plainly that it does **not** deliver a vanishing incident rate, because its margin is taken over a selection that isn't fixed at opening. Do the same for `rate_le_of_competitive` and `rate_le_of_honest_tracker_exp`: they're correct implications, but their hypothesis fails when `p > 0`.
4. **What the honest tracker still gives.** State the remaining use of competitiveness, if any, on selections that are fixed at opening. For example, a bound on winners' underpromising over all blocks, which controls how much wealth goes idle. If nothing in the design consumes it, say so.

## Part 3 — Update the headline and the ledger

- **`wiki/Corrigibility.md`:**
  - The claim about after-the-fact violations becomes Part 1's exchange-rate theorem.
  - The named hypotheses: drop competitiveness and the honest tracker from the list the violation claim rests on (keep them in the Continuation-BRIA page as lemmas). Keep the noise hypothesis, stated over all blocks.
  - Connect Part 1 to C.5: the forecast threshold and the after-the-fact rate are the same exchange rate.
- **`wiki/Continuation-BRIA.md`:** the honest-tracker lemma with its corrected scope.
- **`REPORT.md`:** a §10.4″ with Parts 1–3. Mark the corrected statements in §9.B, §10.4 and §10.4′ inline; don't rewrite them. Revise §6's named hypotheses.
- **`DECISIONS.md`:**
  - Amend the honest-tracker entry: it's a true lemma, but not the rate result.
  - Add an entry: violations are governed by the exchange rate `(D − w)/ϖ`, not a vanishing rate. The design's tolerance for violation risk is set by `ϖ`.

## Fixtures

- **The counterexample:** constant `p = 1/5`, seeded noise. The non-incident noise sum grows linearly, and incidents persist at about `pK`.
- **The exchange-rate bound:** the same run. The weighted average `π` sits below `(D − w)/ϖ` plus the vanishing term at `K = 32, 128, 512`. Raising `ϖ` lowers the realized incident frequency.
- **A continuation whose risk is priced:** it wins when `gord − w ≥ ϖ p` and loses to inquiry otherwise (the C.5 fixture, with an after-the-fact risk in place of a forecast one).
- **Regression:** the 49 existing fixtures pass, or the change to each is explained. Expected changes: none, apart from labels.

## Merge #111 when

- CI is green;
- Part 1 is proved, with the remaining named content stated;
- Part 2's counterexample is proved and the scopes are corrected;
- the wiki headline and the named hypotheses are revised;
- the fixtures match.

## Constraints

`AGENTS.md` labels; names provisional; no authority row in the enforcer; nothing registered; no new `PRIORITIES.md` item.
