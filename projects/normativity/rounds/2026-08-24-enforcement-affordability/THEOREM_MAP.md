# Theorem map: model ↔ skeleton v44 ↔ Lean

Status: research round artifact; unregistered. Skeleton = *Strengthening
Logical Induction with Traderized Constraints*, v44 (sha256 in `MEMO.md`).
Lean file/line citations are to this repository's
`lean/Workspace/Normativity/Contrib/` and, for the source, the FAF pin
`c0d885bf`.

| Model object / statement | Skeleton | Lean |
|---|---|---|
| MarketMaker postulate (`solve_day` verification: combined day value ≤ 2^-n at every cube vertex) | Lemma 3.2 (Def./Prop. 5.1.2 extended to fractional valuations) | — (cited via source MarketMaker lemmas) |
| projection enforcer `Enforcer` (`λ(proj_K(p) − p)`) | Definitions 2.2, 3.6 | — |
| `loss_cap`, `BudgetedTrader.scale`, `shut_off` | the TradingFirm's Budgeter, as consumed by Remark 4.2 | source `Budgeter.lean:600,727,735,783,918`; lift `AssessmentProcess.lean:358,392,399,472,498,518,613,653,704`; specializations `:835,868,890` |
| per-component floors; firm floor −2; spread-independence (G2) | Remark 4.2's budget structure | `AssessmentFirm.lean:266` (`componentTrader_netWorth_floor`), `:293` (`tradingFirmTrader_netWorth_floor`), `:127` (component-sum identity) |
| `intensity` (`ρ_n = A_n + 2^-n`, `λ_n = ρ_n/δ_n²`) | Definition 3.3, Proposition 3.1 | — |
| `lifetime_liability` (min over live tables of cumulative enforcement worth) | Definition 4.1 | — |
| T1: uncontested fixed point within 2^-n of K, position ≤ 11·2^-n, liability geometric against every pattern | **strengthens Theorem 3.4** in the uncontested case (realized ≈ 2^-n versus guaranteed δ_n) | — |
| T2: liability ≤ W·hi/(1−hi) + 7·Σ2^-n, tolerance-free; flow-inventory identity | **refines Proposition 6.1**: per-day worst case `−(ρ_n/δ_n)e_n(W)` replaced by realized-flow accounting `≥ −|c_n|·e_n(W) − slack`; the divergence of 6.1's bound is an artifact for margined contested schedules | — |
| T2(vi): K = {1/2} affordable uniformly in δ | **Remark 6.2's homothetic core shown sufficient-but-not-necessary**; the core lens reads a revenue property (churn spread) as solvency | — |
| W1 / W3 exploitation shapes forcing divergence | Theorem 4.4 contrapositive (cited, not re-proved); Definition 4.1 | — |
| zero-liability (absorbed) regime | Theorem 4.6 (cited) | — |
| W4 stream: final-region membership vs earlier losses | consistent with Appendix B Proposition B.1; extends it to the vindication-recharge divergence engine | — |
| per-day vs at-horizon plausibility; nesting promotion | the criterion's `PC(D_N)` quantifier (Section 1); Appendix D's generalized live sets are exactly where the non-nested attack lives | `AssessmentProcess.lean:88` (`Assessment.nested`), `:205,217` |

## Skeleton results: cited vs strengthened vs untouched

- **Cited, relied on:** Lemma 2.3; Lemma 3.2; Theorem 3.4 (contested days);
  Theorem 4.4 (and its contrapositive, load-bearing for W1/W3); Theorem 4.6;
  Remark 4.2; Proposition B.1.
- **Strengthened / refined by this round (model evidence, unregistered):**
  Theorem 3.4 in the uncontested case (T1); Proposition 6.1 (realized-flow
  accounting replaces per-day worst case; divergence classified by the
  two-defect taxonomy); Remark 6.2 (homothetic core demoted to sufficient
  condition; revenue-vs-solvency distinction).
- **Untouched:** Sections 5 and 7; Theorem 5.3 and its corollaries;
  Appendices A, C, D (Appendix D is referenced as the natural home of the
  non-nested identity attack, not modified).
