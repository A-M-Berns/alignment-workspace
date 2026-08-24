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

---

## Continuation: paper-1 targets (C0–C3)

| Model object / statement | Skeleton | Lean |
|---|---|---|
| C1 self-financing lemma: `q ≤ (Σ_j b_j + I)/m`, with `I` the income received at the throttling world | new; the missing side condition of Proposition 6.1's accounting | budgeting side only: `AssessmentProcess.lean:704,653,628`; `AssessmentFirm.lean:127,266,293` |
| C1 channel (c) witness: static perfectly-margined peg, liability geometric in the cycle count | **bounds the scope of any §6 affordability claim**: no schedule-local bound survives cross-coordinate subsidy | — |
| C0 one-coordinate bound under (H1)–(H4) | **the paper-1 nonzero-liability theorem**; refines Proposition 6.1 for stationary margined interior pegs, and instantiates Theorem 4.5's hypothesis | steps 3–4 only (table below) |
| C0 hypothesis necessity (H1)/(H2)/(H3)/(H4) | Remark 3.9 made quantitative; Remark 6.2 demoted (parent) | — |
| C0′ criterion-forced divergence for anti-settlement schedules | **the paper-1 impossibility**; Theorem 4.4 contrapositive + Theorem 3.4 | `AssessmentProcess.lean:217` (`exploits_ofDeductiveProcess`) for the exploitation shape; Theorem 4.4 has no `Contrib` counterpart |
| C2 agreement-condition check; day-uniform income never becomes horizon upside | **Appendix D, Theorem D.1's second hypothesis** shown load-bearing, not bookkeeping | `AssessmentProcess.lean:88` (`Assessment.nested`), `:205`, `:217` |
| C3 flow-quantified biconditional at a stationary interval peg | **converse of Theorem 4.6**, as a §6 remark | — |

### Lean-promotion table for C0

Composition targets for each proof step, and the named gaps.

| step | content | composes from | gap |
|---|---|---|---|
| 1 | MarketMaker day bound at fractional valuations | — | **entire step**: Lemma 3.2 has no `Contrib` counterpart; the source MarketMaker lemmas would have to be lifted |
| 2 | flow–inventory identity at the fixed point | — | **entire step**, and the load-bearing one: needs the fixed point itself, which `Contrib` does not model |
| 3 | throttle conversion `q_j ≤ b_j/(1−hi)` | `AssessmentProcess.lean:704` (`budgetedTrader_netWorth_floor`), `:653` (`BudgeterAt_value_ge_neg_available`), `:628` (`budgetScaleFeature_denote_le_lossCap`) | the geometric step from "worth `≥ −b_j`" to "`q_j(1−hi) ≤ b_j`" — needs entry prices bounded by `hi`, which is step 2's output |
| 4 | aggregation without netting | `AssessmentFirm.lean:127`, `:266`, `:293` | none — this step is available now |
| 5 | billing at `W(φ)=0` | — | **entire step**: convex geometry of the projection trade; Lemma 2.3 has no `Contrib` counterpart |
| 6 | allowance term, `2^-n/p` near a vertex | — | **entire step** |
| 7 | income-channel closure (C1) | — | **entire step**: the sign of the projection trade at the throttling world |
| 8 | tolerance-freedom | — | **entire step**, immediate from step 2 |

**Step 4 is the only step that promotes today.** Steps 3 and 7 are one lemma
each away once step 2 exists; steps 1, 2, 5, 6 require modelling the
MarketMaker fixed point and the projection trade in `Contrib`, which no
existing module begins. A Lean port of this theorem is therefore a
market-side project, not a budgeting-side one — the opposite of where the
existing `Contrib` investment sits.

### Skeleton results: continuation deltas

- **Newly cited, relied on:** Theorem 3.4 (for C0′'s price bound); Definition
  5.1 and Theorem D.1's hypotheses (for C2); Theorem 4.5 (C0 instantiates its
  bounded-liability hypothesis).
- **Strengthened / refined by this continuation (model evidence,
  unregistered):** Proposition 6.1, further — the affordability claim is
  sound only under a no-cross-coordinate-subsidy side condition, which the
  parent round's T2 did not need to state because its fixtures were
  single-coordinate; Theorem 4.6, which gains a converse at a stationary
  interval peg; Appendix D, whose second hypothesis is shown to carry the
  liability–exploitation correspondence.
- **Still untouched:** Sections 5 and 7; Theorem 5.3 and its corollaries;
  Appendices A and C.
