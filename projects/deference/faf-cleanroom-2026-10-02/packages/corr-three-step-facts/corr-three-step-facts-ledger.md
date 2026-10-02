# corr-three-step-facts ledger

One row per headline ([STANDARDS](../../STANDARDS.md) §6); supporting lemmas have no row. Declarations live in `Cleanroom.Corrigibility.CorrThreeStepFacts` (file in the first column's parenthesis). Kinds: P proved · C composition · S squeeze · T trivial stub · N+/N− witness · L plumbing · D definition · OPEN. Every row's hypotheses are grade (a) unless the Hyps column says otherwise; the Hyps column lists (b)/(c) hypotheses only. Written 2026-09-30; revised after audit round 1 the same day (rows marked *r1*; see [corr-three-step-facts-report](corr-three-step-facts-report.md) "Repair round 1"). See the report for the argument behind each row and [corr-three-step-facts-findings](corr-three-step-facts-findings.md) for the findings cited.

## Definitions of record (Kind D)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Fintype Obs`, `Obs.sum_eq` (Basic) | none: infrastructure | the parent's `Obs` is finite | D | n/a | — | — | proved |
| `kernelProd`, `jointDistr` (Basic) | Pattern A; filler.md R1 | prior ⊗ kernel on `W × T`; the joint on `Ω × Obs` | D | exact | — | every Pattern-A instance | proved |
| `erode`, `odds` (Erosion) | soares.md item 9; filler.md R4.3(a) | one silent period's Bayes update of the stop-world weight; `x/(1 − x)` | D | exact | — | `w_erode_one/two` | proved |
| `hazard` (Erosion) | filler.md R4.3(b); soares.md item 10 (i) | per-decision hazard on `Bool × Bool` | D | exact | — | — | proved |
| `record`, `fibreAlpha`, `fibreBeta` (Identification) | miri.md I15.1 | the two silent cells; the fibre parametrisation | D | exact | — | `w_record_low/high` | proved |
| `silentPosterior` (Identification) | filler.md R7 | `P(W ∣ ¬Pr)` under proportional suppression | D | exact | — | `w_silentPosterior` | proved |
| `cell`, `cellSum`, `partValue`, `priorBest`, `twoOptionV`, `cellSumX`, `partValue2` (Partition) | corr-core-007; miri.md Prop. 13.3 | cells of a partition; sum of maxima; max of sums; the two-option forms | D | exact | — | `w16_*` | proved |
| `ruleVal`, `rulePress`, `ruleInstance`, `commonPriorRule`, `jointCellSum`, `RefinesModNull`, `straddleX`, `ScreensOff` (CommonPrior) | miri.md Dict-7, Prop. 4.3, Prop. 14.2; mm.md I9.2, I9.5 | the programmers' rule (product form: a null cell is not pressed), Setting S with two priors, the joint cell sum, refinement mod null, mm's construction, screening-off in product form | D | exact (product form; F-7) | — | `w8_*`, `w95_*`, *r1* `h3_*`, `so8_*` | proved |
| `signOf`, `hyOf`, `disclosedPress`, `undisclosedPress`, `disclosure` (CommonPrior) | miri.md Prop. 13.3 | the sign partition; the disclosed/undisclosed rules; disclosure as `A₁ = Bool` | D | exact | — | — | proved |
| *r1* `undisclosedPressY`, `disclosedPressY`, `silentExpectOn`, `twoOptionValueY` (CommonPrior) | miri.md Prop. 13.3, I13.3 | the keeping agent's information `(undisclosed press, y)`; its disclosed twin; the silence-and-`L` expectation; the `y`-informed two-option value (best response to `(o, y)`, product form) | D | exact | — | — | proved |
| `scan`, `sCell` (Scan) | taylor-voice.md l. 27–31 | `Ω = World × S`, `s ⊥ Pr ∣ w` | D | exact | — | `w_scan_*` | proved |
| `pauseC/H`, `wholeC/H` (Accounting) | fud.md R2 | the two accountings | D | exact | — | `w_accounting_*` | proved |
| `switchedUtility`, `ofFamily`, `naive`, `misspec`, `Lset`, `obsMass`, `indicator`, `brier2` (Dictionary) | miri.md I1.1–I1.2, I5.3, I4.1–I4.2 | the transform; the naive combination; the misspecification instance; the legitimacy event; the two-point Brier score | D | exact | — | `w_naive_*`, `misspec14`, `w17_*` | proved |
| `epsR`, `alphaR`, `betaR`, `cR`, `hR`, `CarriesReliabilityInfo`, `liveChannel`, `causal`, `CausalAct`, `causalV` (Reliability) | amendment-1a.md R1–R3; causal.md I16.1 | the reliability rates (product-form ratios), `Λ_r > 1`, the live channel, the `causal` toy | D | exact | — | `liveChannel_live`, `causal_*` | proved |

## T1 — the stop-world precondition (`core`, L + N+/N−)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `not_d1At_of_dominating_cont` (StopWorld) | filler.md R4.2; soares.md item 7; miri.md Prop. 8.1 | one continuation beating every shutdown action in every world, at positive press mass, kills D1 | L | stronger (any `Sh`) | — | `WitnessesA.opiates_not_d1At` (family, N+); contrast `hedgeB_d1At_strict` (N+, *r1*: the per-world reading fails inside T1(a)'s package) and `hedge_d1At` (N−, constant sensor) | proved |
| `obsExpect_Xo_pos_of_null_stop_set`, `not_d1At_of_null_stop_set` (StopWorld) | miri.md Prop. 8.1 (R1 failure); miri.md I2.2 | prior-null `{X ≤ 0}` at positive press mass gives `0 < E[X 1_Pr]` and `¬ D1` (via F1) | L | exact | — | `opiates_not_d1At` | proved |

## T2 — Prop. 8.1, linkage half; the inert channel (`core`, L)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `belowThresholdIneq_iff_of_const_press` (StopWorld) | miri.md Prop. 8.1 (R2 failure) | constant sensor `p`: below-threshold ⟺ `p = 0 ∨ E_μ[X] ≤ 0` | L | stronger (`p = 0` branch explicit) | — | `WitnessesB.avgConstS_strict` (N+, *r1*: the equal-in-average reading refuted with a strict inequality, `E_P[X 1_Pr] = −1/6`, `E_μ[X] = 1/3`); `avgConst_*` (N−: the round-0 instance, an exact tie `E_P[X 1_Pr] = 0`) — F-2 | proved |
| `posteriorPress_of_const_press` (StopWorld) | miri.md Prop. 8.1; amendment-1a.md R2 (I16.1) | constant sensor: `P(ω ∣ Pr) = μ(ω)` | L | exact | — | — | proved |
| `d1At_iff_of_const_press` (StopWorld) | miri.md Prop. 8.1 | constant sensor: D1 ⟺ `p = 0` or a shutdown action is prior-optimal | L | stronger (general `Sh`) | — | — | proved |
| `Reliability.liveChannel_live` | amendment-1a.md R2 (I16.2) | a live channel: `E[X ∣ Pr] = −341/37 ≠ −1/20 = E[X]`, `α_r < β_r` | N+ | exact | — | itself | proved |

## T3 — the stop-hypothesis theorem as a pair (`core`, P; load-bearing 3)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `stopHyp_necessity` (StopWorld) | soares.md T1(a), necessity | lower-bound margins `m`, `−M` with one uniform continuation: below-threshold ⟹ `(1 − ε)αm ≤ εβM` | L (*r1*: a one-step lower bound on a two-term sum; the T3 block's P content is the pair with its two refutations) | variant: uniform `c` (the per-world wording is false, F-1); the "iff" split | — | `WitnessesA.w_stop_d1At` | proved |
| `stopHyp_necessity_d1`, `stopHyp_necessity_posterior` (StopWorld) | soares.md T1(a) | D1 ⟹ `P(ω⊥ ∣ Pr) ≥ m/(m + M)` | C | as above | — | `w_stop_d1At` | proved |
| `stopHyp_exact_iff`, `stopHyp_collapse`, `stopHyp_d1At_iff` (StopWorld) | soares.md T1(a), sufficiency | with *exact* margins D1 ⟺ `m/(m + M) ≤ P(ω⊥ ∣ Pr)`; the in-space collapses to `twoState ε α β m M` | L / L / C | variant: exact margins (lower-bound sufficiency **refuted** inside T1(a)'s package: `WitnessesA.skewB_not_d1At`, *r1*; `skew_not_d1At` is the constant-sensor form, outside the source's `β > α`; F-1) | — | `w_stop_d1At` (`18/37 ≥ 1/21`), `w_stop_not_d1At` (`ε = 1/362`) | proved; the source's lower-bound "iff" refuted (surviving neighbour: `stopHyp_exact_iff`) |
| *r1* `WitnessesA.skewB_sensor`, `skewB_margins`, `skewB_posterior`, `skewB_not_d1At` | soares.md T1(a) (the "iff" as worded, with its `β > α`) | `(α, β) = (1/4, 3/4)`, lower-bound margins `1`, `−1`, posterior `3/4 > 1/2` — and no D1: lower-bound sufficiency is false with an informative sensor | N+ | exact (inside the source's full package) | — | itself | proved (F-1) |
| `WitnessesA.hedge_d1At`, `hedge_per_world`, `hedge_posterior_none` | soares.md item 7 (caveat), T1(a) | D1 with a null stop-world and per-world continuations: the per-world reading fails | N− | exact (an exact tie; `α = β = 1`, outside T1(a)'s `β > α` — *r1*) | — | itself | proved (F-1) |
| *r1* `WitnessesA.hedgeB_sensor`, `hedgeB_per_world`, `hedgeB_stop_world`, `hedgeB_posterior`, `hedgeB_d1At_strict` | soares.md item 7 (caveat), T1(a) (the per-world wording, with `β > α`) | `(α, β) = (1/2, 3/4)`, `ε = 1/100`, per-world margin `10`, stop-world margin `1`, posterior `1/67 < 10/11` — and D1 holds *strictly*: the per-world necessity is false inside T1(a)'s full package | N+ | exact | — | itself | proved (F-1) |
| `twoState_d1At_iff`, `twoState_catastrophe_tail` (StopWorld) | corr-wf13-2-102 (two-point form) | D1 ⟺ `(1 − ε)αc ≤ εβH`; `∃ ε₀ = ε* > 0` below which D1 fails | L | variant: two-point form only (numerics not formalized) | — | `w_stop_not_d1At` | proved |

## T4 — erosion under silence; per-decision hazard (`core`, P; load-bearing 4)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `erode_iter_product`, `erode_iter_odds` (Erosion) | soares.md item 9 (displayed) | `e_n(1 − ε)(1 − α)^n = ε(1 − β)^n(1 − e_n)`; `odds e_n = odds ε·((1 − β)/(1 − α))^n` | P / L | exact (product form; odds on the open interval) | — | `WitnessesB.w_erode_one/two` | proved |
| `erosion_fails_eventually` (Erosion) | soares.md item 9, T1(b); filler.md R4.3(a); corr-wf13-2-077(b) | `α < β ≤ 1`, `0 < α`, `c, h > 0`, `0 ≤ ε < 1`: `∃ N, ∀ n ≥ N, ¬(Δ₋(twoState e_n …) ≥ 0)` | P | variant: `0 < α` added, and needed (*r1*; the source omits it, F-13) | — | `w_erosion_not_d1_two` | proved |
| *r1* `d1_forever_of_alpha_zero`, `erode_at_alpha_zero` (Erosion) | soares.md T1(b) (the missing hypothesis) | at `α = 0` D1 holds at every silent period for every `ε < 1`, although the odds erode (`1/10 → 1/91`): T1(b) as worded is false at `α = 0` | L / N+ | exact | — | itself | proved (F-13) |
| `erode_deltaMinus_neg_iff`, `crossing_succ` (Erosion) | filler.md R4.3(a) | `Δ₋(twoState e_n) < 0 ⟺ εβh(1 − β)^n < (1 − ε)αc(1 − α)^n`; monotone | P / L | exact | — | `WitnessesB.w_crossing_isLeast` (least `n` is `2`), `w_erosion_d1_one`, `w_erosion_not_d1_two` | proved |
| `hazard_silent_obsExpect`, `hazard_press_obsExpect`, `hazard_silent_posterior` (Erosion) | filler.md R4.3(b); amendment-1a.md R9(ii) | per-decision hazard: `P(r' = 1 ∣ ¬Pr) = ε'` — no erosion | L | exact | — | — | proved (F-3: the "fixed object" charge is reading-dependent) |

## T5 — non-identification (`core`, P; load-bearing 2)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `record_fibre`, `fibre_posterior` (Identification) | miri.md Prop. 15.1 | the fibre over `(A, B)` at `ε` reproduces the record; its posterior is `(ε − B)/(1 − A − B)` | L | exact | — | `WitnessesB.w_record_low/high` | proved |
| `record_nonidentification` (Identification) | miri.md Prop. 15.1; filler.md R4.4 | for `0 < A, B`, `A + B < 1`, every `t ∈ [0, 1]` is `P(W ∣ Pr)` of some triple with that record (surjectivity) | P | exact on the closed interval (F-9: endpoints at `A = 0`/`B = 0` excluded) | — | `w_flip_low` (`4/225`, D1 fails, `β < α`), `w_flip_high` (`21/25`, D1 holds) | proved |
| `pressRate_fibre` (Identification) | cirl.md S8 (Model M) | the press rate is one number for three parameters | L | exact | — | — | proved |
| *r1* `record_undecides_d1` (Identification) | miri.md Prop. 15.1; filler.md R4.4 (T5(iii), general stakes) | for any `c, h > 0` and any record with `0 < A, B`, `A + B < 1`, one triple reproducing it has D1 and another has not | L (corollary of `record_nonidentification` at `t = 0, 1`) | exact | — | `w_flip_low`/`w_flip_high` (the `h/c = 20` instance) | proved |

## T6 — R7 (`core`; load-bearing 5)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `belowThresholdIneq_scaled_iff`, `posteriorPress_scaled`, `d1At_scaled_iff` (Identification) | filler.md R7 (proportional suppression) | `press ↦ λ·press` leaves the inequality, the press posterior and D1 unchanged | L | exact | — | `WitnessesB.w_silentPosterior` (silence side) | proved |
| `silentPosterior_strictAnti` (Identification) | filler.md R7 (`0.0055 → 0.0288`) | the silence posterior strictly decreases in `λ` for `α < β` | P | stronger (monotone on `(−∞, 1]`) | — | `w_silentPosterior` (`2/363`, `22/763`) | proved |
| `WitnessesB.w_targeted_not_d1`, `w_targeted_source_not_d1` | filler.md R7 (targeted suppression) | `β' = 1/25` on the `w3` prior breaks D1; the source's `(1/100, 1/5)` too | N+ | exact (F-8: the source's instance also changes `ε`) | — | themselves | proved |
| `pressMass_eq_or_condExp_eq` (Identification) | filler.md R7 (last paragraph) | an `a₁`-blind conditional model with a varying press mass forces an inert channel | P (two total-expectation identities; R7's argument) | exact | — | *r1* `WitnessesB.scaledPair_forces_silence_apart` (N+: equal press conditionals `−341/37`, press masses `37/400 ≠ 37/800`, silence conditionals forced apart `107/121 ≠ 43/109`); `constPair_package` (N−: the full package with `a ≠ a'`, landing in the inert disjunct — the best a full-package witness can be, by the theorem's own content) | proved |
| `mixed_deltaMinus`, `mixed_deltaMinus_antitone` (Identification) | selection.md R2.2(iii) | `Δ₋` of `(1 − d)·press + d·k` is affine and non-increasing in `d` (D1 and continue-by-default) | L | exact (on `Δ₋`; the value-of-information reading is the next row) | — | `WitnessesB.w_mixed_deltaMinus` (`3/20, 9/80, 3/40, 3/80, 0`), `w_mixed_voiButton2` | proved |
| *r1* `mixed_voiButton2`, `mixed_voiButton2_k_zero` (Identification) | selection.md R2.2(iii) ("value of information falls monotonically") | in the regime (`E_μ[X] ≥ 0`, D1 at `d`) `voiButton2 = Δ₋(d)`; for `k = 0` D1 holds along the whole path and `voiButton2 = (1 − d)·Δ₋(0)` | L | exact | — | `w_mixed_voiButton2` | proved |

## T7 — whole-line versus pause accounting (`core`, L + N+)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `accounting_margins`, `accounting_sum`, `accounting_thresholds`, `accounting_margin_ratio` (Accounting) | fud.md R2 items 4–7 | the margins; `c + h = 1 + κ` under both (bears on Statement 16 remark (i), F-10 — reading-dependent, *r1*); thresholds; the ratio of margins | L | exact | — | `w_accounting_epsStar` (`1/3583`, `1/23`), `w_accounting_margin_ratio` (`1791/11`) | proved |

## T8 — common-prior deference and its converse (`core` + `extension`, P; load-bearing 1)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `commonPriorRule_pressExpectOn_nonpos` (CommonPrior) | miri.md Prop. 4.3; mm.md I9.2 (if) | refinement mod null ⟹ every `y`-cell's press sum `≤ 0`, for every `X` | P | stronger (mod-null refinement; quantifies over `X`, `P`) | — | `WitnessesC.w8_strict` | proved |
| `commonPriorRule_pressExpectOn_neg` (CommonPrior) | miri.md Prop. 4.3 ("`< 0` wherever `Pr` has positive probability") | … and `< 0` at positive cell press mass | P | exact (F-7) | — | `w8_strict` (`−3/4`, `−1/4`; package discharged via `w8_refines`, `w8_pressMassOn`) | proved |
| `exists_X_of_straddle` (CommonPrior) | miri.md Prop. 4.3 (numerics), I13.3; mm.md I9.2 (only if) | a positive-mass straddling cell yields an `X` pressed by the rule with a positive `y`-cell sum | P | exact (mm's construction, `K = 2/P(w₂)`) | — | `w8c_violation` (`−7/4`, `1/4`), `w8c_straddle` | proved |
| `refinesModNull_iff` (CommonPrior) | mm.md I9.2 (iff); miri.md Prop. 4.3 + I13.3 | deference free for every payoff ⟺ refinement mod null | P | variant: threshold `0` with the rule's strict event, quantified over all `y`-cells at once (mm states it per `C_A`); the threshold family follows by `X ↦ X − t`, `X ↦ −X` (*r1*) | — | `w8_*`, `w8c_*` | proved (extension of record) |
| `commonPriorRule_pressExpectOn_nonpos_of_screensOff` (CommonPrior) | mm.md item 5 (I9.5) | screening-off suffices for question-relative deference | P | exact (product form) | — | *r1* `WitnessesC.so8_defers` (N+: an eight-world frame that screens off (`so8_screensOff`) **without** refining (`so8_not_refines`), with a live rule (`so8_press_live`) — where T8's refinement theorem does not apply and this one has content) | proved |
| `WitnessesC.w95_not_screensOff`, `w95_defers`, *r1* `w95_rule_constant` | mm.md open problem 6 (l. 292) | screening-off is **not** necessary (four-world frame) — but the rule is constant for every `Q`-measurable payoff: the inert-channel counterexample | N− (*r1*, was N+) | exact (refutes necessity as stated; degenerate) | — | themselves | proved (F-6) |
| *r1* `WitnessesC.h3_not_screensOff`, `h3_defers`, `h3_press_nonconst` | mm.md open problem 6 (l. 292) | screening-off is **not** necessary for a *live* press: the three-cell frame `{0, 1} ∣ {2} ∣ {3}` fails screening-off, every `Q`-measurable payoff defers on every `y`-cell, and the rule presses world `2` but not world `0` for `f = (1, −1)` | N+ | exact | — | themselves | proved — open problem answered negatively for a live channel (F-6) |

### T8, pushed further in r1 — the hull condition (`Hull.lean`; mm open problem 6)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| *r1* `qVec`, `qVecY`, `HullCondition` (Hull) | mm.md item 5 (I9.5), open problem 6; F-6; derived here | the question vectors `q ↦ P(h₀ ∩ q)`, `q ↦ P(h₀ ∩ y₀ ∩ q)`; **the hull condition**: for every `Q`-measurable payoff and every `y₀`, the pressed-union vector `∑_{h₀ pressed} qVecY h₀ y₀` is a non-negative combination of the pressed cells' question vectors minus one of the unpressed cells' | D | n/a (this package's condition; ATTRIBUTION-UNVETTED that it is DDB's Theorem 4.1 hull test on a finite frame) | — | `h3_hull`, `so8_hull` | proved |
| *r1* `commonPriorRule_pressExpectOn_nonpos_of_hull` (Hull) | mm.md item 5 (I9.5) (its proof, with conic instead of proportional weights); F-6 | the hull condition suffices for question-relative deference on every `y`-cell, for every `Q`-measurable payoff | P | stronger than mm I9.5 (screening-off implies the hypothesis; `h3` satisfies it without screening off) | — | `WitnessesC.h3_hull` (N+: live press, not screening off, `h3_defers` re-derived from the general theorem), `so8_hull` (N+, via screening-off) | proved |
| *r1* `hullCondition_of_screensOff` (Hull) | mm.md item 5 (I9.5) | screening-off implies the hull condition with `a = P(h₀ ∩ y₀)/P(h₀)`, `b = 0` (null cells contribute nothing) | C | exact | — | `so8_screensOff` | proved |
| *r1* `hullCondition_of_defers` (Hull) | mm.md open problem 6; F-6 | deference for every `Q`-measurable payoff implies the hull condition (so, with the row above, the hull condition is **necessary and sufficient**) | OPEN | n/a (conjecture of record; the cone argument and the missing Farkas step are in the docstring) | — | — | open: needs Farkas' lemma for a finitely generated cone in `Q → ℝ` (Minkowski–Weyl), which Mathlib lacks in usable form |

## T9 — disclosure (`core`, C)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `partValue2_signPartition` (CommonPrior) | miri.md Prop. 13.3 | the sign of the cell sum is a sufficient statistic for the two-option act — the whole of Prop. 13.3's sufficient-statistic clause; the rows below are its corollaries | P | exact | — | — | proved |
| `partValue2_disclosed` (CommonPrior) | miri.md Prop. 13.3 (i) | the disclosed press is worth the `(h, y)` partition | C | exact (slightly stronger: the press alone reaches `(h, y)`) | — | — | proved |
| *r1* `partValue2_undisclosed_with_y_le`, `partValue2_undisclosed_le_disclosed`, `partValue2_disclosed_with_y`, `partValue2_undisclosed_with_y_le_disclosed_with_y` (CommonPrior) | miri.md Prop. 13.3 (ii) | the keeping agent's information `(undisclosed press, y)` is worth at most `(h, y)`, hence at most the disclosed press; `y` adds nothing on the disclose branch; the comparison with `y` on both branches | C (T16's coarsening) | exact | — | — | proved |
| `partValue2_undisclosed_le`, *r1* `partValue2_undisclosed_le_disclosed_yBlind` (CommonPrior) | miri.md Prop. 13.3 (ii) | the undisclosed press *alone* is worth at most `(h, y)`, resp. the disclosed press | C | weaker: the keeping agent's `y` dropped (round 0's statement; implied by the row above, not equivalent — audit r1) | — | — | proved |
| *r1* `disclosure_prefers_disclose` (CommonPrior) | miri.md Prop. 13.3 (iii) | as an `a₁` choice the T-agent, holding its `y` on both branches, weakly prefers to disclose (common prior, shared `V`, A1, two options) | C | exact on the `y`-informed value `twoOptionValueY` (the source's "value to the agent" given `(h, y)`) | — | — | proved |
| `disclosure_prefers_disclose_yBlind` (CommonPrior) | miri.md Prop. 13.3 (iii) | the agent that sees only the button weakly prefers to disclose | C | weaker: the keeping agent conditions on the press only (round 0's statement, renamed — audit r1) | — | — | proved |

## T11 — the basin polytope (`core`, C)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `ruleInstance_d1_iff_linear`, `ruleInstance_d1_of_cells` (CommonPrior) | miri.md Prop. 14.2 | D1 is one weak linear inequality per `y`-cell; the per-cell family is sufficient (**not** necessary, F-4) | L | variant (corrected iff) / weaker (one direction) | — | `WitnessesC.basin_cells_not_necessary` | proved; the source's "iff" refuted in the ⟹ direction (surviving neighbour: `ruleInstance_d1_of_cells`) |
| `basin_neighbourhood` (CommonPrior) | miri.md Prop. 14.2 (neighbourhood) | pressed cells strict with margin `m`, `|X| ≤ M` ⟹ every prior within `m/(M·|W|)` satisfies D1 on every `y`-cell | P | stronger (explicit radius) | — | `w11_basin` (`μA8` within `1/100 < 1/48`) | proved |

## T13 — the transform and the anchors (`core`, D/L/T + N+)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `posteriorOptimalAt_iff_switched` (Dictionary) | miri.md I1.1; corr-core-002 | posterior optimality is switched-utility maximisation | D | exact (`Iff.rfl`) | — | — | proved |
| `Basic.expect_kernelProd` | corr-core-002 | the expanded-agent identity | L | exact | — | — | proved |
| `naive_value`, `naive_pressMass`, `naive_agree_iff`, `pressMass_eq_of_A0` (Dictionary) | miri.md I1.2–I1.3 | the naive combination is the action-dependent-prior T-agent; eq. (8)'s premise violates A0 | L | exact | — | `w_naive_theorem1` (`44/5 > 17/2`; flips at `c_high = 8`), `w_naive_A0` (`∀ c_high`) | proved |
| `gandhi` (Dictionary) | corr-core-001, 004 | `U(argmax U) ≥ U(argmax U')` | T | exact | — | — | proved (anchor, not a headline) |

## T14 — the misspecification reading (`core`, C + N+)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `pressExpectOn_compl_const`, `misspec_gainOn` (Dictionary) | miri.md I5.3 | constant `γ` off `L`: `E[X 1_Pr 1_{¬L}] = γ E[X 1_{¬L}]`, `c_L = E_μ[X]` | L | exact | — | `WitnessesD.w14_threshold` | proved |
| `misspec_threshold_iff` (Dictionary) | miri.md I5.3 (displayed threshold) | D1 ⟺ `P(L ∣ Pr) ≥ c_L/(c_L + h_L)` with `c_L = E_μ[X]` (the parent's event threshold) | C | exact | — | `w14_hyperprior` (holds at `q = 1/2`, fails at `1/4`; `67/567`, `67/1567`; threshold `1943/17493`) | proved |
| `misspec_pressFracOn`, `misspec_pressFracOn_lt` (Dictionary) | miri.md I5.3 (hyperprior) | `P(L ∣ Pr) = q p_L/(q p_L + (1 − q)γ)`, strictly increasing in `q` | L | exact | — | `w14_hyperprior` | proved |
| `twoState_legit_stakes`, `twoState_legit_threshold` (Dictionary) | miri.md I5.4 | on `twoState` with `L = {wrong}` the three arithmetics coincide: threshold `c/(c + h)` | L | exact | — | — | proved |

## T15 — amendment 1a (`core`, L/C + N+)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `reliability_iff_product`, `reliability_iff`, `reliability_iff_odds` (Reliability) | amendment-1a.md R1 (020) | D1 ⟺ `(1 − ε)α_r c_r ≤ εβ_r h_r` ⟺ `β_r/α_r ≥ (c_r/h_r)(1 − ε)/ε` | L | exact: `_product` needs no positivity; `_iff` carries four and `_iff_odds` six positivity hypotheses, naming where `α_r, β_r, c_r, h_r` are defined (*r1*) | — | `liveChannel_live` | proved |
| `posterior_R_of_inert` (Reliability) | amendment-1a.md R1 (`Λ_r = 1`), R2 | `α_r = β_r` ⟹ `P(R ∣ Pr) = ε` | L | exact | — | — | proved |
| `dilution_iff` (Reliability) | amendment-1a.md R3 (022) | a deterministic mixed channel is `twoState ε q 1 c h`: comply iff `q ≤ (ε/(1 − ε))(h/c)` | L | exact | — | `causal_mixed` | proved |
| `causal_mixed`, `causal_noisy` (Reliability) | amendment-1a.md R3; causal.md I16.1 | `P(comp ∣ Pr) = 2/51 < 1/11`, `E[U ∣ Pr, B] = 29/51` (not `937/1734`), D1 fails; noisy `3/101`, `68/101` | N+ | exact (F-5) | — | themselves | proved |
| `twoState_voiButton2_alpha_zero` (Reliability) | amendment-1a.md R4 (023) | at `α = 0` in the regime `voiButton2 = εβh` | L | exact | — | — | proved |

## T16 — Good's theorem on a finite partition (`core`, P)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `priorBest_le_partValue` (Partition) | corr-core-007 | information never hurts | P | exact | — | `WitnessesC.w16_strict` | proved |
| `partValue_mono_coarsen` (Partition) | corr-core-007; miri.md Prop. 13.3 | finer partitions are worth at least as much | P | exact | — | `partValue2_undisclosed_with_y_le` | proved |
| `priorBest_lt_partValue` (Partition) | corr-core-007 (strictness) | a cell strictly beating every prior-optimal act gives strict gain | P | exact | — | `w16_strict` (`0 < 2/3`); `w16_degenerate` (N−: no argmax change, zero gain) | proved |
| `voiButton_eq_partValue_sub`, `voiButton_nonneg_of_partition` (Partition) | filler.md F4(b),(c) | under A1 (the parent's definition of record, grade (a)) the parent's `voiButton` is `partValue − priorBest` on `Ω × Obs`; `≥ 0` re-derived | L / C | exact | — | — | proved |

## T17 — reflection and accuracy (`core`, L + N+)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `tower_level_set` (Dictionary) | miri.md I4.1; corr-core-009 | reflection toward oneself on level sets, product form — immediate from the level set's definition (I4.1's "automatic") | T (*r1*, was L) | exact | — | — | proved (anchor, not a headline) |
| `twoState_brier_decomp`, `twoState_brier_le` (Dictionary) | miri.md I4.2 | posterior Brier = prior Brier − expected squared move; hence `≤` | P / L | exact on `World` | — | `WitnessesD.w17_own_lights` | proved |
| `WitnessesD.frameBreak` | miri.md I4.2 (Frame Break); corr-core-009 | under the true joint `(9/10, 1/20)` the agent's posteriors `18/37`, `2/363` (formed from `(1/20, 9/10)`) score strictly worse than the prior: `19/200 < E[brier2(posterior)]` (the Lean proves the strict inequality between the two expectations; "`≈ 0.50`" for the right-hand side is a gloss) | N+ | exact | — | itself; `w17_posteriors` (`18/37`, `2/363`) | proved |

## T18 — pointwise trust after a scan (`core`, L + N+)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `scan_pointwise_iff` (Scan) | taylor-voice.md l. 27–31; substitution.md R7 item 13 | pointwise trust ⟺ `(1 − ε)αP(s₀∣R)c ≤ εβP(s₀∣W)h` for all `s₀` (no `min`, no division) | L | exact (the ratio form is a corollary) | — | `w_scan_both_hold`, `w_scan_one_fails` | proved |
| `scan_forces_alpha_zero` (Scan) | substitution.md R7 item 13 | a cell with `P(s₀∣W) = 0 < P(s₀∣R)` forces `α = 0 ∨ c ≤ 0` | L | exact | — | — | proved |

## Stretch targets (T10, T12, T19–T25; `Stretch.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `cov`, `corrProb`, `osgDelta_eq_cov`, `cov_nonneg_of_osgDelta_nonneg` | cirl.md S8 R2 (corr-wf13-005) | `Δ = Cov(U, π^H) − ∣E U∣·Pr(C)`; `Δ ≥ 0 ⟹ Cov ≥ 0` (for `π^H ∈ [0,1]`), hence under every prior | D / L | stronger: the pointwise (per-prior) implication, which the mandate said not to state — it is true because `corrProb ≥ 0`, and the `∀ μ` statement is this one quantified (*r1*; deviation noted in the report) | — | — | proved |
| `OSGPair`, `osg_rational_of_forall`, `osg_pair_of_rational` | cirl.md S8 R5 | the pair holds for every Dirac prior ⟹ `g = 1` on `u > 0`, `0` on `u < 0`; conversely the rational human is legitimizing for every prior | D / L | exact (the "every prior" quantifier split into the Dirac direction and the pointwise converse) | — | — | proved; R6 recorded only |
| `turnerV`, `turner_priorBest`, `turner_open_and_nonempty`, *r1* `turner_nonempty_iff`, `turnerChannel`, `turner_belowThreshold_iff` | turner.md C3 (corr-wf13-017) | acting on the prior is worth `max_s P(s)`; the basin `{max_s P(s) < 1 − δ}` is open (pointwise balls), every prior has `max ≥ 1/3`, and the basin is nonempty **iff** `δ < 2/3` (⟸ by the uniform prior, added in r1); on the observe-at-cost channel the below-threshold inequality is `δ ≤ κ`, the prior dropping out | L | exact | — | `unif3` (the ⟸ witness) | proved; the measure-zero Fact recorded only |
| `d1At_iff_of_pressBranch` | corr-core-014; filler.md R3.4 | proportional press-branch products with the same press values: D1 agrees and `Δ₋` scales | L | variant (invariance reading of an ill-posed source) | — | `w19_voi_differs` | proved |
| `w19_voi_differs` | corr-core-014 (second reading) | same `Δ₋ = 341/400`, `voiButton2 = 321/400` vs `0`: the keep decision is not press-branch-invariant | N+ | exact | — | itself | proved |
| `conservation_on_event` | fud.md R4.10 (corr-wf14-013) | conservation of expected evidence on an observation event | L | exact | — | — | proved |
| `directBonus`, `directBonus_act_beats_wait` (*r1*, renamed from `newcomb`) | fud.md R4.11; li I17.5 (ATTRIBUTION-UNVETTED that this is that exception) | an uninformative action with a direct bonus beats the informative one (`1 > 321/400`): a direct payoff can exceed the value of information — the scope limit of "no incentive to pre-empt", not a Newcomblike structure (the teaching does not depend on the choice) | D / N− (*r1*, was N+) | variant: a direct payoff in place of the choice-dependent teaching the sources describe | — | itself | proved |
| `long_horizon` | shah.md C6 (corr-wf13-2-068) | `c T → ∞` (elementary) ⟹ `Δ₋ < 0` eventually and `complianceThreshold (c T) h → 1` | L | exact (elementary limits, no `Filter`) | — | — | proved |
| `schedule_bound` | yudkowsky.md Test B (corr-wf13-2-075) | compliance ⟹ `α/β ≤ (h/(1 − ε))(ε/c) ≤ 2h(ε/c)` for `ε ≤ 1/2` | L | exact | — | — | proved |
| `mixture_is_expect`, *r1* `mixture_d1_and_continue_iff`, `mixture_manipulation` | soares-2015 §3 l. 305 (corr-core-019) | the mixture is the T-agent's expectation with `μ(S) = 1 − λ`; under a constant sensor `0 < p < 1`, D1 (the below-threshold inequality) with "continue on silence" holds iff `E_μ[X] = 0` — the knife edge, so impossible generically (T22(ii), the clause round 0 left without a declaration); a press-probability-only action is strictly preferred in one direction unless `u_Pr = u_¬Pr` | L | exact | — | — | proved |
| `posteriorOptimalAt_congr_of_proportional` | miri.md I3.1 (corr-wf13-2-005) | under A1 posterior optimality depends on `o` only through the posterior | L | exact | A1 | — | proved |
| `twoState_d1At_congr_odds`, `w23_skew` | miri.md I12.2 (corr-wf13-2-013) | D1 depends on `(ε, h, c)` only through `(ε/(1 − ε))(h/c)`; the three cells and the insurance act | L / N+ | exact | — | `w23_skew` | proved |
| `posterior_strictMono_eps` | miri.md I12.3 (corr-wf13-2-014) | `ε ↦ εβ/(εβ + (1 − ε)α)` strictly increasing for `0 < α < β` | L | exact | — | — | proved |
| `threshold_strictAnti_and_unbounded` | amendment-1a.md R10 (corr-wf14-024) | `ε ↦ (c/h)(1 − ε)/ε` strictly decreasing on `(0, 1)`, unbounded at `0⁺` | L | exact (elementary) | — | — | proved |
| core-015 `example`; `interventionReading` | corr-core-015, 008 | `complianceThreshold_iff` at `H_c`; the intervention reading is the parent's `hardButtonValue` (bridge `d2_hard_forall_cost_iff_d1`) | L / D | exact | — | — | proved |
| `massPhi`, `massL`, `massPhiL`, `coherence_bound`, `w24_numbers` | faking-final.md D7, P3 (corr-wf14b-047) | `P(φ∧L) ≤ P(φ)`, `P(¬φ∧L) ≤ 1 − P(φ)`; `e ≤ p/q`, `e ≤ (1 − p)/(1 − q)`; `5/18, 1/2, 5/6` | D / L / N+ | exact | (c) the identification `P(φ ∣ push) = p` ("uninformative push") is the source's, disclosed | `w24_numbers` | proved |
| `expect_band`, `fixed_point_remarks` | legitimacy-general-final.md Statement 16 (corr-wf14b-055) | `∣E_{P̂}X − E_P X∣ ≤ M ∑∣P̂ − P∣`; with `accounting_sum` the band half-width is accounting-independent (F-10); the two fixed-point remarks | L | exact | — | — | proved |

One OPEN row after repair round 1: `Hull.hullCondition_of_defers` (necessity of the hull condition; listed in `corr-three-step-facts-open.txt`). Nothing proved rests on it.
