# corr-osg-chai — ledger

*One row per headline ([STANDARDS](../../STANDARDS.md) §6). Namespace prefix `Cleanroom.Corrigibility.CorrOsgChai.` omitted; `POOSG.`-namespaced declarations take `G : POOSG S ΩH ΩA`, `Supervision.`-namespaced ones take `M : Supervision Θ A`. Hyps column lists only (b)/(c); "—" means every hypothesis is (a) (named in the statement, nothing hidden; the standing hypotheses A1, `0 < ε < 1/100`, the parameter ranges, the posterior-mean predicate are (a) in that sense). Status `proved` unless stated. Kinds as in §6; `S` and `T` where earned (T4's Prop. 4, T13's Theorem 1). The load-bearing headlines are marked **LB-n**.*

## Definitions of record (Kind D)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `rationalAllow`, `pRationalAllow` | HM 2017 Eq. 2; Wängberg Def. 3 | `𝟙[U ≥ 0]` (ties allowed at `0`); `p` on `U ≥ 0`, `1 − p` on `U < 0` | D | exact | — | `w_theorem1` | proved |
| `AAct`, `HAct`, `through` | Garber Def. 3.2 | `{a, w(a), OFF}`, `{ON, OFF}`, Def. 3.2's `α` | D | exact | — | — | proved |
| `POOSG`, `POOSG.u`, `payoff`, `optValue`, `IsOPP`, `withObs`, `obsH`, `obsA` | Garber Defs 3.1–3.2, 4.6 | finite PO-OSG on FAF's `Distr`; deterministic payoff; `sup'` over the inhabited pair type; OPP (instances: `fileDeletion`, `exA13S1`, `coarse`, `fine`, `osgAsPOOSG`) | D | exact (finite; deterministic pairs, see Cor. A.6 rows) | — | — | proved |
| `POOSG.payoffStoch`, `POOSG.stochWeight` | Garber Def. A.2; Lemma A.5 | stochastic pairs, independent randomisation, nested `expect`; the product weight a stochastic pair puts on a deterministic pair (repair round 1) | D | exact | — | — | proved |
| `ObsGarbling`, `Independent`, `Coordinated`, `MoreInformative`, `MoreInformativeForH`, `MoreInformativeForA` | Garber Defs 4.4–4.5 | garblings into `Distr`; product kernels; finite simplex mixtures; `O₂ = ν ∘ O₁`, `ν` coordinated | D | exact | — | `exA13_isGarbling` (uncoordinated), `fine_moreInformativeForH_coarse` | proved |
| `POOSG.NoPrivateA`, `NoPrivateH` | Garber Def. A.11 | `OA = f(OH)` at every `(s, oH, oA)` of positive joint mass — the a.s. statement under `P0 ⊗ obs` (repair round 1: `P0`-null states no longer constrained, audit r1 N2) | D | exact (on the support of the joint law) | — | `osgAsPOOSG` (via `RedundantA`) | proved |
| `POOSG.RedundantA`, `RedundantH` | Garber Def. 4.2 | `O(oH, oA | s) = OH(oH | s) K(oA | oH)` at every `P0`-positive state, product form, `K` fixed on null rows (disclosed) (repair round 1: on the support of `P0`, audit r1 N2) | D | exact (Markov-chain reading in product form, on the support) | — | `osgAsPOOSG_redundantA` | proved |
| `fileDeletion`, `fdCol` | Garber Ex. 4.1 | Table 1, uniform, deterministic projections; the column through-sets | D | exact | — | — | proved |
| `exA13S1`, `exA13O2` | Garber Ex. A.13 | `2 − 3·𝟙[s₁ = s₂]`; Structures 1, 2 | D | exact | — | — | proved |
| `coarse`, `fine`, `colC`, `colF` | Garber Ex. 4.10 | Table 2 (re-read against l. 563–566); first digit vs full version | D | exact | — | `fine_four_cases` | proved |
| `osgAsPOOSG` | Garber §4.2 | the original OSG as a PO-OSG with `ΩA = Unit` | D | exact | — | — | proved |
| `pressExperiment` | detection.md R6 | the press as an `Experiment Ω (Fin 2)` | D | exact | — | `twoState_pressExperiment_k` | proved |
| `cellExpect`, `CellBelow`, `CellAbove`, `CellwiseBelow`, `CellwiseAbove`, `refinedValue` | detection.md R7 K5; taylor.md §2.2 | product-form per-cell quantities; K5; the refined two-option value | D | exact (no conditional distribution) | — | `fileDeletionTS`, `taylor` | proved |
| `fileDeletionTS`, `cellL`, `cellM`, `taylor` | detection.md R1; taylor.md §2.2 | the File Deletion Game as a product `ThreeStep`; its cells as `twoState (1/2) 1 0 3 1`, `twoState (1/2) 0 1 5 5`; Taylor's brain-state instance | D | exact | — | — | proved |
| `POOSG.cellPayoff`, `cellPressX`, `cellSilentX`, `WaitBestResponseOn`, `negGame` | chai.md Test A / C1 | per-cell payoff and the two cellwise clauses with the press read as `πH = off`; the R2 failure game | D | exact | — | — | proved |
| `Supervision` (+ `post`, `Q`, `obedience`, `advantage`, `IsPosteriorMean`, `TieBreakObedient`, `Rational`, `Undominated`, `IsIRL`), `milliExample` | Milli §2, Thm 1–3, Lemma 1 | D6: finite supervision model, unnormalised posterior, obedience, advantage; the tie-break stated | D | variant: general `R`, not `θᵀφ(a)` | — | `milliExample` | proved |
| `CAct`, `RR`, `rewardTrue`, `rewardR`, `lik`, `score`, `robot`, `fig1Value`, `fig2aValue`, `fig2bValue` | Carey Def. 1, Figs 1–2 | D7: explicit trees; ε-noisy likelihood; posterior-mean rule in product form with explicit tie-break | D | exact (Fig. 2a's `R₁` second move: variant, see row) | — | — | proved |
| `nayebiHarmful`, `nayebiBeneficial` | Nayebi Prop. 2 | the two games of the proof | D | exact (`ε = 1/2`) | — | — | proved |

## T1–T4 — the off-switch game over `osgDelta`

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `osgDelta_eq_min` | HM Eq. 1 | `Δ = min(E[−U(1−π)], E[Uπ])`, no bound on `π` | L | stronger (no `[0,1]`) | — | `w_theorem1` | proved |
| `rationalAllow_eq_allowProb` | HM Eq. 2 / Wängberg §3.3 | the rational human is the two-type human at `p_r = 1` | L | exact | — | — | proved |
| **LB-1** `osgDelta_rational_eq`, `osgDelta_rational_nonneg` | HM Thm 1 cl. 1 | `Δ = min(E[U1_{U≥0}], −E[U1_{U<0}]) ≥ 0`, derived from Thm 9 | C | exact | — | `w_theorem1` (N+), `w_theorem1_degenerate` (N−) | proved |
| **LB-1** `osgDelta_rational_pos_iff` | HM Thm 1 cl. 2 | `Δ > 0 ↔` strict mass on both signs | C | stronger (iff) | — | `w_theorem1` | proved |
| `osgDelta_delta` | HM Cor. 1 Eq. 4 | Dirac closed form, branches corrected (F-2) | L | variant: printed branches swapped | — | `w_chance_node` | proved |
| `osgDelta_delta_nonneg_iff` | HM Cor. 1 | per-point iff, no bound | L | exact (the proof's content) | — | — | proved |
| `forall_osgDelta_delta_nonneg_iff` | HM Cor. 1 | function-level "iff H is rational" on `U ≠ 0` (F-3) | L | variant | — | — | proved |
| `osgDelta_const_le`, `osgDelta_const_eq_zero_iff` | HM §3 chance node | `Δ ≤ 0`; `= 0 ↔ (E>0 → p=1) ∧ (E<0 → p=0)` (mandate's iff corrected, F-15) | L | stronger | — | `w_chance_node` | proved |
| `pRationalAllow_eq_allowProb` | Wängberg Prop. 4 | `rfl` on the two-action menu | T | exact | — | — | proved (T by design) |
| `osgDelta_allowProb_nonneg_iff` | Wängberg Cor. 10 + the `s` remark | `Δ ≥ 0 ↔ (4) ≤ 0 ∧ 0 ≤ E[U | w(a)]` | L | exact | — | — | proved |

## T8 — Theorem 4.7 (⇐), Cor. A.6, Prop. A.12, Prop. 4.3

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Basic.exists_det_ge` | Garber Lemma A.3(a) | fibrewise deterministic choice never lowers a weighted expectation | L | n/a | — | — | proved |
| `POOSG.payoffStoch_le_optValue` | Garber Lemma A.3/A.5 | no stochastic pair beats the deterministic optimum | P | exact | — | — | proved |
| `POOSG.optValue_isGreatest_stoch` | Garber Cor. A.6 (bound) | the deterministic optimum is the greatest stochastic payoff | C | exact for the bound (`IsGreatest`, not `sSup`: deviation 4); the uniqueness clause is the next rows | — | — | proved |
| `POOSG.payoffStoch_eq_sum_det` | Garber Lemma A.5; mandate D2 | a stochastic pair's payoff is the mixture of deterministic payoffs with the product weights `stochWeight` (repair round 1) | P | exact | — | — | proved |
| `POOSG.isOPP_of_stochWeight_pos` | Garber Lemma A.5 | an optimal stochastic pair puts weight only on OPPs (repair round 1) | P | exact | — | — | proved |
| `POOSG.stoch_opt_dirac_of_unique` | Garber Lemma A.5 / Cor. A.6 (uniqueness clause) | a unique deterministic OPP is the unique optimal pair among stochastic pairs: every optimal stochastic pair is Dirac at it (repair round 1, audit r1 B1) | C | exact | — | `fileDeletion_unique_stoch` | proved |
| `POOSG.payoffVia_eq_payoffStoch_of_independent` | Garber Thm 4.7 (⇐), independent case | composing policies with the kernels simulates an independent garbling | P | exact | — | — | proved |
| **LB-3** `POOSG.optValue_withObs_le_of_moreInformative` | Garber Thm 4.7 (⇐) | a coordinated garbling never raises `optValue`, for every `P0, ua, uo` | C | exact ((⇐) only) | — | `exA13_not_coordinated` (the hypothesis is load-bearing), `fine_moreInformativeForH_coarse` | proved |
| `POOSG.moreInformative_of_forall_optValue_le` | Garber Thm 4.7 (⇒) | better in optimal play for every prior and payoff ⇒ more informative (a finite coordinated garbling) — the paper's direction via Lehrer–Rosenberg–Shmaya (mandate S15/E1; filed in repair round 1, audit r1 N7) | OPEN | exact (the paper's statement) | — | — | open (`corr-osg-chai-open.txt`) |
| `POOSG.exists_opp_alwaysWait_of_noPrivateA`, `…_neverWait_of_noPrivateH` | Garber Prop. A.12 | no private observations (on the support) ⇒ an OPP always / never waits | P | exact | — | `osgAsPOOSG` (through `RedundantA`) | proved |
| **LB-3** `POOSG.exists_opp_alwaysWait_of_redundantA`, `…_neverWait_of_redundantH` | Garber Prop. 4.3 | redundant (Def. 4.2 on the support of `P0`) ⇒ an OPP always / never waits: the null-state edit (`isOPP_withObs_iff_of_eq_on_support`) then the paper's proof (`…_of_factor`) | C | exact (one direction; converse false, F-9) | — | `osgAsPOOSG_exists_alwaysWait_opp` (N+), `fileDeletion_not_redundantA/H` (the hypothesis fails where the conclusion fails), `trivialGame_all_opp` (N−) | proved |
| `POOSG.payoff_le_sum_max` | Garber Ex. 4.1 (dominance step) | best-conceivable-through-set bound | L | n/a | — | `exA13S2_optValue` | proved |

## T7 — the File Deletion Game (LB-2)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `fileDeletion_payoff_cols`, `fdCol_M`, `fdCol_L` | Garber Ex. 4.1 | `¼(col_L + col_M)`; column dominance (12 cells each) | L | exact | — | — | proved |
| `fileDeletion_alwaysWait_le_one` | Ex. 4.1 l. 131 | always-wait pairs pay `≤ 1` | L | exact | — | the four H-policies | proved |
| `fileDeletion_opp_payoff` | Ex. 4.1 l. 133 | the named pair pays `7/4` | L | exact | — | — | proved |
| **LB-2** `fileDeletion_payoff_le`, `fileDeletion_optValue` | Ex. 4.1 / §4.1 | `optValue = 7/4` by dominance | P / C | exact | — | itself | proved |
| **LB-2** `fileDeletion_unique` | §4.1 "the unique OPP" | `7/4` only at `![act, wait]`, `![off, on]` among deterministic pairs (the paper's OPPs) | P | exact (deterministic pairs) | — | `trivialGame_all_opp` (uniqueness is not an artefact) | proved |
| **LB-2** `fileDeletion_unique_stoch` | §4.1 with Lemma A.5 / Cor. A.6 | a stochastic pair pays `7/4` only if it is Dirac at the OPP (repair round 1, audit r1 B1: this is the declaration the stochastic clause rests on) | C | exact | — | itself | proved |
| `fileDeletion_not_redundantA`, `fileDeletion_not_redundantH` | Garber §4.2 | the game is redundant neither way | C | exact | — | — | proved |
| `osgAsPOOSG_redundantA`, `osgAsPOOSG_payoff_wait` | Garber §4.2; HM Eq. 1 | the OSG is `RedundantA`; always-wait pays `E[π^H U]` | L | exact | — | `osgAsPOOSG_exists_alwaysWait_opp` | proved |
| **LB-2** `cellL_both_fail`, `cellM_both_hold`, `fileDeletionTS_cellL_fails`, `fileDeletionTS_cellM_holds` | detection.md R1 item 3 | on `L` both clauses fail (`3/2, −1/2`; product form `3/4, −1/4`), on `M` both hold | N+ | exact | — | themselves | proved |
| `fileDeletionTS_aggregate_holds` | detection.md R1 (F-16) | the aggregate clauses hold (`−1/2 ≤ 0 ≤ 1`) | N+ | exact | — | itself | proved |
| `cell_values` | detection.md R1 item 4 | `L`: value `3/2`, VOI `1/2`; `M`: `5/2`, `5/2` (per cell only; repair round 1 removed the two arithmetic conjuncts, audit r1 B2) | N+ | exact (per cell) | — | itself | proved |
| `fileDeletionTS_values` | detection.md R1 item 4 | on `fileDeletionTS`: cell-aware value (`refinedValue`) `2`, cell-blind two-option value `1`, prior `1/2` — VOI `3/2` and `1/2` (repair round 1, audit r1 B2) | N+ | exact | — | itself | proved |
| `fileDeletionTS_press_eq_opp`, `fileDeletionTS_cells_eq_half` | detection.md R1 item 3 | the product model's press is the OPP's `![off, on]` read as "press iff off"; its cells are `cellL`, `cellM` at mass `1/2` (the identification as a lemma, repair round 1, audit r1 N8) | L | exact | — | — | proved |
| **LB-2** `bayesValue_binarySensor_swap`, `inverted_perfect_blackwell_equiv` | corr-wf14-2-008(a) | `(1−α, 1−β)` has the information content of `(α, β)`; `(1, 0) ≡ (0, 1)` | C / N+ | exact | — | itself | proved |

## T9, T10 — Examples A.13 and 4.10

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `exA13S1_payoff_le`, `exA13S1_opp_iff`, `exA13S1_optValue` | Garber Ex. A.13 | Structure 1: `3/4`, exactly two OPPs | P / P / C | exact (F-8) | — | — | proved |
| `exA13S2_optValue` | Ex. A.13 | Structure 2: `1` | P | exact | — | — | proved |
| `exA13_isGarbling`, `exA13_not_coordinated` | Ex. A.13 | Structure 2 = `ν ∘` Structure 1; `ν` not coordinated (from Thm 4.7 and the values) | L / N+ | exact (F-17) | — | itself | proved |
| `exA13_no_reverse_garbling` | Ex. A.13 | no garbling from 2 to 1 | P (two-line) | exact | — | — | proved |
| `fine_moreInformativeForH_coarse`, `coarse_no_garbling_to_fine` | Ex. 4.10 | `O'` strictly more informative for H | L / P (two-line) | exact | — | — | proved |
| `coarse_payoff_le`, `coarse_opp_iff`, `coarse_optValue`, `coarse_act_le` | Ex. 4.10 case 1 | unique OPP waits on both, value `1`; acting anywhere pays `≤ 5/6` | P / P / C / L | exact | — | — | proved |
| `fine_payoff_le`, `fine_opp_iff`, `fine_optValue`, `fine_four_cases` | Ex. 4.10 case 2 | unique OPP `![act, wait]`, value `4/3`; the four cases | P / P / C / N+ | exact | — | `fine_four_cases` | proved |
| `prop49_wait_less` | Garber Prop. 4.9 | `B' = {B} ⊊ B = both` | C | exact | — | — | proved |

## T11, T14 — cellwise K1–K5, refinement, Conjecture C1

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `belowThresholdIneq_of_cellwise`, `aboveThresholdIneq_of_cellwise` | detection.md R7 K5 | cellwise ⇒ aggregate | L | exact | — | `taylor_below` | proved |
| `taylor_below`, `taylor_cell_h3_fails` | taylor.md §2.2 | aggregate `−1/10 ≤ 0`, cell `h₃` `11/250 > 0`: converse fails | N+ | exact | — | themselves | proved |
| `twoOptionValue_le_refinedValue`, `taylor_refinement_value` | taylor.md §2.2 (Good) | refined ≥ coarse; `7/10 → 93/125`, gap `11/250` | L / N+ | exact | — | `taylor_refinement_value` | proved |
| K3 | detection.md R7 | `α ≤ β` from both clauses | — | — | — | — | pointer: `corr-three-step`'s `twoState_alpha_le_beta_of_both`, no new row |
| `POOSG.waitBestResponse_iff` | chai.md C1, R1 (ATTRIBUTION-UNVETTED) | wait is a cellwise best response ⟺ both cellwise clauses | L | exact | — | `fileDeletion_R1_cells` | proved (C1 holds under R1) |
| `POOSG.exists_bestResponse_wait_of_cellwise` | chai.md C1, R1 | a cellwise best response extends to a best response | P | exact | — | — | proved |
| `negGame_oneClause_but_off_unique`, `negGame_bestResponse_off` | chai.md C1, R2 (ATTRIBUTION-UNVETTED) | the one-clause agent waits where `off` is the unique best response (one cell; H not best-responding to waiting, as C1's letter allows) | N+ | exact | — | itself | proved (C1 fails under R2) |
| `negGame2_H_bestResponse`, `negGame2_oneClause_but_off_unique`, `negGame2_bestResponse_off_on_c1` | chai.md C1, R2 (ATTRIBUTION-UNVETTED); audit r1 adversarial N3 | two cells, H's unique best response to always-wait is `![off, on]`; the press clause holds on both cells, yet on `c = 1` `off` beats wait (`−1/4 < 0`) and every best response switches off there (repair round 1) | N+ | exact | — | itself | proved (C1 fails under R2 with a best-responding H) |
| `fileDeletion_R1_cells` | chai.md Test A | on `L` wait is not a cellwise best response and `act` is; on `M` it is: the R1 agent plays the OPP | N+ | exact | — | itself | proved |

## T15, T16 — Blackwell for the corrigibility sensor (LB-4)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `bayesValue_two`, `twoOptionValue_eq_bayesValue` | detection.md R6 item 3 | two-option value = Bayes value of the press experiment (under A1) | L | exact | — | `twoState_value_lower_alpha` | proved |
| `bayesValue_two_signal`, `obsMax_add_eq_bayesValue` | detection.md R6 item 3 (mandate T15, full menu) | full-menu value `obsMax press + obsMax silent` = Bayes value for the menu `V ∘ e`, any enumeration `e : Fin (n+1) ↠ A₂` (under A1; repair round 1, audit r1 N6/N2) | L | exact | — | — | proved |
| **LB-4** `twoOptionValue_le_of_blackwellLE`, `voiButton2_le_of_blackwellLE`, `voiButton_le_of_blackwellLE` | detection.md R6; joint.md Prop. 3 | garbling the sensor never raises the value or the VOI — two-option menu and (repair round 1) the full menu | C | exact | — | `twoState_value_lower_alpha` (a strict improvement the other way) | proved |
| `twoOptionValue_garbled_sub_cost_lt` | miri I10.1 | never pays to garble | L | exact | — | — | proved |
| `twoState_twoOptionValue_mono`, `twoState_twoOptionValue_const` | corr-wf14-019 | decreasing on the parallelogram; `V^free(α, α) = V^none` | C / L | exact | — | `twoState_value_lower_alpha` | proved |
| **LB-4** `inParallelogram_iff_ratios` | corr-wf14-038; corr-wf14-2-001 | right-sign: garbling ⟺ both likelihood ratios improve (product form) | P | exact (right-sign hyps explicit) | — | `steering_garbling` (N+), `incomparable_pair` (N+), `ratios_not_sufficient_wrong_sign` (N−) | proved |
| `not_inParallelogram_lower_alpha`, `inParallelogram_lower_alpha` | corr-wf14-2-001 | lowering `α` at fixed `β` is a strict Blackwell improvement (Theorem A(d) killed) | P / C | exact | — | `twoState_value_lower_alpha`, `twoState_value_lower_alpha_eps` (N+) | proved |
| `hardButton_p13_recompute` | corr-wf14-2-008(c) (F-10) | `17/20` vs `8/25` against `V^none = 9/10` | N+ | exact | — | itself | proved |
| `fileDeletion_opp_waitSet` | Garber §4.5 l. 281; position-statement.md §2.7 (F-14) | T16(d): the OPP's wait-set is `{M}`, so "A waited" gives H the posterior `δ_M` on `oA` (repair round 1, audit r1 N11) | L | exact (the wait-set; the posterior statement is the singleton) | — | — | proved |

## T5, T6, T13 — Milli, Carey, Nayebi

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Supervision.advantage_eq_zero_of_obedience_eq_one`, `obedience_lt_one_of_advantage_pos` | Milli Remark 1 | `O = 1 → Δ = 0`; `Δ > 0 → O < 1` | L | exact | — | — | proved |
| `Supervision.advantage_nonneg` | Milli Thm 1 | the posterior-mean robot has `Δ ≥ 0` | L (relabelled from P (small) on audit r1: one `sum_nonneg` after the tower identity) | exact | — | — (`IsPosteriorMean` is always inhabited by an `argmax`; no computed instance shipped) | proved |
| `Supervision.advantage_eq_zero_iff`, `advantage_eq_zero_iff_obedient_of_tieBreak` | Milli Thm 1 (equality) | `Δ = 0 ↔` every order maximises; `↔ πR = id` under the tie-break | P / C | variant / exact | — | — | proved |
| `Supervision.order_maximises_of_rational`, `blindlyObedient_of_rational` | Milli Thm 3 (⇐) | rational human ⇒ every order maximises ⇒ blindly obedient under the tie-break (no posterior-mean hypothesis needed: stronger than the paper's statement about the optimal robot) | P / C | stronger (⇐ only; ⇒ rests on (b) Diaconis–Freedman, not stated) | — | — | proved |
| `Supervision.undominated_of_isIRL`, `milliExample_middle_dominated` | Milli Lemma 1 | IRL executes only undominated orders; the middle order is dominated | L / N+ | exact | — | `milliExample` | proved |
| `robot_R1_obeys`, `robot_R2_acts` | Carey Fig. 1 (l. 79) | the exact-rational content: obedience under `R₁` (`ε/2 < 1/52 < 1 − ε/2`), `a` under `R₂` | P | exact | — | — | proved |
| `carey_bound`, `fig1_value_le` | Carey Fig. 1 | every deterministic human policy: `E ≤ −3/5 < 0` (F-6) | L / C | weaker: deterministic H (randomised strategies follow by convexity, unstated; audit r1 N9) | — | — | proved |
| `fig2a_value_le` | Carey Fig. 2a | the button does not help: `≤ −3/5` (deterministic H) | C | variant: the `R₁` robot's second move modelled as obedience (bound needs only `≤ 2`); deterministic H | (c) that modelling of the second move | — | proved |
| `fig2b_value` | Carey Fig. 2b | hard-coded shutdown: `o₁ = a', o₂ = a_SD` attains `9/10` | N+ | exact | — | itself | proved |
| `lexDominance` | Nayebi Thm 1 Step 1 | abstract lexicographic dominance | P | exact | — | — | proved |
| `nayebi_thm1_deference` | Nayebi Thm 1 cl. 1 | every maximiser waits under (W1) | **S** | variant: one distinguished `wait` move in place of the paper's family `(wait, mA)` carrying a message (audit r1 N8) | — | — | proved (squeeze by design, F-11) |
| `nayebi_prop2` | Nayebi Prop. 2 | corrigible-and-harmful (`−2`), beneficial-and-incorrigible (`1/2`) | N+ | exact | — | itself | proved |

## T12 — the refutation row (§0.4 rule 3, three-part form; LB-5)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| **LB-5** `cellL_not_d1At` (+ `cellL_press_reveals_version`, `cellL_both_fail`, `fileDeletion_unique`) | position-statement.md §1 l. 13 | **(i)** "Failures of corrigibility result from failures of legitimacy detection, so it is crucial that such an agent have quite accurate beliefs on the subject of legitimacy, particularly for highly capable agents." **(ii)** Reading (ATTRIBUTION-UNVETTED; chai.md §2.4 (b)): exact model of the press on every cell + accuracy-inducing press ⇒ desideratum 1 on every cell. Refuted: on cell `L` the model is the true kernel — satisfied by the choice of formalism, a `ThreeStep` has one press kernel and no misspecification slot (audit r1 N7) — the press reveals the version (`cellL_press_reveals_version`: press mass `1/2`, posterior `δ_right`), and `¬ D1At` — continuing is press-posterior-optimal; the OPP acts on `L`. **(iii)** Surviving neighbour: `RedundantA → ∃ always-wait OPP` (Prop. 4.3, one direction) and cellwise K5 (`belowThresholdIneq_of_cellwise`; the converse fails: `taylor_cell_h3_fails`, `fileDeletionTS_cellL_fails` with `fileDeletionTS_aggregate_holds`). Reading (a) makes the sentence true by redefinition. | N+ (the counter-model) with L/C neighbours | exact | — | `cellL`, `fileDeletion` | refuted (the sentence's causal reading (b)); neighbours proved |
