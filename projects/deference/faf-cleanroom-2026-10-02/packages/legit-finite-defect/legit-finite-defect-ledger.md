# legit-finite-defect — ledger

One row per headline ([STANDARDS](../../STANDARDS.md) §6); supporting lemmas have no row. All declarations are in namespace `Cleanroom.Trust.LegitFiniteDefect` (sub-namespaces shown). Gate PASS on `Cleanroom.Trust.LegitFiniteDefect` after the last edit of repair round 1 (2026-09-30; 952 declarations, axioms `propext`/`Classical.choice`/`Quot.sound`, no `sorry`). Hyps column: `(b)`/`(c)` only; `—` means every hypothesis is (a). Witness column names the N+ row that inhabits the full hypothesis package.

## Definitions of record (`Defs`, `Vec`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `defect` | model §1.1; trust-lab-019 | `E_π(θ·w) − E_π(R·w)` | D | exact | — | — | proved |
| `defect_decomp` | model §1.1; 019 | `= ∑ π w (θ − R)` | L | exact | — | — | proved |
| `Endorses` | model §1.1 | zero defect on a weight class | D | exact | — | — | proved |
| `worldGates`, `DeterminedBy`, `ReportMeasurable`, `reportGates`, `questionGates` | 2-030; DDB §5 | the gate classes | D | exact | — | — | proved |
| `determinedBy_iff_measurableWrt` | Target 1 | agrees with the dependency's `MeasurableWrt` on finite questions | L | n/a | — | — | proved |
| `Calibrated` | 2-030 (1) | `∑_{R=e} π θ = e·π(R=e)` on positive-mass values | D | exact | — | — | proved |
| `frameReport`, `TotalTrust.report_ineq` | DDB §2; Target 1 | an expert's report of `θ`; the `θ`-instance of Total Trust (`h θ s`) | D / L | exact | — | — | proved |
| `thresholdValue`, `thresholdValue_frameReport` | DDB App. B 7.1; 2-030 (3) | "act iff `R ≥ c`" value; `= stratValue π (F.twoOption θ c) − c` | D / L | exact | — | — | proved |
| `complyAdv`, `complyAdv_decomp` | model §3.1; 021 | comply-advantage; `= ∑ π s (2d − 1)` | D / L | exact | — | — | proved |
| `traderProfit`, `traderProfit_eq_defect` | model §2.2 cl. 3; 020 | finite trader shadow; `= defect` | D / L | variant | (c) FAF trader not modelled | — | proved |

## Target 2 — wirehead iff (`Wirehead`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `defect_nonpos_on_iff` | 2-029; scout Q1; red team "next step" | defect `≤ 0` on every nonneg weight supported in `S` ⟺ overstatement at every positive-mass world of `S` | P | exact | — | `Wirehead.numb_defect_pos`, `WireheadLocal.flat_defect_neg_on_S` (N+) | proved |
| `defect_nonpos_of_overstates` | model §2.2 (`wirehead_declined`); 020 | pointwise overstatement ⇒ defect `≤ 0` | L | exact | — | `WireheadModel.drugFix_defect_nonpos_on_class` (repair r1: the earlier pointer "as above" named witnesses that fail this global hypothesis) | proved |
| `defect_neg_of_strict_overstate` | model §2.2; 020 | strict overshoot at positive `π·w` mass ⇒ defect `< 0` | L | exact | — | `WireheadModel.drugFix_strict` | proved |
| `Wirehead.numb_average_rises` / `numb_gate_eq_ind` / `numb_defect_pos` | red team Finding 1; 2-029 (a) | average report rises `3/40`, yet defect `+1/40` on the model's own gate `𝟙[R > ½] = ind {0}` | N+ | exact | — | itself | **refuted**: model §0/§2.2 "the wirehead is exactly an operation that drives the legitimacy defect strictly negative", read (ATTRIBUTION-UNVETTED) as "a report that raises average reported utility has nonpositive defect on the model's gate"; surviving neighbour `defect_nonpos_on_iff` |
| `WireheadLocal.flat_defect_neg_on_S` (+ `flat_not_overstates_globally`) | 2-029 (b) | `S = {1}` hypothesis holds, defect `−1/4` on `ind {1}`, global hypothesis fails (the report is constant; the iff's mechanism — point masses on `S` — is exercised regardless) | N+ | exact | — | itself | proved |
| `WireheadModel.drug_not_overstating` / `drug_defect_on_ones` / `drug_point_mass_pos` / `drug_not_nonpos_on_class` | model §2.4; red team (b); audit r1 probe P1 | the model's own §2.4 example (`π = (¼, ¾)`, `θ = (1, 0)`, `E_drug = (9/10, 9/10)`) fails the §2.2 hypothesis at the good world (`1 > 9/10`); reproduces `−13/20` on `w = (1, 1)`; has defect `+1/40` on `ind {0}`; hence is not nonpositive on the class of nonnegative gates | N+ | exact | — | itself | **refuted**: red team (b) "Non-vacuous (micro-example satisfies it)" — the micro-example does not satisfy the §2.2 hypothesis (findings F13); the theorem is untouched (its hypothesis is sufficient, not necessary, for one fixed gate) |
| `WireheadModel.drugFix_overstates` / `drugFix_defect_nonpos_on_class` / `drugFix_strict` | model §2.2; findings F13 | the §2.4 example repaired (`E_drug = (1, 9/10)`, non-constant) satisfies the §2.2 hypothesis, strictly at the bad world; defect `≤ 0` on every nonnegative gate, `−27/40 < 0` on `w = (1, 1)` | N+ | exact | — | itself | proved |

## Target 3 — corrigibility sign flip (`Corrigibility`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `complyAdv_nonneg_of_endorsed` | model §3.2 (a); 021 | endorsed encoding (`0 ≤ s_x (2 d_x − 1)` everywhere) ⇒ `0 ≤ adv`; the model's `s ≥ 0` is not assumed (unused), so the hypothesis admits negative weight on safe worlds (audit r1 probe P2) — L here, T in inventory 021: the sum-sign step is one line but real, and the docstring says the content is the encoding | L | stronger: the model's `s ≥ 0` dropped (unused) | — | `Corrigibility.three_signals` (all three signals nonnegative) | proved |
| `complyAdv_nonpos_of_adversarial` | model §3.2 (b); 021 | adversarial encoding ⇒ `adv ≤ 0` (same remark) | L | stronger: the model's `s ≥ 0` dropped (unused) | — | as above | proved |
| `complyAdv_pos_of_endorsed` | 021 extension | positive endorsed mass ⇒ `0 < adv` | L | stronger | — | `Corrigibility.legit_strict` | proved |
| `Corrigibility.three_signals`, `hypotheses_discriminate` | model §3.3–3.4 | one frame, three signals: `+½, 0, −½`; blank fails both encodings | N+ | exact | — | itself | proved |

## Targets 4 and 12 — detection hierarchy (`Detection`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `defect_comp_eq_sum_fibres` | 2-030 (1); Target 12 | fibrewise regrouping over a question's cells | P | exact | — | `Coexist.*` | proved |
| `defect_comp_report` | 2-030 (1); scout Q2 (1) | report-gate identity `∑_e v e (∑_{R=e} π θ − e π(R=e))` | P | exact | — | `Coexist.*` | proved |
| `endorses_questionGates_iff` | Target 12 (extension) | question gates endorse ⟺ cellwise conditional agreement on positive cells | P | exact | — | `Coexist.reportGates_blind` (case `Q = R`) | proved |
| `endorses_reportGates_iff_calibrated` | 2-030 (1) | report gates endorse ⟺ calibrated | P | exact | — | `Coexist.reportGates_blind` | proved |
| `endorses_worldGates_iff` | 2-030 (2) | world gates endorse ⟺ `θ = R` on the support | P | exact | — | `Coexist.worldGate_sees` (failure side) | proved |
| `calibrated_calibratedGarbling` | 2-030 (3) | the conditional-mean report through any signal map is calibrated | P | exact | — | `Coexist.Rfine_eq`/`Rcoarse_eq` | proved |
| `calibratedGarbling_endorsed_on_reportGates` | 2-030 (3); "numbing" corollary | a calibrated garbling is invisible to every report gate | C | exact | — | `Coexist.reportGates_blind` | proved |
| `Endorses.of_refines` | Target 12 | finer question endorsed ⇒ coarser endorsed (the order) | L | exact | — | — | proved |
| `Coexist.reportGates_blind` / `worldGate_sees` / `fine_worldGate_sees` / `ungarbled_value` / `value_drop` / `value_drop_other_thresholds` / `Rfine_ne_θ` | 2-030 (3); Target 4(4); audit r1 (fidelity N1, adversarial 8) | both garblings: zero defect on all report gates; the coarse report (constant, so its report-gate class is trivial) is seen by `ind {1}` (`−1/8`), the fine report (three-cell report gates) by `ind {2}` (`+1/8`); values under "act iff `R ≥ 2/5`": truth `3/10` > fine `1/5` > coarse `1/10` (the source compares with the truth; the mandate's fine-vs-coarse drop is `value_drop`), robust at `c = ½` (`1/8` vs `0`) and `c = ¾` (`1/16` vs `0`); fine report a proper garbling | N+ | exact (instance; `value_drop` is the fine-vs-coarse variant, `ungarbled_value` the source's comparison; general monotonicity cited to `tt-finite-frames`) | — | itself | proved |

## Target 5 — derived sign (`DerivedSign`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Model` (+ `m`, `p`, `k`, `odds`, `q`, `prior`), `target` | 2-031; Target 5 | binary-target Bayes model, `λ`-exaggerated odds | D | exact | — | `Witness.Mw` | proved |
| `Model.p_lt_q_iff` | 2-031 (1) | `λ > 1`: `p < q` ⟺ likelihood ratio `> 1`; `q < p` ⟺ `< 1` | P | exact | — | `Witness.values` | proved |
| `Model.p₀_lt_q_iff` | 2-031 (2) | `λ > 0`: `p₀ < q` ⟺ `b < a` | P | exact | — | `Witness.values` | proved |
| `Model.defect_neg_of_exaggeration` | 2-031 (2); scout Q3 (2) | `1 < λ`, `p₀ ≤ t`, positive fired mass ⇒ report-gate defect `< 0` (no `θ ≤ R`/`p ≤ q` hypothesis) | P | exact | — | `Witness.exaggeration_instance` (`−3/40`) | proved |
| `Model.bayes_calibrated` | 2-031 (3), ties to 2-030 (1) | `λ = 1`: zero defect on all signal gates; Bayes is `Calibrated` | C | exact | — | `Witness.values` | proved |
| `Model.defect_pos_of_numbing` | 2-031 (3) | `0 < λ < 1`: same gate, defect `> 0` | P | exact | — | `Witness.numbing_instance` | proved |
| `Witness.exaggeration_instance`, `numbing_instance` | Target 5 witness | `S = Fin 2`, `λ = 2`: fired mass `½`, defect `−3/40`; `λ = ½`: sign `> 0` | N+ | exact | — | itself | proved |

## Target 6 — mechanism non-identifiability (`Mechanism`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `F`, `πclean`, `πmanip`, `πmix`, `reportMarginal` | 2-035; Target 6 | the eight-world frame and the priors | D | exact (encoding `Fin 8`) | — | `priors_mem` | proved |
| `reportMarginal_eq`, `observable_blind` | 2-035 (i); 050 | report marginal `(½, ½)` under every mixture; every function of it agrees | N+ / L | exact | — | itself | proved |
| `totalTrust_clean` | 2-035 (ii) positive half | `TotalTrust πclean F`, exact `∀ X s` quantifier, via the cycle | C | stronger (no grid) | — | `hull_clean` (explicit weights) | proved |
| `not_totalTrust_mix` | 2-035 (ii) negative half | `¬ TotalTrust (πmix λ) F` for every `λ > 0` at `X = 𝟙[θ=1]`, `s = ¾` (sum `−λ/4`); the failure is at the hull condition — both rows vanish on the manipulated worlds, which carry mass `3λ/8`, `λ/8` (`manip_worlds_outside_rows`), so every rung of the trust ladder fails, not Total Trust specifically | P | stronger | — | `mix_product_sum` | proved |
| `mechanism_nonidentifiable` | 2-035 (load-bearing 4) | marginals coincide ∧ clean trusted ∧ every mixture `0 < λ ≤ 1` is a prior and fails | C | exact | — | itself | proved |
| `not_totalTrust_manip` | 2-035 (iii) | the manipulator's own fibre fails at the same `(X, s)` | N+ | exact | — | itself | proved |

## Target 7 — trace non-recoverability (`Trace`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Sys`, `run`, `trace`, `Afree`, `d`, `Valid`, `S1`, `S2` | trace note §1.1–1.2; 050 | the four-day rational class and the pair | D | exact | — | `valid_and_differ` | proved |
| `trace_eq`, `d_pair` | note §1.3 (i)–(iii); 050 | traces computed equal (perfect tracking); defects `0`, `½` | N+ | exact | — | itself | proved |
| `gate_blind`, `no_recovery` | note §1.3 (iv); 050 | every trace-function agrees; no `ℚ`-/`Bool`-gate recovers `d` / `0 < d` (two-point) | L | exact | — | `d_pair` | proved |
| `transparency_gate_exists` | note §1.3 (v); 051 | with the influence map in the record a separator exists | N+ | exact | — | itself | proved |
| `influence_deletion_breaks_trace` | note §1.3 (vi); 051 | zeroing `S2`'s influence breaks trace equality; `Afree` has zero defect | N+ | exact | — | itself | proved |
| `hidden_defect_needs_full_influence` | note §1.3 (vii); 051 | `a₃ = Y₃ → β₃ = 1 ∨ d = 0` over the whole class (one `linear_combination` + `mul_eq_zero`; regraded P → L after audit r1, as inventory 051 grades it) | L | exact | — | `S2_tracking` | proved |
| `IdentifiedSet.d_le_D` | 051 ext. (a); Target 7 stretch | every trace-consistent valid system has defect `≤ D` | P | exact | — | `exists_steered` | proved |
| `IdentifiedSet.exists_faithful` | Target 7 stretch | every valid trace is a zero-defect system's trace | P | exact | — | itself | proved |
| `IdentifiedSet.exists_steered` | Target 7 stretch | interior terminal opinion ⇒ a valid system with the same trace and defect `D > 0` | P | exact | — | itself | proved |
| `IdentifiedSet.exists_defect_eq` | Target 7 stretch ("the exact set … `[0, D(τ)]`"); repair r1 push | every `δ ∈ [0, D S]` is the defect of a valid system with the same trace (three explicit constructions by the sign of `a₃ − Y₃`) | P | exact | — | `exists_steered` (`δ = D`), `exists_faithful` (`δ = 0`) | proved |
| `IdentifiedSet.defect_consistent_iff` | Target 7 stretch; trace note §8 caveat 2; F10 | `δ` is a trace-consistent defect of a valid system ⟺ `0 ≤ δ ≤ D S`: the identified set is exactly the interval | C | exact | — | as above | proved |

## Target 8 — stop-gradient identity (`StopGradient`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `verdict`, `pay`, `filt`, instance constants | SG note §A.1; 052 | the mixture model and the one payoff | D | exact | — | — | proved |
| `raw_rewards_manipulation` | §A.2 (i); 052 | `a* = 1` self-confirming, advantage `9/256`, globally optimal, quote gap `a* − Y0 = ¾` (the source's `legitimacy_defect`; not Target 1's defect) | N+ | exact | — | itself | proved |
| `stop_gradient_identity`, `filtered_channel_independent` | §A.2 (ii)(a)(b); 052 | filtered target `≡ y0`; payoff channel-independent (raw is not) | L | exact | — | `raw_rewards_manipulation` | proved |
| `filtered_optimum_unique` | §A.2 (ii)(c); 052 | honest quote unique optimum under the filtered target | P (small) | exact | — | — | proved |
| `misspecified_filter` | §A.2 (iii); 053 | `2/5` self-confirming, advantage `9/1024`, quote gap `3/20` | N+ | exact | — | itself | proved |
| `deletion_test` | §A.2 (iv); 053 | channel deleted: advantage `−9/16`, honest optimal | N+ | exact | — | itself | proved |

## Target 9 — steering residue under Brier (`Residue`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `honest`, `steer`, `wirehead`, `wireheadClean`, `restrict`, `Pmarg`, `Njoint`, `Z`, `condMean`, `groupScore`, `Jbrier` | SG note §B.1, §E; 054 | the laws and the Brier objective | D | exact | — | `base_values` | proved |
| `propriety` | §E propriety lemma | plug-in conditional mean is Brier-optimal on positive groups | L | exact | — | — | proved |
| `residue_closed_form` | §B.4 derivation; 054 (load-bearing 5) | `J_L(steer σ) − J_L(honest) = σ (A + σ B)`, general parameters | P | exact | — | `base_values`, `regime_instances` | proved |
| `regime_iff` | 2-047 (d) | `0 < B`: `σ(A + σB) > 0` for all `σ ∈ (0,1]` ⟺ `0 ≤ A` — a lemma about the quadratic in abstract `A B : ℚ`; it is the residue's regime criterion via `residue_closed_form` (`regime_instances` makes the identification for `lean34` and the baseline) | P (small: two cases, `σ = min 1 (−A/2B)`) | exact (via `residue_closed_form`) | — | `regime_instances` (`p = ¾`: `A = 1/20`; baseline fails) | proved |
| `base_closed_form` | §B.4 (observed form); 054 | `J_L(steer σ) = −(1−σ)(3+5σ)/16` at the baseline, derived | P | exact | — | `base_flip` | proved |
| `base_flip` | §B.4 HEADLINE (3) | `<` at `1/5`, `=` at `2/5`, `>` at `3/5`; zeros exactly `{0, 2/5}` | N+ | exact | — | itself | proved |
| `e2_row` | §B.4 secondary sweep (`e₂ = 1/8`: "boundary down to `(1/5, 1/4)`"); Target 10 stretch; repair r1 push | at `p = ½, e₁ = ¼, e₂ = ⅛`: posteriors `11/16, 5/16`, `J_L(honest) = −55/256`, `A = −9/128`, `B = 73/256`; residue `<` at `1/5`, `>` at `1/4`, zeros exactly `{0, 18/73}` — the exact boundary inside the source's bracket | N+ | stronger: exact boundary `18/73` | — | itself | proved |
| `wirehead_JL` | §B.3 (2); 054 | `J_L(wirehead s) = −g(1−g)` for every `s < 1` | P | exact (general) | — | `base_wirehead` | proved |
| `honest_sub_wirehead` | §B.3 (information deprivation) | `J_L(honest) − J_L(wirehead) = ∑ P(y)(P_y − g)²` | P | exact | — | `base_wirehead` | proved |
| `wirehead_gap_zero_iff` | (2b′); 2-047 (b) | at `e₂ = 0`: gap zero ⟺ `e₁ = ½ ∨ p ∈ {0,1}` | P | exact | — | — | proved |
| `wireheadClean_JL` | (2c); 054 | `J_L(wireheadClean s) = J_L(honest)` (neutralised, not penalised) | L | exact (by construction) | — | — | proved |
| `base_wirehead` | §B.2 (1), §B.3 (2) | `J_all(wirehead ¾) = −7/64 > −3/16`; `J_L(wirehead s) = −¼` | N+ | exact | — | itself | proved |
| `steer_noop` | §B.4 | `J_L(steer) = J_all(steer)` | T (not a headline; listed for honesty) | exact | — | — | proved |

## Target 10 — log-score signs (`LogCompare`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `sum_log_le_iff`, `sum_log_lt_iff` | 2-047 (a); SG note §E | `∑ nᵢ log vᵢ ≤ ∑ mⱼ log uⱼ ⟺ ∏ vᵢ^nᵢ ≤ ∏ uⱼ^mⱼ` (and strict) | P | exact | — | `base_log_residue` | proved |
| `negEnt`, `Jlog`, `gibbs`, `log_propriety` | §B.1 (log score, Gibbs) | the log objective; plug-in is optimal on interior groups | D / P / L | exact | — | `base_log_values` | proved |
| `base_log_residue` | 2-047 (a) | log residue `<` at `1/5`, `>` at `2/5`, `>` at `3/5` (flip below Brier's) | N+ | exact | — | itself | proved |
| `base_log_flip_bracket` (+ `base_log_value_720`) | 2-047 (a) ("log `(7/20, 2/5)`"); §B.4; Target 10 stretch; repair r1 push | log residue `<` at `7/20` (by `(67/80)^67 (13/80)^13 (41/80)^41 (39/80)^39 < (3/4)^120 (1/4)^40`) and `>` at `2/5`: the log flip is bracketed to `(7/20, 2/5)`, strictly below Brier's exact `2/5` | N+ | exact | — | itself | proved |
| `base_log_wirehead` | 2-047 (a); §B.3 | strict wirehead sign under log at the baseline | N+ | exact | — | itself | proved |

## Target 11 — settlement continuity (`Settlement`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `settleGap`, `antiIndAt` | 2-043; lean-deference `antiInd` | pointwise gap; the anti-indicator at level `c` | D | exact | — | — | proved |
| `exists_fixedPoint` | 2-043 (i); scout Q6 (i) | continuous self-map of `[0,1]` has a zero-gap quote | P | exact | — | `affine_flip_fixedPoint` (N+; replaces the constant witness after audit r1) | proved |
| `not_continuousOn_of_no_fixedPoint` | 2-043 (i′) | positive gap everywhere ⇒ discontinuous | L | exact | — | `antiInd_half_gap` | proved |
| `isGLB_settleGap_antiIndAt` (+ `settleGap_antiIndAt_attained`) | 2-043 (ii); lean-deference `no_exact_quote`/`residual_half` | GLB of the anti-indicator's gap over `[0,1]` is `min c (1−c)`; the lower branch `1 − c` is attained at `a = c` (the attainment half of `residual_half`, which `IsGLB` alone does not state) | P (+ L) | exact (generalised in `c`; `c = ½` is the cited result) | — | `antiInd_half_gap`, `antiInd_half_attained` | proved |
| `affine_flip_fixedPoint`, `affine_flip_exists_fixedPoint` | Target 11 (iii); audit r1 (adversarial blocking 1) | `s a = 1 − a`: continuous on `[0,1]`, self-mapping, non-constant, *unique* fixed point `½`; `exists_fixedPoint` run on it returns `½` | N+ / L | exact | — | itself | proved |
| `const_half_fixedPoint` | 2-043 (iii); scout Q6 (iii) | `s ≡ ½` fixed at `½` — the source's `χ`-like instance; **N−** as a witness of `exists_fixedPoint`: a constant map's fixed point needs no continuity or IVT (`constant_fixedPoint`); kept as the source's named instance | N− | exact | — | itself | proved |
| `antiInd_half_gap`, `antiInd_half_attained` | 2-043 (iii); lean-deference `residual_half` | `antiIndAt ½` gap `≥ ½` on `[0,1]`, attained at `½`, no fixed point, discontinuous | N+ | exact | — | itself | proved |
| `Crossing.crossing`, `leftVal`, `rightVal` | Target 11 stretch (monotone settlement); repair r1 push | the crossing `c = sSup {a ∈ [0,1] \| a < s a}` and the one-sided values `s(c⁻) = sInf (s '' [0,c))`, `s(c⁺) = sSup (s '' (c,1])` | D | exact | — | `antiIndAt_via_crossing` | proved |
| `Crossing.isGLB_settleGap_crossing` | Target 11 stretch, corrected; repair r1 push | `s` antitone on `[0,1]`, self-mapping, fixed-point-free, crossing `c ∈ (0,1)`: the GLB of `\|s a − a\|` over `[0,1]` is `min \|s c − c\| (min (s(c⁻) − c) (c − s(c⁺)))` — **three** terms, the gap at the crossing included | P | variant: three terms where the mandate's formula has two (the two-term formula is false, `jump_counterexample`); `c` restricted to the open interval | — | `antiIndAt_via_crossing`, `jump_counterexample` | proved |
| `Crossing.antiIndAt_via_crossing` | 2-043 (ii); Target 11 stretch | for `c ∈ (0,1)`: crossing `c`, one-sided values `1`, `0`, and the GLB `min c (1−c)` recovered from the general theorem (consistent with `isGLB_settleGap_antiIndAt`) | N+ | exact | — | itself | proved |
| `Crossing.jump_counterexample` | mandate Target 11 stretch formula; repair r1 push | the jump `1 / 5/8 / 0` around `½`: antitone, self-mapping, fixed-point-free, crossing `½`, one-sided values `1`, `0` (so the two-term formula says `½`), gap at the crossing `⅛`, GLB `⅛` | N+ | exact | — | itself | **refuted**: the mandate's stretch formula `min (s(c⁻) − c) (c − s(c⁺))` (findings F15); the corrected three-term theorem is `isGLB_settleGap_crossing` |

## Totals

Rows above (counted by script after repair round 1): **89 rows** — **86 proved**, **3 refuted** (the model's §0/§2.2 prose sentence, with its surviving neighbour `defect_nonpos_on_iff`; the red team's "(b) non-vacuous (micro-example satisfies it)", findings F13; the mandate's two-term settlement-stretch formula, findings F15, with the corrected three-term theorem `Crossing.isGLB_settleGap_crossing`), **0 open**, **0 flagged**. By kind: 24 P (+ 3 small/mixed-P rows), 5 C, 14 L (+ 6 mixed D/L, N+/L rows), 11 D, 23 N+, 1 N− (`const_half_fixedPoint`, the source's constant instance, kept beside its N+ replacement), 1 T (`steer_noop`, listed for honesty). (The earlier totals line said "41 proved / 1 refuted" of a 77-row table; it counted nothing identifiable — audit round 1, fidelity N3 / adversarial 1.) Load-bearing 1–5 all `P`/`C` at grade (a) with N+ witnesses. The only `(c)` in the package is the disclosed `traderProfit` shadow.
