# corr-reflect-frames — ledger

Package `corr-reflect-frames` (faf-cleanroom run, 2026-09-30). One row per headline ([STANDARDS](../../STANDARDS.md) §6); supporting lemmas have no row. Namespace `Cleanroom.Corrigibility.CorrReflectFrames` (witnesses `.Witnesses`, MM `.Slips`); files under `Cleanroom/Corrigibility/CorrReflectFrames/`. Kinds: P proved · C composition · L plumbing · D definition of record · N+/N− witness · OPEN. Every hypothesis in the package is (a): derived here or in the dependencies, or none; no (b) or (c) anywhere (the one (b) the mandate allowed, T12's accuracy leg, was omitted rather than assumed). "INT" = `CandsIntrospective` (introspection at candidates), always in the statement where used. Status `proved` means built and gate PASS (see the report's "Gate" section).

## Definitions of record (T0; kind D, fidelity exact unless noted)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `valCell`, `estCell` (`Defs`) | radical S3, Def I5.1 | the cells `{P_{t₂}(φ) = c}`, `{E_{P_{t₂}} X = s}` | D | exact | — | — | proved |
| `ValueReflects`, `VarReflects`, `EstimateMatching` | radical S3 (R-val), I4.1 (R-var), S3 (Mart) | the three forms, product form, all `c`/`s`, vacuous at null cells | D | exact (ratio forms are the `*_iff_ratio` lemmas) | — | `frame4` (all hold), `fig3`/twist (separate) | proved |
| `CandsIntrospective` | radical S1 INT, armstrong S16 | every candidate row gives its own cell probability one | D | exact (restricted to candidates) | — | `frame4` | proved |
| `restrict` + homogeneity (`*_smul_iff`, `restrict_normalize_mem`) | mandate (Representation) | unnormalized conditioning; every predicate homogeneous of degree one | D/L | exact | — | — | proved |
| `LegitimizingVal` | radical Def I5.1 / Lemma I5.2 | `L` legitimizing for `φ`: hits inside `L` in ratio `c : 1−c` in every cell | D | exact (I5.2's form; I5.1 is `legitimizingVal_iff_ratio`) | — | Model A/B | proved |
| `LegitimizingTT` | ddb L-C | Total Trust conditional on `L` | D | exact | — | `ddb4` | proved |
| `condRow`, `refineFrame`, `selectFrame`, `RetainsGrounds` | armstrong S16, selection R1.1/R2.1 | Bayesian refinement rows (`δ_w` on null fibres, disclosed); selected frame; per-`k` retention | D | exact / variant (per-`k`) | — | `frame4`, `τ₁₃`, `sForget` | proved |
| `Introspective` (`Bridge`) | radical S1 INT | positive atoms' kernels give themselves probability one | D | exact | — | via bridge | proved |
| `pmfOfSimplex`, `toAnticipation` (`Bridge`) | radical Def I3.2, mm Prop I3.1 | a frame as an anticipation structure with atoms the rows | D | exact | — | — | proved |
| `metaJoint` (`MetaBelief`) | armstrong I3.2 | the joint `(ω, i) ↦ w i · q i ω` | D | exact | — | — | proved |
| `twist` (`Twist`) | armstrong I2.2 | rows `(1−l)·π(·|cell) + l·π` | D | exact | — | — | proved |
| `brier`, `logLoss`, `expLoss`, `constLoss` (`Accuracy`) | radical S3 (Acc_φ) | local scoring | D | exact | — | `s6` | proved |
| `ValueReflectsOn` (`Legit`) | radical I5.3(d) | value-form reflection for one event | D | exact | — | — | proved |
| `cellBound` (`Legit`) | radical I5.5(a) | the finite per-cell bound with explicit endpoints | D | exact | — | Model A/B | proved |
| `LegitimizingEvent`, `DelegitimizingEvent`, strict (`Viability`) | miri I6.1/I6.3 | Blackwell order on the two conditional experiments | D | exact | — | `coinArm_strictlyDelegitimizing`, `evidence_strictlyLegitimizing` (`WitnessesD`, r1) | proved |
| `SelfRefSpace`, `SelfRefSpace.IsUniversal` (`SelfRef`, r1) | radical I7.1 | a nonempty compact metrizable Borel `Ω` with canonical `state`/`cred` forming `Ω ≃ₜ W × Δ(Ω)`; the terminal-coalgebra property | D | variant (`T = Unit`, topological reading; universality over continuous test coalgebras) | — | none (bare existence is not the claim, F16) | proved (defs) |
| `Ustar`, `mixU` (`Expanded`, r1) | bli-soto-b-055, corr-core-003 | expanded and mixed utility | D | exact | — | — | proved |
| `pushJoint`, `ReflectiveFor` (`Clarity`) | radical I3.2, I7.2 | prior × push; reflective for given targets | D | exact | — | — | proved |
| `voi` (`Good`) | joint-final P.5′ | value of learning `θ` | D | exact | — | — | proved |
| `lossOf`, `gainAll`, `gainPrinted`, tables (`Slips`) | herrmann-2025 App. A/B, §4.3 | MM's scores under the two conventions | D | exact (transcription) | — | — | proved |

## T1 — the collapse (load-bearing)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `varReflects_of_reflects`, `valueReflects_of_varReflects`, `estimateMatching_of_varReflects`, `totalTrust_of_varReflects` | radical I4.1 (i), (iv) | the four INT-free arrows | P | exact | — | — | proved |
| `reflects_of_valueReflects` | radical I4.1 (ii), armstrong A(a) | value form ⟹ function form under INT (singleton events suffice) | P | exact | — | `frame4` | proved |
| `varReflects_of_estimateMatching` | radical I4.1 (iii) | Mart ⟹ variable form under INT | P | exact | — | `frame4` | proved |
| `varReflects_of_totalTrust` | radical I4.1 (v) | Total Trust ⟹ variable form under INT, no limit | P | exact (`≥`-thresholds) | — | `frame4` | proved |
| `candsIntrospective_of_reflects` | armstrong A(c) | Reflection forces INT at candidates | P | exact | — | — | proved |
| `collapse` | radical I4.1, armstrong A, mm Cor I4.1 | the six forms are equivalent under INT | C | exact | — | N+ `frame4_witness`, N− `flat` (`flat_candsIntrospective`, in Lean since r1) | proved |
| `reflects_iff_estimateMatching_and_int` (+ `_valueReflects_`, `_totalTrust_`) | armstrong A | Reflection ⟺ Φ ∧ INT | C | exact | — | `frame4`; twist/`fig3` show INT needed | proved |
| `frame4_witness` (`WitnessesA`) | mandate T1 | immodest two-branch refinement, two candidates, not flat, all six forms | N+ | exact | — | itself | proved |

## T2 — twists and fn 18

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `estimateMatching_iff_stationary` | ddb l. 149 | Mart = `π = πP` | L | exact | — | — | proved |
| `twist_estimateMatching` | armstrong I2.2 | every twist is estimate-matching | P | exact (whole family) | — | family; instance `twist4_instance` (`WitnessesD`, r1) | proved |
| `twist_not_candsIntrospective`, `twist_not_reflects` | armstrong I2.2, A2 | non-trivial twists fail INT and Reflection | P | exact (whole family) | — | family; instance `twist4_instance` (r1) | proved |
| `fig3_value_not_estimateMatching`, `fig2_estimateMatching_not_value` | ddb fn 18 | SU independent of Value | N+ | exact | — | themselves | proved |

## T3 — the meta-belief representation (load-bearing)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `calibrated_iff_reflective_and_introspective` (`Bridge`) | radical I3.3(b) survivor, armstrong A | SC-internal calibration ⟺ reflective ∧ introspective, any `Ω` | P | exact | — | `as38` (SC) refutes the INT-free ⇐; frames via bridge | proved |
| `reflects_iff_calibrated`, `estimateMatching_iff_reflective`, `candsIntrospective_iff_introspective` | mm Prop I3.1, radical I3.3(b) | the frame bridge | L | exact | — | — | proved |
| `reflects_iff_estimateMatching_and_int_transported` | armstrong A | T1's Theorem A re-derived through the bridge | C | exact | — | — | proved |
| `exists_metaJoint_iff` (`MetaBelief`) | armstrong I3.2, radical I3.3(b) existence reading | a joint with the announced conditionals exists ⟺ `∑ wᵢ qᵢ = P` | P | exact | — | `metaJoint` | proved |
| `eq_metaJoint` | armstrong I3.2 | the joint is forced | P | exact | — | — | proved |
| `i33b_fixed_joint_refuted` | radical I3.3(b) l. 108 as printed | (i) quoted in findings F1; (ii) fixed joint, `Reflective → Calibrated`; (iii) survivors above | N+ / refuted | n/a | — | `as38` — `udt-supercondition`'s witness, imported, not this package's | refuted |
| `dz_finite` | radical I3.1, mm D–Z | finite D–Z (re-export) | L | exact | — | — | proved |
| `sum_mass_snd_inter_eq` | radical I3.3(a) | total probability over the meta-belief events | L | exact | — | — | proved |

## T4 — zero → positive

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `reflects_null_of_null`, `valueReflects_null_of_null` | radical I2.2 | candidates give `π`-null events probability zero (value form: no INT) | P | exact | — | — | proved |
| `totalTrust_null_of_null` | mm Prop I2.1 | worlds where the expert gives a `π`-null event positive mass are null | P | exact (single threshold) | — | — | proved |
| `totalTrust_mass_supp` | ddb L-A | positive worlds' experts give `π`'s support mass one | P | exact | — | — | proved |

## T5 — accuracy

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `brier_expLoss_le_constLoss` | radical I4.2(a), armstrong I4.2(i) | value form for `φ` ⟹ Brier non-decrease (conditional-variance identity) | P | weaker: Brier only (the note claims every strictly proper score) | — | positive `frame4_brier_strict` (`0 < 1/4`, r1); `s6` shows the converse fails | proved |
| `s6_separation` (`WitnessesA`) | radical I4.2(b)(c) | immodest, Brier and log better, value form and Total Trust fail | N+ | weaker: two scores (log via `5¹⁰ < 2¹¹·3⁹`; the source's (Acc_φ) is every proper score) | — | itself | proved |
| `valueReflectsOn_iff_ratio` | radical I4.2(c) | recalibration identity | L | exact | — | — | proved |
| all-proper-scores extension | radical I4.2(b) | — | — | — | — | — | not done |

## T6 — legitimizing events (load-bearing)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `legitimizingVal_iff_ratio` | radical Def I5.1 / I5.2 | ratio ⟺ linear form | L | exact | — | — | proved |
| `legitimizingVal_union_of_disjoint`, `legitimizingVal_sdiff` | radical I5.3(a)(b) | closure under disjoint union, proper difference | P | exact | — | Model A | proved |
| `legitimizingVal_univ_iff`, `legitimizingVal_empty` | radical I5.3(d), I5.5(c) | `Ω` ⟺ unconditional; `∅` vacuous | L | exact | — | — | proved |
| `legitimizingVal_compl_iff` | radical I5.3(e) corrected | for legitimizing `L`: `Lᶜ` legitimizing ⟺ `Ω` legitimizing | C | variant (printed biconditional false, F14; probe `ModelBPhiNotLegit`) | — | — | proved |
| `modelA_legit_02`, `modelA_legit_03`, `modelA_not_legit_union`, `modelA_not_legit_inter` (`WitnessesB`) | radical I5.3(c) | non-closure under union and intersection | N+ | exact | — | themselves | proved |
| `defect_decomposition` (+ `_ratio`) | radical I5.4 | unconditional defect = defect on the illegitimate part | P | exact | — | — | proved |
| `legit_hits_bound`, `legit_misses_bound` | radical I5.5(a) | `c·π(L∩C) ≤ h_c`, `(1−c)·π(L∩C) ≤ m_c` | L | exact (product form; one-step monotonicity from the definition) | — | Model B attains | proved |
| `legit_cell_le_cellBound`, `legit_mass_le_sum_cellBound` | radical I5.5(a) | per-cell and summed finite bound | P / C | weaker: bound, not equality | — | `modelB_attained` (attained), `modelA_bound` 7/8 (not attained, F4) | proved |
| `modelB_attained`, `modelA_bound` | radical I5.5(a) | bound `1` attained; bound `7/8` | N+ | exact | — | themselves | proved |
| atomless equality; open problem 4 | radical I5.5(a), open 4 | — | — | — | — | — | not attempted |

## T7 — composition (load-bearing)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `mass_eq_sum_cells` | radical I3.3(a), I5.6(c) | reflecting deferrer = cell-weighted mixture of rows | P | exact | — | — | proved |
| `legitimizingVal_compose`, `valueReflectsOn_compose` | radical I5.6(c), joint-final Prop 7 | function form at step 1 + value form at step 2 ⟹ `L₁₂ ∩ L₂₃` legitimizing | P / C | exact | — | positive `compose_positive_witness` (`WitnessesE`, r1: proper `L₁₂`, `L₂₃`, `F₃` strictly finer); negative `s5` | proved |
| `reflects_restrict_of_cells_subset` (`Compose`, r1) | radical I5.6(c) | conditioning on a union of `F`-cells preserves function form | P | exact | — | `compose_positive_witness`, `frame4_conditional_totalTrust` | proved |
| `compose_positive_witness` (`WitnessesE`, r1) | radical I5.6(c), mandate T7 | the theorem's full package on the depth-2 tree, `L₁₂ = {X₁ = 1}`, `L₂₃ = {X₂ = 1}`, composite `{3, 7}` | N+ | exact | — | itself | proved |
| `s5_value_form_does_not_compose` (`WitnessesB`) | radical I5.6(c), joint P.8 | value form at both steps, function form failing, composite failing | N+ | exact for the negative claim (step-one value cell trivial, disclosed; the failing cell is the value-form one, `5/16 ≠ 3/8`, not the note's function-form number) | — | itself | proved |

## T8 — minimal viability

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `legitimizingVal_iff_condIndep_cells` | miri I5.2 corrected | viable ⟺ `L ⊥ φ` given the cell partition | L | variant (cells, not `O`; F3); a restatement under value form — the content is the choice of partition plus the next two rows | — | `twoObs_legit_not_condIndep` | proved |
| `legitimizingVal_of_condIndep_fibres` | miri I5.2 (⇐) | `L ⊥ φ | O` suffices for the own refinement | P | exact (⇐ half; ⇒ false) | — | `twoObs_legit_not_condIndep` (⇒ fails) | proved |
| `twoObs_legit_not_condIndep` (`WitnessesD`, r1) | miri I5.2, F3 | legitimizing yet not `L ⊥ φ | O` (two observations announcing `1/2`) | N+ | exact | — | itself | proved |
| `legitimizingVal_preimage` | miri I5.2 | `σ(O)`-events are viable | L | exact | — | — | proved |
| `sensorCorrect_not_legitimizingVal` (`WitnessesD`, r1) | miri I5.2 | "the sensor reported correctly" is not viable on the 4-atom joint (`P(W | Pr, L) = 1 ≠ 2/5`) | N+ | exact | — | itself | proved |
| `blackwellLE_of_const`, `blackwellLE_ofMap_id` (`WitnessesD`, r1) | Blackwell (infrastructure for I6.3) | constants are garblings of everything; everything is a garbling of the perfect experiment | P | exact | — | the two instances | proved |
| `coinArm_strictlyDelegitimizing`, `evidence_strictlyLegitimizing` (`WitnessesD`, r1) | miri I6.1, I6.3 | forced press on tails strictly delegitimizing; perfect sensor given the evidence strictly legitimizing | N+ | exact | — | themselves | proved |
| `cell_refineFrame_eq_fibre` | miri I7.2, 2-010 | "I will believe `ρ`" is a fibre (candidates) | L | exact (null-fibre caveat) | — | — | proved |

## T9 — selection (load-bearing)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `cell_condRow`, `refineFrame_reflects`, `refineFrame_immodest` | armstrong T1, selection R1.1 | refinements reflective and immodest | P | exact | — | `frame4` | proved |
| `selectFrame_eq_refineFrame` | selection R1.1, armstrong A1 | retaining selection = refinement along `(s, f (s ·))` | P | variant (per-`k`) | — | `τ₁₃`; `sForget` (negative) | proved |
| `selectFrame_reflects/valueReflects/estimateMatching/totalTrust/value` | selection R1.1, radical Sel.4 | selection preserves every form | C | exact | — | `stopped_frame_reflects` | proved |
| `retainsGrounds_of_refines` | selection R1.1 hypothesis | R1.1 is a corollary | L | exact | — | — | proved |
| `retainsGrounds_of_adapted` (`WitnessesC`) | selection R1.3, radical Sel.1 | adaptedness *is* per-`k` retention, by definition (the identity `h`) | L | exact | — | — | proved |
| `stopped_frame_reflects` (`WitnessesC`) | selection R1.3, radical Sel.1 | the rule `τ₁₃` on the 16-atom tree is reflected, value-reflective, estimate-matching — an application of `selectFrame_reflects` (`τ₁₃_retains` is the only computation; no numeric property of the frame is checked) | N+ | exact | — | itself; probe `StoppingNoCommonG` shows it is not an R1.1 instance | proved |
| `sForget_not_retains`, `sForget_not_estimateMatching`, `sForget_not_reflects` | selection R2.2(i), C1 | the forgetting rule breaks everything | N+ | exact | — | itself | proved |
| `pathMax_not_estimateMatching`, `τmax_not_retains` (`WitnessesE`, r1) | radical `s3`, selection R2.2(i), T9(b) | the path-maximum rule: `E[P_τ(φ)] = 67/108 ≠ 1/2`, not estimate-matching, not reflected, not retaining | N+ | variant: depth 2 (`67/108`) for depth 3 (`353/540`) | — | itself | proved |
| `faceValue_not_valueReflectsOn`, `σ2_not_retains` (`WitnessesE`, r1) | radical Sel.2, T9(c) | "adopt the larger": `E[ρ_σ] = 31/54`, `P(φ | ρ_σ = 2/3) = 8/13 ≠ 2/3`; the retained successor reflective, announcing `1/2` at world `1` | N+ | exact | — | itself | proved |
| `cellConstant_choice_le_refineFrame_value`, `sum_maximizer_eq_refineFrame_value` (`Dominance`, r1) | selection R2.4, corr-wf14-051, T9(e) | a cell-constant action rule is weakly dominated by the refinement's cellwise maximizer, which attains the bound | P | exact (world-indexed payoffs; belief-indexed excluded) | — | `twist_choice_le_refineFrame_value` | proved |
| `rowsConstant_choice_le_refineFrame_value`, `twist_choice_le_refineFrame_value` (`Dominance`, r1) | selection R2.4, corr-wf14-051 | any frame with rows constant on positive cells — the twist family in particular — is weakly dominated under every tie-break | C | exact (whole family) | — | family | proved |
| `bothZero_builder` (`WitnessesF`, r1) | joint-final Prop 6′ corrected, E4; corr-wf14-062, 2-006, T9(g) | fully-retaining successor reflective; `1/325 < 1/25` on the `13/20` branch, `1/5` on the mixed branch, face value `1/37` | N+ | exact | — | itself | proved |
| C4 kernel change (d)(iii); randomization (f) | T9(d)(iii), T9(f) | — | — | — | — | — | not built (stretch) |

## T10–T17

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `sup'_sum_le_sum_sup'` | armstrong I6.2, joint-final P.5′ | finite Jensen for `max` | P | exact | — | — | proved |
| `good_of_estimateMatching`, `good_refineFrame`, `refineFrame_value` | armstrong I6.2 | Good's theorem | P / C | exact | — | `good_voi_7_20` (`WitnessesF`, r1: `1/20` vs `2/5`, VOI `7/20`) | proved |
| `good_voi_7_20` (`WitnessesF`, r1) | armstrong `reflection.py` T4, I6.2, I17.2 | the T4 instance: estimate matching exact, VOI `7/20 > 0` | N+ | exact | — | itself | proved |
| `sum_voi_le_voi` | joint-final Prop 5′ | martingale posteriors lower expected residual VOI | P | exact | — | `voi_halves` (`8 → 4`), `voi_single_signal_raises` (`WitnessesF`, r1) | proved |
| `voi_halves`, `voi_single_signal_raises` (`WitnessesF`, r1) | joint-final Prop 5′ remark, T10(c) | revealing `θ` w.p. `1/2` halves `8 → 4`; one signal raises `8/5 → 8` while the expectation stays `8/5` | N+ | exact | — | themselves | proved |
| `totalTrust_of_partition`, `totalTrust_of_restrict_compl` | ddb L-C | partition lemma | P | exact | — | positive `frame4_conditional_totalTrust` (`WitnessesD`, r1: both branches); `ddb4` shows the converse fails | proved |
| `ddb4_legitimizingTT`, `ddb4_not_legitimizingTT_compl`, `ddb4_not_totalTrust` (`WitnessesA`) | ddb I5 witness | converse of L-C fails | N+ | exact | — | itself | proved |
| `legitimizingTT_iff_forall_legitimizingVal` | mandate T11(c) | the two senses coincide under INT | C | exact | — | `frame4_conditional_totalTrust` under INT with `L = {0,1}` (r1); `fig3_legitimizingTT_not_val` without INT | proved |
| `legitimizingTT_union_of_disjoint` | T11(d) | disjoint TT-legitimizing union | P | exact | — | — | proved (intersections not attempted) |
| `clarity_tfae` | mm Cor I4.1 | Value ⟺ TT ⟺ Reflection ⟺ rows are conditionals, immodest frames | C | weaker (accuracy leg omitted) | — | `frame4` | proved |
| `no_reflective_of_worldIndependent`, `no_reflective_uniform_push` | radical I7.2 | no reflective prior for a world-independent push | P / N+ | weaker: world-independent push (the note claims "generic"); probe `PushReflectiveSat` shows the predicate is satisfiable | — | itself | proved |
| `universalSelfRefSpace_exists_open` (`SelfRef`, restated r1) | radical I7.1 | a universal self-referential space exists: `∃ X : SelfRefSpace W, X.IsUniversal` (`W` finite discrete nontrivial) | OPEN | variant (`T = Unit`, topological reading, continuous test coalgebras); the round-0 statement was trivially true (F16) | — | — | open (listed) |
| `transport_compliance` | joint-adversary A.13.1 | the function-form transport is an identity | L | exact | — | — | finding |
| `e3prime_witness` (`WitnessesD`, r1) | joint P.7 E3′, joint-final Thm B sharpness (a), T16(b) | value form on `{X}` holds (`9/10` both sides), on `{Z}` fails (`1/20` vs `−191/5000`); builder complies (`60/109 ≥ 1/5`), successor overrides (`6/55 < 1/5`) | N+ | exact (`X = (1, −4)` reconstructed from the printed expectations, F18) | — | itself | proved |
| `E_factorized_eq`, `sup'_factorized_eq` (`Expanded`, r1) | bli-soto-b-055, corr-core-003, T14(a) | factorized joint ⟹ expected expanded utility = expected mixed utility; best values agree | L | exact | — | — | proved |
| `mem_convexHull_range_iff_exists_mixture` (`Expanded`, r1) | bli-soto-b-055, T14(b) | `Ū ∈ convexHull (range U) ↔ ∃ μ` probability on `Θ` | D | exact | — | — | proved |
| `point_martingale_of_reflects` (`Expanded`, r1) | corr-core-006, T14(c) | `∑_w π w · P_w(θ) = π θ` under Reflection | L | exact | — | — | proved |
| `table2_allCorrect`, `table2_printed`, `table2_aliceOpens` (r1), `table4_bob`, `table4_alice`, `verdicts_unchanged` (`Slips`) | herrmann-2025 §4.1–4.2, App. A/B | MM's numbers recomputed; verdicts through the transcribed tables (no hand-entered numerals since r1) | N+ / L | exact | — | themselves | proved |
| T15, T16(c), T18; T5 extension; T6 stretches; T11(d) intersections; T13(b) | — | — | — | — | — | — | not done (report) |
