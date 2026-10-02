# corr-joint-process — ledger

*One row per headline ([STANDARDS](../../STANDARDS.md) §6). Namespace prefix `Cleanroom.Corrigibility.CorrJointProcess.` omitted; the parent's declarations are `Cleanroom.Found.CorrThreeStep.…`. Hyps column lists only (b)/(c); "—" means every hypothesis is (a). Following the parent's convention, source-stated assumptions of the setting (right sign `α ≤ β`, the continue-by-default regime, the floor `ε_i ≥ ε_∞`, the seal) are graded (a) because every theorem quantifies over them as named hypotheses rather than assuming them of a fixed object; (a) there means "named in the statement, nothing hidden". Witness column names the N+ instance inhabiting the row's full hypothesis package. Status `proved` throughout; `refuted` rows are the source's claims (the surviving neighbour named in the Claim column and in [corr-joint-process-findings](corr-joint-process-findings.md)). Gate PASS on all 13 modules at commit `9433705f` (re-run after the open-list fix). The mandate's rule (Known issue 3): the parent's threshold identity appears in many coats — T2, T6, T7(a), T13(c), T14(b), T16(a), T21(i) — and each such row is `L`; the rows carrying a real argument are marked `P`/`C` and argued in the report.*

## Definitions of record (Kind D)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `JointRound` | joint-final.md S.1–S.2 (053) | one round: prior on `Θ × Y`, `wrong`, stakes `c, h`, sensor in `[0,1]`; `toThreeStep` is the parent's Setting S on `Θ × Y` with `Sh = {stop}` | D | exact (`wrong : Θ → Bool`) | — | `Cellwise.e3`, `Battery.inclRound` | proved |
| `JointRound.cell`, `cellMass`, `cellErrMass`, `cellRightMass`, `cellPressMass`, `cellPressSum`, `cellEps` | joint.md S.3, C(i-R) | cells and their product-form masses; `Z_i = E[X 1_Pr 1_{y=i}]` (parent's `pressExpectOn`); `ε_i` derived, junk-guarded | D | exact | — | `e3_cellA_overrides` | proved |
| `JointRound.cellwiseBelowThreshold`, `averagedBelowThreshold` | joint.md C(i-R) (054) | cellwise (i) `Z_i ≤ 0`; averaged (i) is the parent's `belowThresholdIneq` | D | exact (denominator-free) | — | `e3_averaged` | proved |
| `JointRound.blind` | joint-final.md S.1 | blind oversight: two rates through `wrong` | D | exact | — | `e3` | proved |
| `RepresentationalCoverage`, `planGain`, `KnowledgeCoverage`, `HarmCoverage` | joint-final.md S.6 | S.6's three grades | D | weaker (representational: no "`V_θ` correctly represented" clause in a one-`V` model) | — | — | proved |
| `SealedTarget` | joint-final.md S.1 ("adopted, not derived") | A0 on the value marginal across first actions — the seal's finite shadow, named in every use | D | exact (shadow) | — | `sealedTarget_of_A0` | proved |
| `mixture`, `mixtureRound` | joint.md P.7 (E3), Pattern D | `P(θ, i) = w_i ρ_i(θ)`; the blind mixture of two-state cells | D | exact | — | `e3` | proved |
| `inclusionRound`, `ruleSum` | joint-final.md Prop. 1′ (055), Pattern B | overseers seeing `f ω` press iff their cell sum is negative — a derived `{0,1}` sensor | D | exact | — | `Battery.inclRound` | proved |
| `JointRound.cellPressValue`, `cellSilentValue`, `refinedValue`, `coarseValue` | joint-final.md Prop. D4− (064) | the refined (per-cell) and coarse (per-branch) successor values | D | exact | — | `e3_refined_gt_coarse` | proved |
| `uPress`, `vSilent` | joint.md P.2 (056) | the corpus's `u = −Δ₋`, `v = Δ₊` | D | exact | — | — | proved |
| `planVoi`, `matchValue`, `threePlanPrior` | joint-final.md P.4′, P.5″ (058, 060) | plan-choice VOI with the null plan; the match menu; the `(p, (1−p)/2, (1−p)/2)` prior | D | exact | — | `planVoi_three` | proved |
| `reversibilityFamily` | joint-final.md Prop. 6 (061), Pattern C | `A₁ = Bool`: reversible vs irreversible-with-side-benefit `b` | D | exact | — | `reversibility_witness` | proved |
| `floorPosterior`, `epsNoFloor`, `epsWithFloor`, `epsMaxFloor`, `oddsBound` | adv A.16.1; joint.md P.9 (066, 2-003) | the Bayes recursion for the floor hypothesis; the three requirement sequences | D | exact; `epsWithFloor` **variant** (generator reverse-engineered, finding F-6) | — | `requirement_table` | proved |
| `probOf`, `bernoulliProd`, `threeFail` | Cor. B′ (065) | finite-event probability; `T` independent Bernoulli failures; a three-point witness | D | exact | — | `independent_bound_vacuous` | proved |
| `Content`, `Content.cellOf`, `cellSum`, `listenValue`, `forcedValue`, `opaqueValue`, `blindValue`, `silentValue`, `silentListen`, `marginMinus`, `convMargin`, `piStar` | anticipatory-final.md S5 (016, 017) | a content (push, realized index, forced action) and `V_C`, `V_P`, `V^op`, `V^bl`, the `¬push` branch, `Δ₋(Q)`, `Δ_C(Q; π)`, `π*(Q)` | D | exact (finite shadow); `piStar` exact under `V^fail < V_C` | — | `Twists.twist_listen_forced` | proved |
| `pushWorld`, `pushU`, `pushEvent`, `shutdownContent`, `actOfBelief`, `beliefContent`, `cellPost`, `IsRefining` | anticipatory.md script A; anticipatory-final.md S6(b), S9 | the two-state push-world `World × Bool × Bool`; forced shutdown; the argmax rule with ties toward continuing; the twisted contents; the refining predicate | D | exact | — | `Twists.qPost_refining` | proved |
| `fakingFamily`, `fakingValue` | detection.md R2 item 2; anticipatory.md P5 (021) | the faking model as a Setting S instance: the press is the modification landing; faking costs `d` on both branches | D | exact (A1 fails for honest by design, disclosed) | — | `faking_table` | proved |
| `worldIndexedStake` | christiano-respondent.md Q3 (2-004) | `h_L = (1−w)h − w c_err` | D | exact | — | `a3b_witness` | proved |
| `inValue`, `shValue`, `refinedShutdown`, `p6World`, `ruleSumOn`, `inclusionContent` | anticipatory.md P6 (022) | in-channel and shielded successor values; the refined successor; the P6 world; the inclusion content (generic form of `ruleSum`) | D | exact | — | `blind_witness_refined_50` | proved |
| `fastValue`, `hurryFamily` | anticipatory.md P8 (024) | the hurried plan's value; SLOW/FAST as `A₁ = Bool` with interruption value `v` | D | exact (A1 fails for SLOW when `v ≠ 0`, disclosed) | — | `hurry_witness` | proved |

## T1 — the joint round

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `JointRound.cellwise_imp_averaged` | joint-final.md Prop. 1 (054) | cellwise (i) in every cell ⟹ averaged (i) | L | exact | — | `e3` (the converse's failure) | proved |
| `JointRound.cellwise_unit_iff` | mandate T1 | on the trivial partition cellwise (i) is the parent's predicate | L | exact | — | — | proved |
| `JointRound.averaged_iff_deltaMinus_nonneg` | filler.md F2(iv) on the round | averaged (i) ⟺ `Δ₋ ≥ 0` (⟺ D1 by the parent) | L | exact | — | `e3_press_sum` | proved |
| `JointRound.blind_cellPressSum` | joint.md P.1 | `Z_i = m_R α c − m_W β h` on a blind round (no ratios) | L | exact | — | `e3_cellA_overrides` | proved |
| `sealedTarget_of_A0` | joint-final.md S.1 | A0 implies the seal | L | exact | — | — | proved |

## T2 — Prop. 1

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `blind_cellPressSum_eq_twoState`, `blind_cellwise_iff_deltaMinus` | joint-final.md Prop. 1 (054) | the positive-mass cell of a blind round *is* `twoState (ε_i) α β c h`: `Z_i = −P(y=i) Δ₋(ε_i)`; cellwise (i) ⟺ `Δ₋(ε_i) ≥ 0` | L | exact | — | `e3` via `mixture_cellwise_iff` | proved |
| `blind_cellwise_iff_odds`, `blind_cellwise_iff_threshold` | joint-final.md Prop. 1 (the three forms) | ⟺ `α/β ≤ (ε_i/(1−ε_i))(h/c)`; ⟺ `c/(c+h) ≤ P(W∣Pr,i)` | L | exact | — | `e3_cellA_posterior` (`6/55 < 1/5`) | proved |
| `mixture_cellPressSum`, `mixture_cellwise_iff` | joint-final.md Prop. 1, Lemma B, Cor. B′ (054, 063, 065) | on the mixture `Z_i = −w_i Δ₋(ε_i)`; cellwise (i) ⟺ component's `Δ₋ ≥ 0` — Lemma B's function-form identity and Cor. B′'s transport clause, as the source's "Kind S" identity | L (source verdict: S) | exact | — | `e3_cellA_overrides`, `e3_cellB_complies` | proved |
| `e3_averaged` | joint.md P.7 (E3; 063) | averaged (i) holds (`−3/20`) while cell A fails (`1/40 > 0`): averaged ⇏ cellwise | N+ | exact | — | itself | proved |

## T3 — Prop. 1′

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `inclusion_cellPressSum` | joint-final.md P.1′ | `Z_i = ∑_{k : g k = i, m_k < 0} m_k` (tower step, product form) | L | exact | — | `Battery.incl_cellB` | proved |
| `inclusion_cellwise` | joint-final.md Prop. 1′ (055, 2-009) | under inclusion cellwise (i) holds in every cell, every `ε`, no rate condition | P (small) | exact | — | `Battery.incl_cellB` (`−7/40 ≤ 0`) | proved |
| `inclusion_cellPressSum_neg` | joint-final.md Prop. 1′ ("positive press probability") | strict: `Z_i < 0` where the press has mass | P | exact | — | `Battery.incl_cellB` | proved |
| `inclusion_pressless` | joint-final.md P.1′ ("both are `0` and D1 is vacuous") | a cell with no negative sub-cell has press mass `0` | L | exact | — | `Battery.incl_cellA_pressless` (N−) | proved |
| `Battery.incl_cellB_posterior` | adv (E) | the agent complies at `54/95 ≥ 1/5` in cell B | N+ | exact | — | itself | proved |

## T4 — Prop. 3′ (load-bearing 1)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `inParallelogram_of_lower_alpha` | joint-final.md P.3′ (057) | for `0 ≤ α' < α ≤ β ≤ 1`, `(α, β)` is a garbling of `(α', β)`: closed-form stochastic channel `(λ₀, λ₁) = (β(α−α')/(β−α'), 1 − (α−α')(1−β)/(β−α'))` | P | exact (`β = 1` included) | — | `steering_certificate_numbers` (`12/145, 137/145`; `1/10, 14/15`) | proved |
| `not_inParallelogram_of_lower_alpha` | joint-final.md P.3′ ("`λ₀ < 0`"); joint.md S.4 | the reverse fails: `(α', β)` is not a garbling of `(α, β)` | P | exact | — | `steering_certificate_numbers` (`λ₀ = −12/125`) | proved; **refutes** joint.md S.4 (F-1) |
| `blackwellLT_of_lower_alpha` | joint-final.md Prop. 3′ | lowering `α` at fixed `β` is a strict Blackwell improvement (`tt-finite-frames`'s order) | P | exact | — | `steering_package` | proved |
| `twoState_twoOptionValue_anti_alpha` | joint-final.md Prop. 3′ ("pays up to …") | `V^free(α, β) ≤ V^free(α', β)` for `α' ≤ α ≤ β`, `c, h ≥ 0` (direct, closed forms) | P | exact | — | `steering_gains` | proved |
| `twoState_twoOptionValue_lt_of_flip` | joint-final.md P.3′ ("strict when the posteriors differ") | strict under `u' < u`, `u' < 0`, `v' > 0` (the mandate's `u' < min(u, 0)` in the regime) | P | variant (F-13: "posteriors differ" is not sufficient) | — | `steering_package` | proved |
| `steering_flip`, `steering_gains` | joint-final.md Prop. 3′; adv (A) | at `ε = 1/50`: overrides before (`Δ₋ = −1/20`), complies after (`71/2500`); gains `71/2500`, `6/125`, `9/125`, `9/100` — D1 bought | N+ | exact | — | themselves | proved |

## T5 — Props. 4 / 4′ (load-bearing 2)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `twoState_voiButton2_perfect` | joint-final.md Prop. 4 (058) | the perfect sensor `(0, 1)` attains `min((1−ε)c, εh)` (bound: parent's `twoState_voiButton2_le_perfectInfo`) | L | exact | — | `Battery` (c) | proved |
| `planVoi_uniform_match` | joint-final.md P.4′ | `planVoi = 10 − max((10 − 2n)/(n+1), 0)` on the match menu | L | exact | — | `planVoi_three` | proved |
| `planVoi_three` | joint-final.md P.4′; adv (D) (2-002) | three plans: `8` against the press-sensor bound `4/3` | N+ | exact | — | itself | proved |
| `planVoi_ge_eight` | joint-final.md Prop. 4′ | for `n ≥ 2`: `planVoi ≥ 8`, press-sensor bound `≤ 10/(n+1)` | P | exact | — | `planVoi_three` | proved |
| `planVoi_ratio_unbounded` | joint-final.md Prop. 4′ ("grows without bound") | `∀ M ∃ n`, plan-choice VOI exceeds `M` × the press-sensor bound | P | exact | — | `planVoi_three` | proved; **refutes** joint.md l. 125 (F-2) |

## T6 — Prop. 5″

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `knowledge_gap_eq`, `knowledgeCoverage_iff` | joint-final.md P.5″ (060, 2-010) | `∣G − G°∣ = ε(c+h)`; `δ`-coverage ⟺ `ε ≤ δ/(c+h)` | L | exact | — | `covered_numbers` | proved |
| `covered_odds_bound` | joint-final.md Prop. 5″ | covered ∧ cellwise (i) ⟹ `α/β ≤ (δ/(c+h−δ))(h/c)` | C | exact | — | `covered_numbers` (`4/49`, `4/499`) | proved |
| `covered_voi_bound` | joint-final.md Prop. 5″ | covered ⟹ `VOI₂ ≤ δh/(c+h)` | C | exact | — | `covered_numbers` (`2/25`) | proved |
| `planVoi_threePlan` | joint-final.md P.5″ (the table) | posterior `p ≥ 1/3` on the truth: `voiTheta = 12(1−p)` | L | exact | — | `threePlan_table` (four cells) | proved |

## T7 — Prop. 2

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `twoOptionValue_sub_hardButtonValue`, `hard_eq_soft_iff`, `soften_iff` | joint-final.md Prop. 2 (056, 018) | `V^free − V^forced = max(−Δ₋, 0)`; hard = soft ⟺ `Δ₋ ≥ 0` (⟺ D1); softened at price `κ` ⟺ `κ < −Δ₋` | L | exact | — | `soft_worthless_witness` | proved |
| `twoState_soft_worthless_of_override` | joint-final.md Prop. 2 ("Where I overrule the adversary"), P.2 | right-signed sensor: `Δ₋ < 0 ⟹ Δ₊ ≥ 0 ∧ V^free = V^none` — soften ≡ disable | P (small) | stronger (only `h ≥ 0`, F-14) | — | `soft_worthless_witness` (`9/10 = 9/10`) | proved |
| `inverted_soft_not_none` | joint-final.md Prop. 2 ("only for inverted sensors") | with `β < α`: `u > 0`, `v < 0`, `V^free ≠ V^none` | N− | exact | — | itself | proved |

## T8 — Prop. D4−

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `JointRound.coarse_le_refined` | joint-final.md Prop. D4− (064) | the builder weakly prefers the refining successor (a finer partition admits every coarser policy) | C | exact | — (the builder's conditional on a cell is the successor's belief by `mixture`; no reflection predicate) | `e3_refined_gt_coarse` | proved |
| `JointRound.coarse_lt_refined_of_split` | joint-final.md P.D4− ("strictly when …") | strict when two cells' press decisions differ | C | exact | — | `e3_refined_gt_coarse` (`27/40 > 13/20`) | proved; **refutes** the develop Summary (F-4) |
| `JointRound.coarseValue_eq_twoOptionValue` | bridge | the coarse value is the parent's `V^free` | L | n/a | — | — | proved |

## T9 — Cor. B′ (load-bearing 4)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `probOf_inter_ge`, `union_bound`, `union_bound_range` | joint-final.md Cor. B′ (065, 2-011) | `P(⋂_{t∈s} L t) ≥ 1 − ∑_{t∈s} λ_t`, `λ_t = 1 − P(L t)` | C (`Finset` induction) | exact (legitimacy events given as `Finset`s; S.8 pending) | — | `disjoint_attains` (tight), `independent_bound_vacuous` | proved |
| `partial_lt_one_summable` | adv A.14.2 | bound informative at every horizon ⟹ `λ` summable with `∑ λ ≤ 1` | P | exact | — | `budget_numbers`, `const_bound_dies` | proved |
| `partial_lt_one_of_tsum_lt` | adv A.14.2; Cor. B′ ("a potential below 1") | summable with `∑ λ < 1` ⟹ informative at every horizon | P | exact | — | — | proved |
| `const_bound_dies`, `bound_pos_iff`, `budget_numbers` | adv (G) | constant `λ > 0` kills the bound; `9/10` at `T = 10`, `0` at `100`, `−1` at `200` | L / N+ | exact | — | themselves | proved |
| `disjoint_attains` | mandate T9(c) | two disjoint failures of `1/100`: `P = 98/100 = ` the bound | N+ | exact | — | itself | proved |
| `bernoulliProd_all_ok`, `bernoulliProd_round_ok`, `independent_bound_vacuous` | mandate T9(c); adv A.14.2 | independent failures: `P(⋂ L t) = (1−λ)^T`, each `λ_t = λ`; at `T = 100`, `λ = 1/50` the bound is `−1` while `P > 1/10` | L / N+ | exact | — | themselves | proved |
| transport clause (d) | Cor. B′ ("content nil under (i-A)") | = `Cellwise.mixture_cellwise_iff` | L (source: S) | exact | — | `e3` | proved (F-5) |

## T10 — Prop. 8 (load-bearing 5)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `floor_product`, `floor_cellwise_mixture`, `floor_cellwise_of_odds` | joint-final.md Prop. 8 (066, 2-003); joint.md P.9 | under the floor `ε_i ≥ ε_∞` and the stationary target (product or odds form), cellwise (i) in every cell of a blind mixture round | C | exact | — (the floor is the source's named hypothesis) | `floor_target_four_ninetynine` (`4/99`) | proved |
| `floorPosterior_strictAnti`, `floorPosterior_tendsto_zero`, `floorPosterior_least_crossing` | adv A.16.1, (F) | for `0 < k < 1`: strictly decreasing, `→ 0`, least crossing of every `τ > 0` exists | P | exact | — | `floorPosterior_witness` (`p_50 < 10⁻⁴`), `floorPosterior_crossing_44` (`n₀ = 44`) | proved |
| `floorPosterior_const_iff` | joint-final.md Prop. 8 ("likelihood ratio exactly 1"); INDEX §C5 | preserved at every round ⟺ `k = 1` | P | exact | — | `floorPosterior_witness` | proved; **refutes** joint.md l. 139's headline (F-3) |
| `requirement_table`, `epsWithFloor_bound_closed`, `epsWithFloor_bound_tendsto`, `epsMaxFloor_bound_eventually` | joint.md P.9; 2-003's flag | the develop's printed sequence is generated by `ε'_t = 2^{−t}/5 + (1−2^{−t})/100`, closed form `4(2^t+19)/(99·2^t−19) → 4/99`; the literal `max` form is `4/99` from `t = 5` | N+ / L / P / L | exact (`epsWithFloor` variant, F-6) | — | `requirement_table` | proved |

## T11 — Prop. 6

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `reversibilityFamily_value_irr`, `reversible_iff_side_benefit_le_voi` | joint-final.md Prop. 6 (061) | `V(irr) = E[X] + b`; in the regime reversible preferred ⟺ `b ≤ VOI₂`, and `VOI₂ ≤ εh` | C | exact | — (regime named) | `reversibility_witness` (`ε = 1/10`: `Δ₋ = 3/20 ≥ 0`, `VOI₂ = 3/20`, `b = 1/5` wins; `ε = 1/25`: `VOI₂ = 0`) | proved |

## T12–T13, T15–T16 — the modification menu

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Content.forcedValue_le_listenValue` | anticipatory-final.md Statement 2(a) (016); Milli Thm 1; HM Thm 1 | listening weakly dominates being forced | L | exact | — | `Twists.twist_listen_forced` (`Q_over`: `9/500 > 0`) | proved |
| `Content.forcedValue_eq_listenValue_iff` | Statement 2(a) ("equality iff") | `V_P = V_C` ⟺ every realized content's forced action attains the cell max | P (small) | exact | — | `twist_listen_forced` (`Q_post`, `Q_deq`, `Q_under` equal) | proved |
| `Content.blindValue_le_opaqueValue`, `opaqueValue_le_listenValue` | Statement 2(b) (Good twice) | `V^bl ≤ V^op ≤ V_C` | L | exact | — | `selfdistrust_table` | proved |
| `shutdown_marginMinus`, `shutdown_marginMinus_nonneg_iff` | Statement 2(e) (018) | forced shutdown: `Δ₋(∅) = min(Δ₋, 0)`; D2 at every positive cost ⟺ `Δ₋ ≥ 0` ⟺ D1 | L | exact (product form) | — | `twist_listen_forced` (`Q_sh` rows via `selfdistrust_table`) | proved |
| `e3prime` | joint.md P.7 (E3′; 063) | `E_π[X] = E_ρ[X]` and `π` complies do not make `ρ` comply (`ρ = (1/50, 1/10, 3/5)`, `π = (1/50, 1/100, 3/5)`) | N+ | exact | — | itself | proved |
| `Content.convMargin_eq`, `convMargin_pos_iff` | Statement 2(c) (017) | `Δ_C = π(V_C − V^fail) − (V_C − V_P)`; `> 0 ⟺ π > π*` under `V^fail < V_C` | L | exact | — | `selfdistrust_table` (`π* = 0, 1/11, 11/115`; inert at `ε = 1/50`, N−) | proved |
| `Content.trueLaw_keep_iff` | taylor-respondent.md item 14 (2-011) | under the true law `μ*`, keeping is optimal iff `π(V_C* − V^fail*) > V_C* − V_P*` (one substitution; "Total Trust on the kernel" is `V_P* > V^fail*`, an inequality) | L | exact | — | `selfdistrust_table` | proved |
| `refining_forced_eq_listen`, `refining_marginMinus_nonneg` | Statement 3(a) (019) | a refining content has `V_P = V_C`, `Δ₋ ≥ 0` | L | exact | — | `Twists.qPost_refining` + `twist_listen_forced` | proved |
| `Twists.converse_fails` | Statement 3(b) (019) | `Q_deq`, `Q_under` at `ε = 1/10`: `V_P = V_C`, `Δ₋ = 9/500 > 0`, not refining | N+ | exact | — | itself | proved |
| `TwoStep.twoStepForced_le_twoStepListen` | Statement 2(a), P4 | listening weakly dominates any forced belief over two steps | L | exact | — | `twoStep_witness` | proved |
| `TwoStep.bayesUpdate_zero`, `bayesUpdate_one` | P4 ("the dogmatic successor cannot move") | dogmatic beliefs `0`, `1` are fixed points of the `h₃` update | L | exact | — | `twoStep_witness` | proved |
| `TwoStep.twoStep_witness` | Statement 3(b), P4 (adv (B), `ε = 1/10`) | two-step `Δ₋(Q_deq) = 0`, `Δ₋(Q_post) = 18/625`, listen − forced(`Q_deq`) `= 18/625`: one-step welcome does not compose | N+ | exact | — | itself | proved |

## T14 — the faking iff (load-bearing 3)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `fakingValue_honest`, `fakingValue_fake`, `fake_gt_honest_iff` | detection.md R2 item 2 (021); anticipatory.md P5 | `V(honest) = −(1−e)h + eg`, `V(fake) = −d`; `fake ≻ honest ⟺ d < (1−e)h − eg` | L | exact | — | `faking_table` | proved |
| `accept_iff_threshold` | detection.md R2 item 2 ("§2.13(a)'s compliance threshold with its slots filled"); Statement 6(a) | the faking iff *is* the parent's `complianceThreshold_iff` at `q = e`, stakes `(h − d, g + d)`: accept iff `e ≥ (h−d)/(h+g)`, `0 < h + g` | C | exact | — (`0 < h + g` names the junk point) | `faking_table` (`e* = 49/60, 2/3, 1/3`) | proved |
| `never_fake_of_price_gt_harm` | mandate T14(b) | `d > h` ⟹ faking never chosen | L | exact | — | — | proved |
| `faking_table` | anticipatory.md P5 (three rows + the stopping prices) | `(1/100, 1/10)`, `(1/10, 1)` fake; `(1/2, 3)` honest; prices `247/50, 22/5, 2` | N+ | exact | — | itself | proved |

## T17 — the successor construction

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `succ_margin_eq`, `succ_margin_nonpos`, `shield_iff` | Statement 7(a) in 2(c)'s direction (022) | `V(IN) − V(SH) = V_P − V_C ≤ 0`; shielded at cost `χ` iff `χ < −Δ_C^succ` | L / C / L | exact (F-7 on 7(a)'s reversed sign) | — | `blind_witness_refined_50` | proved |
| `blind_witness_refined_50`, `blind_witness_coarse_50`, `blind_witness_20` | anticipatory.md P6 (script E) | blind: `ε = 1/50` refined `437/500` vs `469/500` (`−8/125`), coarse `−13/500`; `ε = 1/20` refined `−1/25`, coarse `0` | N+ | exact | — | themselves | proved |
| `inclusion_forced_eq_listen`, `inclusion_succ_margin_zero` | Statement 7(c) | under inclusion `V_P = V_C`, `Δ_C^succ = 0` for every prior (T3's mechanism + T13(a)'s equality clause) | C | exact | — | `inclusion_witness_50` (`469/500 = 469/500`) | proved |
| `disclosing_attains` | Statement 7(b) ("attains the shielded value in-channel at zero cost") | `V(refined, IN, inclusion) = V(refined, SH, blind) = 469/500` | N+ | exact | — | itself | proved |
| 020 limit (stretch) | Statement 4 | not formalized here beyond the parent's `epsStar` forms | — | — | — | — | not attempted (report) |

## T18 — preemption

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `fastValue_sub_hardButtonValue`, `hurry_gain` | Statement 9 (024); A31 (2-013(D)) | `V(FAST) − V(SLOW) = −Δ₋`; the gain from choosing to hurry is `max(0, −Δ₋)` | L | exact | — | `hurry_witness` (`−81/200`) | proved |
| `twoState_caution` | Statement 10, caution proposition; anticipatory.md P8 | right-signed live sensor, correct model: `Δ₋ < 0 ⟹ 0 < (1−ε)c − εh` | P (small) | exact (`h ≥ 0` only) | — | `hurry_witness` | proved |
| `hurry_witness` | anticipatory.md P8 (R5) | `FAST = 2/5`; `SLOW = 13/100, 161/200, 37/25` at `v = −5, 0, 5`; the argmax moves | N+ | exact | — | itself | proved |

## T19 — the battery, T21 — the anchors

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Battery` examples (a), (c) | `j1_examples.py` (a), (c) | E1: `VOI 3/20 → 0`, disable incentive `1/20`, needed `α₂ ≤ 12/245`; the bound at `1/50` | N+ | exact | — | themselves | proved |
| `Battery.i_inversion` | `j1_examples.py` (i) | the header's "inversion keeps `V^free`" fails at `ε = 1/10` (`13/20 ≠ 1/2`), holds at `1/50` | N+ (refutation of the scratch header) | exact | — | itself | proved (F-12) |
| `comply_iff_constitutive` | christiano-respondent.md Q3 (2-004) | the act-component and procedural rules coincide under constitutive stakes — the parent's `complianceThreshold_iff` | L | exact | — | `a3b_witness` | proved |
| `dodged_of_neg_stake`, `a3b_witness` | christiano-respondent.md Q3; legitimacy-general-final.md Stmt 4(b) A3b | a negative world-indexed stake is dodged at every `p ∈ (0, 1]`; A3b: threshold `90/91 > 19/20`, resisted at `19/20` | L / N+ | exact | — | `a3b_witness` | proved |

## T22(a) — the coined objects; 020 — the limit (`Coined.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `IrreversibilityBeforeCoverage`, `SensorImprovingSteering`, `InformativePressElicitation` | joint-final.md §J10 (068) | the three coined predicates: D1 intact ∧ `VOI₂ < b`; `α' < α ≤ β` ∧ `η <` gain; `β < β'` ∧ strict value gain | D | exact | — | `coined_witnesses` | proved |
| `twoState_twoOptionValue_mono_beta` | joint-final.md §J10 ("incentive to elicit presses") | raising `β` at fixed `α` never lowers `V^free` under a right-signed sensor (mirror of T4(b)) | P | exact | — | `coined_witnesses` (`13/20 → 77/100`) | proved |
| `coined_witnesses` | joint-final.md §J10 | the three predicates inhabited (T11's, T4's and a `β: 3/5 → 9/10` instance) | N+ | exact | — | itself | proved |
| `deltaMinus_tendsto` | anticipatory-final.md Statement 4 (020) | `Δ₋ → −αc` as `ε → 0` | L | exact | — | `epsStar_one_twentyeighth` | proved |
| `shutdown_resisted_iff_epsStar` | Statement 4 ("negative past `ε*`") | forced shutdown's `min(Δ₋, 0) < 0 ⟺ ε < ε*` (`0 < αc + βh`) | L | exact | — | `epsStar_one_twentyeighth` (`1/28`) | proved |
| refining `≤ εh` (020, last clause) | Statement 4 ("the refining content has `Δ₋ ≥ 0` … and `→ 0`") | `≥ 0` is `refining_marginMinus_nonneg`; the `εh` bound not written | — | — | — | — | not attempted (report) |

## Not attempted (stretch / extension; see the report)

| Target | Item | Disposition |
|---|---|---|
| T17 (020, last clause) | refining content's `marginMinus ≤ εh` | not attempted |
| T20 | 2-003 training-data model (`77/104`; omniscient-targeted never best) | not attempted; F-10 records the kernel-vs-menu flag |
| T22(b)–(d) | findings | F-9, F-15 |
| T23 | the faking iff at a general finite menu | not attempted |
