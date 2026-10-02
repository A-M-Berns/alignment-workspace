# corr-position-finds — ledger

*One row per headline ([STANDARDS](../../STANDARDS.md) §6). Namespace prefix `Cleanroom.Corrigibility.CorrPositionFinds.` omitted; file in the Declaration column's group heading. Every object of record is `corr-three-step`'s (`Cleanroom.Found.CorrThreeStep`); rows marked "shadow" state the two-point or finite shadow of an object another package owns and say so in the docstring. "regime" = the continue-by-default hypotheses `0 ≤ E_μ[X]` and `0 ≤ Δ₊`, always named. Hyps column lists only (b)/(c); "—" means every hypothesis is (a) (named in the statement, nothing hidden; source-stated assumptions of the setting — A0 at the pair, A1, the regime, the part-maximiser predicates — are graded (a) as in [corr-three-step-ledger](../corr-three-step/corr-three-step-ledger.md)). Witness column names the N+ instance inhabiting the row's full hypothesis package. Status: `proved` / `refuted` (the source's claim is false and the refutation is proved; per plan §0.4 rule 3 the findings file quotes the sentence with pointer, states the reading formalized with ATTRIBUTION-UNVETTED where chosen, and names the surviving neighbour — see the F-number) / `open`. Kinds are graded honestly: this is a findings package, and most rows are L or N+ by design; the four P rows are T1(a), T6's reflection failure (repair r2), T7(c) and T12. Gate: PASS (8 modules, 1266 declarations, axioms `propext`, `Classical.choice`, `Quot.sound`) after the last edit of repair round 2 (2026-09-30); rows marked "repair r1" / "repair r2" were added or relabelled then — see [corr-position-finds-report](corr-position-finds-report.md) §Repair round 1 and §Repair round 2.*

## Infrastructure (`Basic.lean`; no headline)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `d1At_iff_twoAct`, `d1At_iff_deltaMinus_nonneg_twoAct`, `twoState_d1At_iff` | filler.md F1/F2(iv) (via the dependency) | on `Sh = {stop}`, D1 is the one inequality / `0 ≤ Δ₋` | L | exact | — | every D1 cell below | proved |
| `posteriorSilent`, `twoState_posteriorSilent_wrong` | miri.md Dict-1 | `P(ω \| ¬Pr)`, the silence twin of `posteriorPress` (not in the dependency; API request) | D / L | exact under `pressMass < 1` | — | `w3_posteriorSilent_wrong` | proved |

## T1 — the manufactured silence (`Silence.lean`; F-1, F-7)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `pressMass_eq_of_condExp_eq` | §2.9 (CLAUDE); thornley item 4 (l. 81) | same conditional expectations at two actions with a shared prior and an informative press ⇒ same press mass (the incoherence) | P | exact (thornley item 4's derivation: two equalities plus an informative press; the word "inequalities" is inventory 091's, M-4) | — | `deceptionPair_incoherence` | proved; refutes the equality imposition (F-1) |
| `pressMass_eq_of_condExp_eq_Xo` | thornley item 4 | the same on `X = V(cont) − V(stop)` with `V` action-neutral | L | exact | — | `deceptionPair_incoherence` (via `deceptionPair_Xo_eq`) | proved |
| `deceptionPair`, `deceptionPair_incoherence` (+ six `deceptionPair_*` cells) | miri I9.4–I9.5 (`deception.py`); §2.9 | Leave `(1/20, 9/10)` and `a₁⁻` `(1/40, 9/20)` on one prior: same `E[X \| Pr] = −341/37`, informative press, masses `37/400 ≠ 37/800` ⇒ the silence-branch equality is refuted by the theorem (and `107/121 ≠ 43/109`) | D / N+ | exact | — | self | proved (the contrapositive on the corpus's numbers; added at repair r1) |
| `twoState_deltaMinus_sensor_scale` | miri I9.4; radical I9.2 | `Δ₋(qα, qβ) = q·Δ₋(α, β)` | L | exact | — | `halved_deltaMinus` | proved |
| `twoState_d1At_sensor_scale_iff`, `twoState_belowThresholdIneq_sensor_scale_iff` | miri I9.4; §2.9 | D1 / the inequality invariant under proportional deception (`q > 0`) | L | exact | — | `halved_d1At` | proved; **refutes** "cannot hold for every `a₁`" of the press branch under proportional deception (F-1) |
| `twoState_posteriorPress_wrong_sensor_scale` | miri I9.4; causal I15.2 | `P(W \| Pr)` invariant under `(qα, qβ)` | L | exact | — | `halved_posteriorPress_wrong` | proved |
| `halved_deltaMinus`, `halved_deltaPlus`, `halved_d1At`, `w3_posteriorPress_wrong`, `halved_posteriorPress_wrong` | miri I9.4 (`deception.py`) | `341/800`, `301/800`, D1, `18/37`, `18/37` at `(1/40, 9/20)` | N+ | exact | — | self | proved |
| `w3_posteriorSilent_wrong`, `halved_posteriorSilent_wrong` | miri I9.4–I9.5 (M1) | `2/363 → 22/763`: what deception changes is silence (the survivor) | N+ | exact | — | self | proved |
| `targeted_deltaMinus`, `targeted_not_d1At`, `targeted_posterior_below_threshold`, `honest_at_eps100_d1At` | miri I9.4 (targeted) | `−19/2000`, `¬ D1`, `4/103 < 1/21`; honest `261/2000 > 0` at the same `ε` | N+ | exact | — | self | proved (the sentence's true case) |
| `believed_voiButton2`, `halved_voiButton2`, `m2_pays` | miri I9.5 (M2) | `661/800`, `301/800`; pays `19/800` for `−341/800` (outside the regime, regime-free formula) | N+ / L | exact | — | self | proved |

## T2 — the deceiver's Blackwell side (`Silence.lean`; F-2)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `IsPostProcessing` | miri I9.4, I9.7 | binary-channel post-processing certificate (shadow of the Blackwell order; definition of record `lit-ddb-frames`', monotonicity `tt-finite-frames`'); complete for binary-output channels (a garbling kernel is a `2 × 2` stochastic matrix) | D | variant: two-point certificate, complete on this class (audit r2, fidelity N9) | — | `deceiver_is_garbling` | proved |
| `believed_not_postProcessing_of_honest`, `honest_not_postProcessing_of_deceiver`, `honest_not_postProcessing_of_targeted` | miri I9.4, I9.7 | the three reverse certificates are impossible (solved `(p, q)` = `(341/340, −9/340)`, `(2, 0)`, `(163/30, −7/30)`, outside `[0,1]²`): the three relations are strict, so "opposite sides" is not "both sides" | L | exact | — | — | proved (added at repair r2, adversarial N3) |
| `deceiver_is_garbling` | miri I9.7; §2.9 | `(1/40, 9/20)` from `(1/20, 9/10)` with `(1/2, 0)`; VOI falls | N+ | exact | — | self | proved |
| `believed_sensor_is_refinement` (was `taylor_is_refinement`; renamed at repair r1, N7) | miri I9.7; taylor.md l. 51 | `(1/20, 9/10)` from `(1/40, 9/10)` with `(349/350, 9/350)`; VOI rises | N+ | exact | — | self | proved; the attribution "this is Taylor's agent" is ATTRIBUTION-UNVETTED and inexact (F-2) |
| `targeted_is_garbling` | miri I9.4 (`deception.out` l. 6) | T1(c)'s `(1/20, 1/5)` from `(1/20, 9/10)` with `(37/170, 7/170)` (the script's `(133/170, 7/170)` in its drop/fabricate parametrisation) | N+ | exact | — | self | proved (added at repair r1, N8) |

## T3 — fully updated deference as arithmetic (`Fud.lean`; F-3)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `fud_band` | §1 (AUTHOR); §2.13(b); miri Prop. 10.5 | `0 < α ≤ β`, `ε < ε*` ⇒ `¬ D1` and `voiButton2 = 0` (regime derived) | C | exact | — | `targeted_in_band` | proved; the §1 sentence is true at the reflection grade, false at the decision grade without its condition (F-3) |
| `targeted_in_band` | §2.13(b); miri I9.4 | the targeted instance has `1/100 < ε* = 1/81`, `α ≤ β`, and `fud_band` applied to it yields `¬ D1 ∧ voiButton2 = 0` | N+ | exact | — | self | proved (added at repair r1, B3) |
| `epsStar_pos`, `fud_band_nonempty` | §2.13(b) | the failing band is nonempty for every `α > 0` | L | exact | — | self | proved |
| `kappa_deltaMinus_pos_iff` | §2.13(b) | `α = κε`: `0 < Δ₋ ↔ κ(1 − ε)c < βh` | L | exact | — | — | proved |
| `kappa_d1At_forall_iff`, `kappa_strict_forall_iff` | §2.13(b); channel-final S12(c) | for `κ ∈ [0, 1]` (so that `α = κε ≤ 1`; the escapes with `κ > 1` are outside the statement): D1 (resp. strict) at every `ε ∈ (0,1)` iff `κc ≤ βh` (same threshold; M-1) | L | exact | — | — | proved (Claim scoped at repair r2, fidelity N4) |

## T4 — Good's theorem up to `εβh` (`Fud.lean`; F-4)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `voiButton2_tendsto_zero` | §1 (AUTHOR); wentworth §2.4(b); miri I11.2 | `voiButton2(ε_t) → 0` along `ε_t → 0`, no regime | L | stronger: no regime | — | any `twoState` sequence | proved |
| `twoState_voiButton2_eq_max` | wentworth §2.4; filler F4(b) | in the regime `VOI₂ = max(εβh − (1 − ε)αc, 0)` | L | exact | — | `refinement_cell_regime` | proved |
| `twoState_deltaMinus_antitone_alpha`, `_monotone_beta` | shah C10 | `Δ₋` antitone in `α`, monotone in `β` | L | exact | — | `refinement_cell_regime` | proved |
| `twoState_voiButton2_antitone_alpha`, `_monotone_beta` | shah C10; miri I11.2(c) | in the regime at both sensors, `VOI₂` antitone in `α` / monotone in `β` | L | exact | — | `refinement_cell_regime` | proved |
| `refinement_cell_regime` | miri I9.7 | at `h = 10`: `α: 1/20 → 1/40` raises `VOI₂` `161/400 → 341/800`, both in the regime | N+ | exact | — | self | proved |

## T5 — the dictionary row is A0 (`Assumptions.lean`; F-5)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `naiveDep`, `naiveA0`, `firstStepValue` | miri I1.2, Dict-2 | the two instances; the T-agent's first-step value `obsMax press + obsMax silent` | D | exact | — | — | proved |
| `naiveDep_prefers_aMinus` | miri I1.2 (`naive_combination.py`); §2.8 (CLAUDE) | action-dependent prior: `17/2 < 44/5`, prefers the `U_N`-dominated action (Theorem 1) | N+ | exact | — | self | proved; **refutes** the "re-notation" reading of the row (F-5) |
| `naiveA0_prefers_aStar` | miri I1.2 | under A0: `8 < 17/2`, prefers `a₁*` | N+ | exact | — | self | proved |
| `firstStepValue_sub_eq`, `firstStepValue_lt_of_vN_lt` | miri I1.3 | on `{N, S}` under A0, perfect sensor, press-branch neutrality: `value(a') − value(a) = μ(N)(v_N(a') − v_N(a))`; dominated never chosen | L | weaker: instance-level, not the general iff (`also in corr-three-step-facts (2-002)`) | — | `naiveA0_ranking_cell` | proved |

## T6 — minimal viability needs `P(L)` (`Assumptions.lean`; F-8)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `legitPrior`, `legitPress`, `legitMix`, `legitThreshold` | miri I5.3 (`legitimacy_event.py`); §2.11 | the legitimacy-mixture instance and `q* = γE/(γE + Δ₋^L)` | D | exact (threshold: prior form, variant of the script's `P(L \| Pr)` form) | — | `legit_d1At_half` | proved |
| `legitPress_on_L`, `legitPress_off_L` | miri I5.3; §2.11 | conditional on `L` the sensor is `twoState`'s (`rfl`), for every `q` — the sensor identity, nothing about §2.11's equation | T | weaker: the sensor identity only; the reflection predicate is `corr-reflect-frames`' | — | — | proved (repair r1 carried miri I5.3's "holds by construction" as a (b) citation in this cell; it is a checked-and-false prose claim under §2.11's reading — the next rows — and is cited as nothing now; repair r2, fidelity B1) |
| `legitMix_pressMass`, `legitMix_posteriorPress_wrong_own`, `legitMix_posteriorPress_wrong_given_L` | §2.11 (`P_{t₂}(φ)`); miri I5.2–I5.3 | `P(Pr) = q·p_L + (1 − q)γ`; reading (A): the mixture agent's own `P(wrong \| Pr) = ε(qβ + (1 − q)γ)/P(Pr)`; reading (B): the `L`-conditional `P(wrong \| Pr, L)` is the honest instance's `εβ/(εβ + (1 − ε)α)` for every `q > 0` (I5.3's "by construction", as a posterior identity) | L | exact (press branch) | — | `legit_own_posterior_half`, `legit_L_posterior` | proved (added at repair r2, B1) |
| `legitMix_reflection_on_L_fails` | §2.11; miri I5.2 (the criterion `L ⊥ φ \| O`) against I5.3 | reading (A): for every informative sensor-latent (`α ≠ β`, `γ > 0`, `0 < ε < 1`) and every `q ∈ (0, 1)`, the two posteriors differ (by `ε(1 − ε)(1 − q)γ(α − β)` over a positive denominator) — §2.11's equation on `L` **fails** on the mixture, so by I5.2 this `L` is not viable | P | exact for `o = Pr` (where D1 lives); the full predicate is `corr-reflect-frames`' | — | `legit_reflection_on_L_fails_half`, `_quarter` | proved; **refutes** miri I5.3's "so this `L` *is* minimally viable in the author's sense" under I5.2's own criterion (F-8, F-20; added at repair r2, B1) |
| `legit_L_posterior`, `legit_own_posterior_half`, `legit_own_posterior_quarter`, `legit_reflection_on_L_fails_half`, `legit_reflection_on_L_fails_quarter` | miri I5.2–I5.3 | `18/67` vs `4/81` (`q = 1/2`, where D1 holds) and vs `48/1567` (`q = 1/4`, where D1 fails): the equation on `L` fails at both, so under reading (A) the criterion rejects both agents — orthogonal to D1, not empty | N+ | exact | — | self | proved (added at repair r2, B1) |
| `legitMix_obsExpect_press`, `_eq_mix` | miri I5.3 | `E[X 1_Pr] = q(−Δ₋^L) + (1 − q)γE` | L | exact | — | `legit_numbers` | proved |
| `legitMix_d1At_iff` | miri I5.3; yudkowsky C5; armstrong 7 | `Δ₋^L > 0`, `E > 0`: `D1 ↔ q* ≤ q` | L | variant: prior form; instance (general threshold `also in corr-three-step-facts (2-008)`) | — | `legit_d1At_half`, `legit_not_d1At_quarter` | proved; under reading (B) the criterion is satisfied by the agent it should exclude and the content sits in `P(L)`; under reading (A) it rejects the `q = 1/4` and `q = 1/2` agents alike (F-8; gloss corrected at repair r2, B1) |
| `legit_numbers`, `legit_d1At_half`, `legit_not_d1At_quarter` | miri I5.3 | `29/50`, `311/1000`, `290/601`; D1 at `1/2`, not at `1/4` | N+ | exact | — | self | proved |

## T7 — private information; the static form of Claim 2.4c (`PrivateInfo.lean`; F-12, F-13)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `rowInstance`, `cellSum`, `hCoarse`, `pressLow` | miri I4.3 (`common_prior.py`) | a row as a Setting-S instance; cell sums; the programmers' partition and press | D | exact | — | — | proved |
| `row3_rule`, `row7_rule` | miri Dict-7 | the press is the programmers' rule, verified per cell | N+ | exact | — | self | proved |
| `row3_not_d1At` (+ `row3_cell_straddles`) | miri I4.3 row 3 (configuration) | common prior, the agent's cell `{0, 2}` straddling `H` (incomparable with it, not finer): `1/2 > 0`, `¬ D1`, nondegenerate | N+ | variant: a straddling two-world cell in place of the script's singleton cells (`y_part = full`) | — | self | proved (relabelled at repair r1, N2) |
| `row7_not_d1At` | miri I4.3 row 7 (configuration); mandate T7(b) (numbers) | within-cell heterogeneous priors, agent trivial: `2/5 > 0`, `¬ D1`, nondegenerate | N+ | variant: the mandate's numbers on the script's configuration (its `muP2`/`muA2` differ) | — | self | proved (relabelled at repair r1, N2) |
| `row8_not_d1At` (+ `pressMass_eq_one_of_press_one_on_support`) | miri I4.3 row 8 | agent on the programmers' cell: `4/5 > 0`, `¬ D1`, `pressMass = 1` | N− | exact | — | self | proved; N− on the silence branch is structural (F-13) |
| `cellOf`, `D1FailsAt`, `Refines`, `rulePress`, `contRegion`, `alphaY` | miri I4.3; carey-everitt 2.4c | partitions as labellings; "D1 fails at `Y`"; refinement; the programmers' rule; the continue region; the induced false-press rate | D | exact / `alphaY`: variant (static reading) | — | — | proved |
| `d1FailsAt_of_refines` | carey-everitt 2.4c; §2.13(b); miri I4.3 | refinement preserves D1-failure (the violation set is monotone in information) | P | variant: static form | — | `d1FailsAt_refines_witness` | proved |
| `d1FailsAt_refines_witness` (+ `yAgent`) | miri I4.3 (row 3's data) | D1 fails at `{{0,2},{1,3}}` (cell `{0}`: `1/4 > 0`), the identity refines it, the theorem propagates the failure | N+ | exact | — | self | proved (added at repair r1, B3) |
| `not_d1FailsAt_of_coarser_common_prior` | miri Prop. 4.3 | coarser than `H` under a common prior: never fails (`also in corr-three-step-facts (008)`) | L | weaker: `≤ 0` on every cell (what D1 needs); the strict clause is the next row | — | — | proved (supporting) |
| `cellSum_neg_of_coarser_common_prior` (+ `cellSum_inter_rulePress_nonpos`) | miri Prop. 4.3 | coarser than `H` under a common prior: every `Y`-cell of positive press mass has a strictly negative press-restricted sum (the source's `< 0`) | L | exact | — | `cellSum_neg_witness` | proved (added at repair r1, N6) |
| `cellSum_neg_witness` | miri Prop. 4.3 (row 3's data) | `H = hCoarse` refines the trivial `Y`, the rule presses on `{0, 1}`, the `Y`-cell has press mass `1/2 > 0`, the theorem gives `< 0` (it is `−1`) | N+ | exact | — | self | proved (added at repair r2, adversarial N5) |
| `alphaY_falls`, `alphaY_rises` (+ `alphaY_falls_tie`, `alphaY_rises_tie`) | carey-everitt 2.4c ("`α` rises") | with `Pr` an arbitrary fixed set (the mandate's definition): `α_Y` falls `1/4 → 0` / rises `2/3 → 1` under refinement, denominators positive; the dropped cell has sum exactly `0` (a tie, named) | N+ (tie disclosed) for the definition as written | exact | — | self | **refuted** in both directions (static form; F-12); the press sets `{0}`, `{0, 1}` are not the programmers' rule for any partition (repair r2, N1/N2: the rule-press pair is `alphaY_falls_rule`, `alphaY_rises_rule`) |
| `alphaY_falls_robust`, `alphaY_rises_robust` (+ `shipped_fall_pr_not_a_rule`) | carey-everitt 2.4c ("`α` rises") | with `Pr` arbitrary: `α_Y` falls `3/4 → 1/2` / rises `1/2 → 2/3` under refinement with every cell sum nonzero at both partitions; `shipped_fall_pr_not_a_rule` records that `{0, 1, 2}` is no rule under `hCoarse`, `yThreeOne` or the discrete partition | N+ for the definition as written | exact | — | self | **refuted** in both directions, with no tie (added at repair r1, N3/N1); press sets not rules (disclosed at repair r2) |
| `alphaY_falls_rule`, `alphaY_rises_rule` (+ `XFallRule`, `XRiseRule`, `yTwoOneOne`, `yOneOneTwo`, `fallRule_press`, `riseRule_press`) | carey-everitt 2.4c ("the overseers' `α` rises as the agent exceeds them"); miri Dict-7 | with `Pr = rulePress μ X H` (the overseers' own press) and the agent refining strictly past `H` at two steps (`H ⊑ Y₁ ⊑ Y₂`, both `Refines` conjuncts in the statement): `α_Y` falls `2/3 → 1/2` (`X = (2, −1, −3, 1)`, `H = {{0,1,2},{3}}`) / rises `1/3 → 1/2` (`X = (2, −3, 2, −1)`, `H = {{0,1},{2,3}}`), every cell sum nonzero at `H`, `Y₁`, `Y₂` | N+ | exact | — | self | **refuted** in both directions under the reading closest to the source (added at repair r2, fidelity N1 / adversarial N2) |
| `alphaY_rulePress_self` | carey-everitt 2.4c; miri Dict-7 | under the rule, `α_H = 0` exactly (the press set and the continue region at `H` are disjoint): the static picture is a valley at `H`, not a monotone ramp | L | exact | — | — | proved (added at repair r2, fidelity N1) |

## T8 — earned trust (`Silence.lean`; F-10)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `w3_posterior_moves` | §2.12 (AUTHOR); causal I15.2 | `P(W \| Pr) = 18/37 ≠ 1/20` | N+ | exact | — | self | proved (the posterior is earned) |
| `channel_not_identified`, `channel_not_identified_cell` | causal I15.2 | different miss rates, same press posterior, same D1 (`q ∈ (0,1)`); cell `1/10` vs `11/20` | L / N+ | weaker: one press, not the compliance record (`corr-three-step-facts`' corr-wf13-007) | — | the cell | proved (the channel is not) |

## T9 — the negative-"VOI" anomaly (`Assumptions.lean`; F-11)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `hardButtonValue_sub_twoOptionPriorValue` | check_channel_model.py `ev`, block D | A1 + regime: hard-button value − prior value `= Δ₋` | L | exact | — | `script_cell` | proved |
| `script_neg_iff_not_d1At` | check_channel_model.out l. 7 | in the regime: the script's quantity `< 0 ↔ ¬ D1`; `voiButton2 ≥ 0` | L | weaker: the iff is proved in the regime; the script's instances are not regime-restricted (the regime is this package's hypothesis, not source-stated) | — | `script_cell` | proved (in the regime; the regime-free direction is the next row — relabelled at repair r1, B2) |
| `hardButtonValue_sub_twoOptionPriorValue_nonneg_of_d1At`, `not_d1At_of_script_neg` | check_channel_model.out l. 7 | under A1 alone (no regime): D1 ⇒ the script's quantity `≥ 0`; hence quantity `< 0` ⇒ `¬ D1` | L | exact (the direction the script observes, over every instance) | — | `script_cell` (a negative-quantity instance with `¬ D1`) | proved ("0 of 509 under trust" is a regime-free theorem; added at repair r1, B2) |
| `twoState_hardButtonValue` | none: infrastructure | on `twoState`, `hardButtonValue = max(Δ₊, 0)` | L | n/a | — | — | proved (added at repair r1) |
| `script_cell` | same; miri I9.4 | `−19/2000` versus `voiButton2 = 0` on the targeted instance, in the regime | N+ | exact | — | self | proved |

## T10 — one inequality (`Cells.lean`; F-14)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `taylor_cell`, `hudson_cell`, `byrnes_cells`, `miri_cell` | refine_check.py; hudson block A; baserate_check.py; deception.py | F3 at the critics' parameters | N+ | exact | — | self | proved (no new statement) |

## T11 — chains (`Chains.lean`; F-6)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `trust_of_cellwise_trust` | ddb-mm-authors C6 | one prior: cellwise trust in the button ⇒ trust in the button (the shadow of C6; C6 is `corr-legit-general`'s) | L | variant: the inequality, not Total Trust | — | `chain_not_transitive`'s `R`-side | proved |
| `chain_not_transitive` (+ `rStop_eq`, `chain_continue_cell_tie`, `chain_stop_cell_no_press`) | ddb.md l. 221, 274 (conjectured); C6 | distinct priors: `μ` trusts `R`'s report, `R` trusts the button, `μ` does not; full supports, both reports occur; two ties named (`R`'s continue cell sums to exactly `0`; no press in `R`'s stop cell) | N+ (ties disclosed) | variant: the threshold-inequality *shadow* of trust, not Total Trust — the finite form of the conjecture's shadow, not of the conjecture | — | self | proved (non-transitivity of the inequality shadow; the witness fails C6's first hypothesis, `chain_not_in_hull`, so C6 — Total Trust composes on one `W` — stands untouched and decides the l. 274 conjecture at the TT grade if its proof holds: F-6, M-5; reworded at repair r1, B2/B3) |
| `chain_not_in_hull` | ddb-mm-authors C6 (its proof's hull condition) | `μ ∉ CH{μ_R(·\|{0,1,2}), δ₃}` (`mass w₁ = 2·mass w₀` on the hull, `1/8 ≠ 1/2`): `μ` does not Totally Trust `R` | L (a negative certificate, not an inhabitant; regraded from N+ at repair r2, adversarial N6) | variant: the hull condition on two coordinates (sufficient for the negative verdict) | — | — | proved (added at repair r1) |
| `chain_not_transitive_robust` (+ `priorRRobust`, `priorAgentRobust`, `prChainRobust`, `rStopRobust_eq`) | ddb.md l. 221, 274; C6 | the eight conjuncts on `μ_R' = (1/8, 1/4, 1/4, 3/8)`, `μ' = (1/2, 1/8, 1/8, 1/4)`, `Pr' = {0,1,3}`, plus strict reports (`+1/8`, `−3/8`) and a press in both `R`-cells | N+ | variant: the inequality shadow, as above (the two trust hypotheses share no variable that reaches the conclusion, so the non-composition of the shadow is near-automatic; the content of T11 after repair is the hull test — audit r2, adversarial N4) | — | self | proved, no tie (added at repair r1, N1) |
| `chain_not_in_hull_robust` (+ `priorRRobust_cond_masses`) | ddb-mm-authors C6 (its proof's hull condition) | `μ' ∉ CH{μ_R'(·\|{0,1,2}) = (1/5, 2/5, 2/5, 0), δ₃}` (coordinate `w₀` forces `a = 5/2 > 1`): the robust witness fails C6's first hypothesis too | L | variant: the hull condition on one coordinate (sufficient for the negative verdict) | — | — | proved (added at repair r2, adversarial N4) |

## T12 — a structural guarantee claim (`Chains.lean`; F-9)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `not_d1At_of_dominated_on_support`, `withSensor`, `not_d1At_withSensor` | §2.3 (CLAUDE); causal I18.2; C7; miri Prop. 8.1 | a continuation dominating every shutdown action on the support ⇒ `¬ D1` for every sensor with positive press mass (`also in corr-three-step-facts (2-003)`) | P / D / L | exact | — | `domInstance_dominated_not_d1At` (full support, nondegenerate sensor; the artifact check `twoState_perfect_sensor_d1At` inhabits the hypothesis's *failure*) | proved; exhibits one every-sensor guarantee-type theorem in Setting S (Prop. 8.1's necessity direction, whose antecedent — dogmatism — is itself the atypical hypothesis) against §2.3's "none can be a structural theorem"; the structural theorems C7 and I18.2 cite are `corr-scim-cid`'s / `lit-ddb-facts`' (F-9; Status reworded at repair r2, fidelity N2) |
| `domInstance_dominated_not_d1At` (+ `domV`, `domInstance`, `domInstance_pressMass`) | miri Prop. 8.1 (necessity, one instance) | prior `(1/2, 1/2)` (both worlds positive), `V(cont) = (1, 1/2) > 0 = V(stop)` on both, honest sensor `(1/20, 9/10)`, `P(Pr) = 19/40` (`Nondegenerate`); the theorem gives `¬ D1` | N+ | exact | — | self | proved (added at repair r2, adversarial B1) |
| `twoState_dominated_not_d1At` | miri Prop. 8.1 (necessity, the degenerate instance) | `twoState 0 (1/20) (9/10) 1 20`: prior `δ_right`, so the "support" is one world, `β` is multiplied by mass `0` and the strict sum has one term; `pressMass = 1/20 > 0`; the theorem gives `¬ D1` | N− (one-world support; graded N+ at repair r1, regraded at repair r2, adversarial B1) | exact | — | self | proved (added at repair r1, B3; kept as the labelled boundary) |
| `d1At_of_pressMass_eq_zero` | filler R1 | `pressMass = 0` makes D1 vacuous (junk, named) | T | exact | — | — | proved |
| `twoState_perfect_sensor_d1At` (+ `twoState_perfect_sensor_eps_zero_junk`) | miri Prop. 8.1 | for `ε > 0` the perfect sensor restores D1 on `twoState`; at `ε = 0` it never presses (the junk end) | N+ | exact | — | self | proved (artifact check; `0 < ε` added at repair r1, N8/N4) |

## T13 — policies as value learners (`Cells.lean`; F-15)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `polV`, `polV_delta_unique` | shah C1 | under `δ_ω`, `π_ω(h)` is the unique maximiser | D / T | exact | — | — | proved |
| `condDist_singleton_mass`, `polV_cond_unique` | shah C1 | FAF's `condDist P {ω₂}` is `δ_{ω₂}`; the value change is a conditioning | L | exact | — | — | proved |

## T14 — the four cells (`Cells.lean`; F-16, F-17)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `landedValue`, `honestValue`, `resistValue`, `eStar`, `Resists`, `resists_iff` | faking-final P1, l. 54 | the one-round rule derived: `resist ↔ e < e*` (`also in corr-general-object (044)`) | D / L | exact | — | `p2_cells` | proved |
| `p2_eStar`, `p2_cells` | faking-final P2, S3–S4 | `e* = 9/20`; resist iff `e = 1/20` in both `L` columns; `{match} ∩ {G > 0} = {resist} ∩ {L = 0}` | N+ | exact | — | self | proved |

## T15 — one accounting (`Cells.lean`; F-18)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `wholeLine_threshold`, `pause_threshold`, `wholeLine_cells`, `wholeLine_threshold_tendsto` | soares-respondent N4; faking-final P1 | `(1 − ρ)/(1 + κ)`, `δ/(1 + κ)`, the cells, the catastrophe limit | L / N+ | exact | — | `wholeLine_cells` | proved |
| `signalLoss`, `stock`, `stockTerm`, `stock_eq_closed` | n4_check.py | the script's `k̂` and its closed form | D / L | exact | — | `stock_cells` | proved |
| `stock_cells` | n4_check.out | `0, 9/500, 9/20`; `1071/625, 46/5, 248/5` | N+ | exact | — | self | proved |
| `stock_monotone_h`, `stock_monotone_kappa`, `stock_eq_zero` | inventory extension flag | `k̂` monotone in `κ`; zero when both signals resist | L | exact | — | `stock_cells` | proved (did not resist) |
| `erosionGain`, `erosion_cells`, `erosionGain_pos_iff` | n4_check.py/.out; landscape 5(c) | `+7/20` at `κ = 1`, `−23/5` at `κ = 100`; positive iff `κ < 8` | D / N+ / L | exact | — | `erosion_cells` | proved (the sign reversal) |
