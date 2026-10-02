# corr-channel-voi — ledger

*One row per headline ([STANDARDS](../../STANDARDS.md) §6). Namespace prefix `Cleanroom.Corrigibility.CorrChannelVoi.` omitted. "regime" = the continue-by-default hypotheses in product form (`0 ≤ E[X]`, `0 ≤ Δ₊`, or their `twoState` closed forms), always named, never built in; "heeded" = `0 ≤ Δ₋` in product form — at the ask model literally desideratum 1 (`askModel_D1At_iff`, r2). Hyps column lists only (b)/(c); "—" means every hypothesis is (a) — in this package "(a)" for a named regime or positivity hypothesis means "named in the statement, nothing hidden" (the convention of [corr-three-step-ledger](../corr-three-step/corr-three-step-ledger.md)). Witness column names the N+/N− cell in `Witnesses.lean` (or a witness declaration elsewhere) that inhabits the row's full hypothesis package; "—" for rows whose hypotheses are trivially satisfiable (definitions, plumbing, hypothesis-free theorems). Status `proved` unless stated; the three `refuted` rows are refutations of two source sentences (F-2, F-10) and of a mandate generalisation (F-13), not of the package's own claims. No `open`, no `sorry`. Report: [corr-channel-voi-report](corr-channel-voi-report.md). Findings: [corr-channel-voi-findings](corr-channel-voi-findings.md). **Repair round 1 (2026-09-30):** Kind column regraded where audit r1 found `P` over-applied (`channel_identity_general`, `AccuracyOnly.cannot_separate`, `askModel_alphaN_zero_heeds`, `askModel_alphaN_zero_asks_iff`, `freeValue_sub_forcedValue`, `concealF_one_ge_zero_iff`, `honest_dominates_forall_iff`); N+/N− grades added to the `AccuracyOnly` inhabitants (B1); rows added for the repair's new declarations, marked "(r1)". **Repair round 2 (2026-09-30):** the T7 reading-(II) witness regraded N− (its `α = 0` kills the factor's term) and the row's N+ is now `w_readings_differ` (audit r2 adversarial B1); Kinds regraded where audit r2 found `P`/`L` over-applied (`scanValue_sub_noScanValue`, `never_scans_of_le`, `selfCheckII_voiGiven_eq` → C; `cell_fails_of_pos` → T); T14 Case B restated on Holtman's own display; rows added for the round's new declarations, marked "(r2)"; the push rows (the two readings compared as theorems) marked "(r2, push)".*

## Definitions of record (Kind D)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `trivialExp`, `perfectExp` | mandate D1 | no channel (one signal); the world revealed (`ofMap id`) | D | exact | — | — | proved |
| `expComap` | none: infrastructure | an experiment read through a relabelling of the states | D | exact | — | — | proved |
| `expProd` | mandate D2 | the conditionally independent product `k w (s,t) = k₁ w s · k₂ w t` (API request to `lit-ddb-frames`) | D | exact | — | — | proved |
| `buttonExperiment` | mandate D1 | the button of a `ThreeStep` as an experiment (`0` = press) | D | exact | — | `twoState_buttonExperiment` | proved |
| `twoMenu`, `sensorValue` | mandate D3; substitution.md l. 27 | `𝒱(k) := bayesValue μ k ![X, 0]`, *through* `lit-ddb-frames`'s `bayesValue` | D | exact (the sources' sum-of-maxima form is the theorem `sensorValue_eq_sum_max`) | — | — | proved |
| `signalGain` | mandate D3 | `∑ w, μ w · k w s · X w`, the product-form gain of a signal | D | exact | — | — | proved |
| `voiSensor`, `voiGiven` | mandate D3; substitution.md R2 items 5–6 | `VOI(k) = 𝒱(k) − max(E X, 0)`; `VOI(k₂ ∣ k₁) = 𝒱(⟨k₁, k₂⟩) − 𝒱(k₁)` | D | exact | — | — | proved |
| `worldIdx`, `twoButton` | mandate D1 | `right ↦ 0, wrong ↦ 1`; the two-state button as `binarySensor α β` relabelled | D | exact | — | — | proved |
| `influenceDefect` | legitimacy.md R3 item 2; corr-wf14-030 | `d(a) = max_ω ∣P(Pr∣a,ω) − P(Pr∣a₀,ω)∣` as a `Finset.sup'` | D | exact | (c) the reference action `a₀` is the source's modelling choice, disclosed | `w_defects` | proved |
| `AccuracyOnly` | mandate D5; legitimacy.md R3 item 1; byrnes-herd l. 203 | a predicate on experiments at a fixed prior is accuracy-only iff Blackwell-monotone | D | variant: the sources leave the phrase undefined; this is the package's reading (ATTRIBUTION-UNVETTED) | — | N+ `thresholdL` (non-constant: `w_threshold_admits_button`, `w_threshold_rejects_trivial`); N− `accuracyOnly_reflects`, `accuracyOnly_brier` (constant-true — the sources' own examples, which exercise nothing) | proved |
| `thresholdL` (r1) | audit r1 B1 (both lenses) | the value-threshold criterion `t ≤ 𝒱_μ(k)(X)` — a non-constant instance of D5 | D | n/a | — | `w_threshold_rejects_trivial`, `w_threshold_admits_button` | proved |
| `AccuracyInvariant`, `valueIs` (r1) | legitimacy.md R3 item 1; byrnes-herd l. 203 (the alternative reading, audit r1 adversarial N6) | D5′: `L` invariant under Blackwell equivalence; the exact-value criterion `𝒱(k) = v` | D | variant: the second candidate reading of the undefined phrase (ATTRIBUTION-UNVETTED) | — | `w_invariant_rejects_scan` | proved |
| `signalMass`, `posterior`, `Reflects` | mandate D5 (example 1) | `P(s)`, `P(w∣s)`, the reflection identity `∑ s P(s) P(w∣s) = μ w` | D | exact | — | — | proved |
| `postMean`, `priorBrier`, `expBrier`, `BrierImproves` | mandate D5 (example 2) | posterior mean; Brier of the prior forecast; expected Brier after the experiment; the improvement predicate | D | exact | — | `w_brier` | proved |
| `brPress`, `brainReader` | legitimacy.md R3 set-up; corr-wf14-029–031 | the four-action dictionary as `ThreeStep World (Fin 4) TwoAct` | D | exact (the scan is not a field; each theorem names the agent's information) | — | — | proved |
| `imposedValue`, `guardedValue` | legitimacy.md R3 item 4 | the agent that evaluates silence with the honest posterior whatever it did; its `{d = 0}`-guarded variant | D | exact (a wrong agent, disclosed as such) | — | `w_imposed_prefers_deceive`, `w_guarded_no_deception` | proved |
| `distrProd` | mandate D6 | the binary product of FAF `Distr`s (FAF's `Distr.prod` is over `Pt Ω`; API request) | D | exact | — | — | proved |
| `Consent`, `consentPrior`, `sunkHarm` | substitution.md R4 item 16 | the consent latent, `P(nc) = q`, the harm `d·𝟙[nc]` | D | exact | — | — | proved |
| `scanValue`, `noScanValue`, `consentModel` | substitution.md R4 item 16 | the scan's value (harm sunk in every option, channel reading `World`), the no-scan value, the augmented `ThreeStep` | D | exact | — | `w_t5_eps5` | proved |
| `askModel` | substitution.md R5 item 25; corr-wf14-041 | `twoState q α_N β_N VOI (d − VOI)` — an instance, no new structure | D | exact | — | `w_ask_q100`, `w_ask_alphaN_zero_half` | proved |
| `Reliab`, `reliabPrior`, `relPrior`, `relStakes`, `relButton` | substitution.md R7 item 29 | the 1a world `World × Reliab`, `P(comp) = e` independent, stakes and button on the world | D | exact | — | — | proved |
| `checkKernelI`, `selfCheckI` | `scan_test.py` l. 97–100; corr-wf14-042 | reading (I): sound ⇒ the world; compromised ⇒ `R` w.p. `ρ` when wrong, always when right | D | exact (the script's model) | — | `w_1a_regime` | proved |
| `checkKernelII`, `selfCheckII` | substitution.md R7 item 29 | reading (II): compromised ⇒ `R` w.p. `ρ` regardless of the world | D | exact (the prose's model) | — | `w_readingII_continues_on_Wr` | proved |
| `jointDistr`, `cellModel`, `cellOf`, `PointwiseTrust` | substitution.md R3 item 13; corr-wf14-039 | the joint of world and scan signal; `twoState` with the scan adjoined; the cell of a signal; `∀ s, (1−ε)αc·k_R(s) ≤ εβh·k_W(s)` | D | exact | — | — | proved |
| `mixDistr`, `mixModel`, `mixCell` | radical.md I18.2; `s4_press.py` | cells `i` of mass `P i` and error rate `ε_i` | D | exact | — | `w_s4_cellwise_fails` | proved |
| `freeValue`, `forcedValue` | radical.md I11.2; corr-wf13-012 | `𝒱(⟨b, k⟩)`; `∑ s max(E[X 1_{¬Pr,s}], 0)` (press forces stop) | D | exact | — | `w_forced_lt_none` | proved |
| `directCost` | 2-011(c); miri.md I11.3(b) | honest/deceived buttons with a direct press cost `κ` (A1 fails) | D | exact | — | `w_direct_cost` | proved |
| `linFamily`, `concealF` | christiano.md T1; 2-072 | the linear concealment family toward `m`; `F(κ) = 𝒱(α κ, β κ) − τ(κ)` | D | exact (the "delegitimizing to degree `κ`" clause adds nothing to `F`; F-6) | — | `w_concealment_u` | proved |
| `honestBinding`, `deceptiveBinding`, `honestAdvisory` | holtman.md C9 | Case A's two values in product form (`P = E[X 1_Pr; a⁰]`); Case B's honest value | D | exact (to the source's formulas) | (c) the value expressions are Holtman's hand-derived formulas taken as definitions, not derived from a `ThreeStep` value (audit r1 adversarial N2; disclosed in the docstrings); on `twoState` the honest side is `v + Δ₊` (`honestBinding_twoState`), = T10's `forcedValue` only when `Δ₊ ≥ 0`; `deceptiveBinding` is a third agent beside the Bayesian and `imposedValue` | `w_holtman_cell` | proved |
| `splitScan` | mandate E1 | a three-signal experiment splitting `right` | D | n/a (witness) | — | `splitScan_attains` | proved |
| `threePrior`, `threeButton` (r1) | mandate T8(c) N+ | a `Fin 3` prior `(1/2, 1/4, 1/4)` and a noisy two-cell button on it | D | n/a (witness) | — | `w_general_scan` | proved |

## T1 — value objects and two-state closed forms

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `distr_mem_stdSimplex` | mandate §Dependencies (bridge) | a FAF `Distr`'s mass is in Mathlib's simplex | L | n/a | — | — | proved |
| `sensorValue_eq_sum_max` | mandate D3; substitution.md l. 27 | `𝒱(k) = ∑ s max(gain s, 0)`, derived from `bayesValue` | P | exact | — | — | proved |
| `sensorValue_trivial`, `voiSensor_eq_sub_trivial` | mandate T1 / D3 | `𝒱(trivialExp) = max(E X, 0)`; `VOI(k) = 𝒱(k) − 𝒱(trivialExp)` | L | exact | — | — | proved |
| `sensorValue_perfect` | mandate T1 | `𝒱(perfect) = E[max(X, 0)]` | L | exact | — | — | proved |
| `twoState_buttonExperiment` | mandate D1 | the two-state button is `binarySensor α β` up to the relabelling | L | exact | — | — | proved |
| `twoState_sensorValue_button` | corr-wf14-037 items 5–6 | `𝒱(button) = max((1−ε)αc − εβh, 0) + max((1−ε)(1−α)c − ε(1−β)h, 0)` | L | exact | — | `w_t2_eps10` | proved |
| `twoState_sensorValue_trivial`, `twoState_sensorValue_perfect` | corr-wf14-037 items 5–6 | `max((1−ε)c − εh, 0)`; `(1−ε)c` (`c, h ≥ 0`) | L | exact | — | `w_forced_lt_none`, `w_perfect_attains` | proved |
| `twoState_voiSensor_button` | corr-wf14-037 item 5 | `VOI(button)` regime-free (three-max form) | L | stronger: no regime | — | `w_regime_form_fails` | proved |
| `twoState_voiButton2_eq_voiSensor` | mandate T1 (bridge) | `voiButton2 = VOI(button)` on `twoState` | L | exact | — | — | proved |
| `twoState_voiSensor_button_regime` | corr-wf14-037 item 5; wentworth §2.4; miri Prop. 10.5 | Wentworth's `(εβh − (1−ε)αc)⁺` **under** the regime (cited from `corr-three-step` through the bridge) | C | exact | — | `w_regime_form_fails` (N−: false off the regime) | proved |
| `twoOptionValue_eq_sensorValue_add` | mandate D3 (bridge) | under A1, `twoOptionValue = 𝒱(button)(X_o) + E[V(s)]` | L | exact | — | — | proved |
| `voiButton2_eq_voiSensor` | mandate D3 / T1 | under A1, `voiButton2 = VOI(button)(X_o)` on every `ThreeStep` | L | stronger: general A1, not only `twoState` | — | — | proved |

## T2 — the channel identity (load-bearing 1)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `prod_perfect_equiv`, `sensorValue_prod_perfect` | mandate D2 | `⟨k, perfect⟩` is Blackwell-equivalent to `perfect`; same value | L | n/a | — | — | proved |
| `channel_identity_general` | corr-wf14-037 items 7, 10 | `VOI(perfect ∣ k) + VOI(k) = E[max(X,0)] − max(E X, 0)` for every prior, stakes, channel — telescoping; the content is D2's equivalence `⟨k, perfect⟩ ≡ perfect` and the two closed forms | C (regraded from P, r1) | stronger: general `W`, both regimes | — | — | proved |
| `twoState_vopi` | corr-wf14-037 items 7, 10 | the two-state VOPI is `min(εh, (1−ε)c)` | L | exact | — | — | proved |
| `twoState_channel_identity` | corr-wf14-037 items 7, 10 | `VOI(scan ∣ button) + VOI(button) = min(εh, (1−ε)c)`, regime-free | C | stronger: one statement for both regimes | — | `w_t2_eps10` (`(1−ε)c` row), `w_t2_eps20` (`εh` row); `w_dead_button_identity` (N−, r2: at the constant button `α = β = 1/2` the identity reads `0 + 9/10 = 9/10`, a specific number, not `0 = 0`) | proved |
| `twoState_channel_identity_of_le` / `_of_ge` | corr-wf14-037 items 7 / 10 | `= εh` when `εh ≤ (1−ε)c`; `= (1−ε)c` otherwise | L | exact | — | `w_t2_eps20` / `w_t2_eps10_sdd` (r1: through `_of_ge`, so `(1−ε)c ≤ εh` is machine-checked at the cell) | proved |
| `twoState_voiGiven_perfect` | corr-wf14-037 item 6 | `VOI(scan ∣ button) = (1−ε)c − 𝒱(button)`, regime-free | L | exact | — | `w_t2_eps10` | proved |
| `twoState_voiGiven_heeded` | corr-wf14-037 item 6; legitimacy.md R3 item 1; armstrong claim 2 | `= (1−ε)αc + ε(1−β)h` under `Δ₋ ≥ 0 ∧ Δ₊ ≥ 0` | C | exact | — | `w_t2_eps20` (`(19/20)(1/10) + (1/20)(1/10)10 = 29/200`; r1: now computed *through* this theorem, so `Δ₋ = 71/200 ≥ 0`, `Δ₊ = 161/200 ≥ 0` are machine-checked) | proved |
| `twoState_voiGiven_discounted` | corr-wf14-037 item 6 | `= εh` under `Δ₋ ≤ 0 ∧ Δ₊ ≥ 0` (the mandate's `E[X] ≥ 0` not needed; `Δ₊ ≥ 0` needed — F-11) | C | exact (with the clause the source's `β > α` supplies) | — | `w_t2_discounted` (r1; the table's `ε = 1/100` row: `Δ₋ = −9/1000 ≤ 0`, `Δ₊ = 881/1000 ≥ 0` machine-checked, `VOI(button) = 0`, `VOI(scan ∣ button) = 1/10 = εh`) | proved |
| `deltaPlus_nonneg_of_le`, `twoState_voiGiven_discounted_of_le` | wentworth §2.4; corr-wf14-037 item 6 | under `α ≤ β`, `E[X] ≥ 0` gives `Δ₊ ≥ 0`; hence `= εh` under `Δ₋ ≤ 0 ∧ εh ≤ (1−ε)c` | L / C | exact | — | — | proved |
| `twoState_voiGiven_heeded_eq_zero_iff` | corr-wf14-037 item 6 | in the heeded regime, `VOI(scan ∣ button) = 0 ↔ α = 0 ∧ β = 1` | P | exact | — | — | proved |
| `epsStar_balance`, `epsStar_mem_Icc` | corr-wf13-004 | `(1−ε*)αc = ε*βh`; `ε* ∈ [0,1]` | L | exact | — | — | proved |
| `twoState_at_epsStar` | corr-wf14-037 item 7 (the limit sentence) | at `ε = ε*` (`α ≤ β`): `VOI(button) = 0 ∧ VOI(scan ∣ button) = ε*h`, exactly | P | stronger: exact at the point, not a limit | — | — | proved |

## T3 — every channel is worth at most the value of perfect information (load-bearing 2)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `max_signalGain_le` | none: infrastructure | per signal, `max(gain, 0) ≤ ∑ μ k max(X, 0)` | L | n/a | — | — | proved |
| `sensorValue_le_perfect_general` | corr-wf14-037 item 9; 2-011(a); wentworth §2.4 | `𝒱(k) ≤ E[max(X, 0)]` for **every** finite experiment (general `W`) | P | exact | — | — | proved |
| `voiSensor_le_vopi` | corr-wf14-037 item 9 | `VOI(k) ≤ E[max(X,0)] − max(E X, 0)` for every `k` | L | exact | — | `w_perfect_attains` (attained) | proved |
| `voiSensor_perfect` | mandate T3 N+ | the perfect experiment attains the bound | L | exact | — | `w_perfect_attains` | proved |
| `twoState_voiSensor_le_min` (r1; was inline) | corr-wf14-037 item 9; 2-011(a); wentworth §2.4 | `VOI(k) ≤ min(εh, (1−ε)c)` for every `S` and `k : Experiment World S` — the load-bearing-2 headline as one named declaration (`voiSensor_le_vopi` + `twoState_vopi`; still used inline in `never_scans_of_le`) | C | exact | — | `w_perfect_attains` (attained) | proved |

## T4 — the brain-reader as one statement (load-bearing 3)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `blackwellLE_perfect`, `binarySensor_le_perfect`, `twoButton_le_perfect` | corr-wf14-029; mandate T4(a) | every experiment is below the perfect one | L | n/a | — | — | proved |
| `blackwellLE_left_prod`, `blackwellLE_right_prod`, `twoButton_le_scanRo` | mandate D2, T4(a) | each factor is below the product | L | n/a | — | — | proved |
| `blackwellLE_trivial`, `blackwellLE_prod_trivial` | mandate D2 | `trivialExp ≤ k`; `⟨k, trivialExp⟩ ≡ k` | L | n/a | — | — | proved |
| `scanRo_sub_honest` | legitimacy.md R3 item 1; armstrong claim 2 | the read-only scanner's advantage is `VOI(perfect ∣ button)` — `rfl` (the advantage *is* `voiGiven` by definition); priced by T2 | L | exact | — | `w_t2_eps10` | proved |
| `scan_preferred_to_repair` (r1; T8(c) third clause, was inline) | armstrong l. 162; mandate T8(c) | with the perfect scan at `κ_s` and repair to any `k_r` at `κ_r`, scan weakly preferred whenever `κ_s ≤ κ_r` (T8(a) at `blackwellLE_perfect`) | L | stronger: any repair target | — | — | proved |
| `garbling_chosen_iff` (r1; T8(d), was inline) | 2-081 (S-form); mandate T8(d) | a channel-breaking `a₁` replacing `k` by a garbling `k'` and saving `σ`: the destroyed VOI `𝒱(k) − 𝒱(k')` is `≥ 0`, and `a₁` is chosen iff `σ` exceeds it | L | exact | — | — | proved |
| `voiGiven_after_perfect`, `voiGiven_button_after_perfect`, `repair_after_scan_worth` | legitimacy.md R3 item 1; miri I10.8 | after the perfect scan no channel adds value; repair at `κ` is worth `−κ` | L | exact | — | — | proved |
| `voiGiven_perfect_left` | corr-core-025; miri I10.8 | holding the perfect channel, the button adds nothing (T4(f)) | L | exact | — | — | proved |
| `brainReader_defect_deceive` / `_scanDis` / `_scanRo` | legitimacy.md R3 item 2; corr-wf14-030 | `d = max(α,β)/2`, `max(α,β)`, `0`, general in `(α, β)` | L | exact | (c) reference action | `w_defects` (`9/20, 9/10, 0`) | proved |
| `influenceDefect_eq_zero_iff` | legitimacy.md R3 item 2 | `d(a) = 0` iff the kernel is untouched | L | exact | — | — | proved |
| `AccuracyOnly.admits_prod_perfect`, `.prod_perfect_iff` | mandate T4(d) | accuracy-only `L` admitting `k` admits `⟨k, perfect⟩`; takes the same value on `⟨k, perfect⟩` and `perfect` | L | exact | — | — | proved |
| `AccuracyOnly.cannot_separate` | corr-wf14-029; 2-078 (1)–(3); legitimacy.md R3 item 1; byrnes-herd l. 203 | for every accuracy-only `L`: `L button → L ⟨button, perfect⟩`, and `L ⟨k₁, perfect⟩ ↔ L ⟨k₂, perfect⟩` — D5 applied to `blackwellLE_left_prod` and `prod_perfect_equiv`; the content is in D2 and D5 | L (regraded from P, r1) | exact, for the D5 reading | — | N+ `w_threshold_admits_scanRo`, `w_threshold_same_on_ro_dis` (on `thresholdL`, which rejects `trivialExp` and admits the button: the clauses are exercised); N− `accuracyOnly_reflects`, `accuracyOnly_brier` (constant-true: both clauses hold for them without D5, audit r1 B1) | proved |
| `thresholdL_accuracyOnly` (r1) | audit r1 B1 | the value threshold is Blackwell-monotone (T8(a)) | C | n/a | — | `w_threshold_rejects_trivial` (non-constant) | proved |
| `AccuracyOnly.invariant`, `AccuracyInvariant.prod_perfect_iff` (r1) | mandate T4(d) second sentence, under D5′ (audit r1 adversarial N6) | D5 ⟹ D5′; under D5′ clause (ii) survives: `L ⟨k₁, perfect⟩ ↔ L ⟨k₂, perfect⟩` (read-only and disabling scans still indistinguishable) | L | exact, for the D5′ reading | — | `w_invariant_rejects_scan` (`valueIs` inhabits D5′) | proved |
| `valueIs_invariant`, `valueIs_admits_rejects_scan` (r1) | mandate T4(d) first sentence, under D5′ (audit r1 adversarial N6) | the exact-value criterion is invariant; whenever `𝒱(k) < 𝒱(perfect)` it admits `k` and rejects `⟨k, perfect⟩` — clause (i) **fails** under D5′: "admitting the button admits the scan" needs the monotone reading | C | exact, for the D5′ reading | — | `w_invariant_rejects_scan` (`71/100` vs `9/10`) | proved (the two readings split the mandate's sentence along its two halves; F-4) |
| `brainReader_separation` | corr-wf14-029–030; 2-078; legitimacy.md R3 items 1–2 | on the dictionary's own buttons (`buttonExperiment (brainReader …) 0/3/2`; r1 restated): admitting the honest button admits scan·ro's information; same value on scan·ro and scan·dis; whereas `d(scan·ro) = 0 < max(α,β) = d(scan·dis)` | C | exact, for the D5 reading | — | N+ `w_threshold_brainReader` (the four-conjunct statement at the non-constant `thresholdL`), `w_defects` | proved |
| `reflects_all`, `accuracyOnly_reflects` | mandate D5; legitimacy.md R3 item 1; substitution.md R9 item 37 | every experiment reflects; hence the identity is accuracy-only | P / L | exact | — | — | proved |
| `sum_weighted_sq_postMean_le`, `expBrier_le_priorBrier`, `accuracyOnly_brier` | mandate D5 (example 2) | the posterior mean minimises the weighted quadratic; expected Brier never worsens; hence accuracy-only | P / P / L | exact | — | `w_brier` (`9/100 → 69/1730 → 0`) | proved |
| `twoButton_half_le`, `deceived_le_honest` | legitimacy.md R3 item 4; corr-wf14-031 | the halved sensor is a garbling (`inParallelogram_scale` at `1/2`); the correct Bayesian prices it below the honest one | L / C | exact | — | `w_deceived_lt_honest` (`241/400 < 161/200`) | proved |
| `imposedValue_lt_of_pressMass_lt` | legitimacy.md R3 item 4 | the imposed-trust agent strictly prefers any action lowering the press mass | L | exact | — | `w_imposed_prefers_deceive` (`60053/69200 > 161/200`) | proved |
| `guardedValue_le_self` | legitimacy.md R3 item 4 | the `{d = 0}`-guarded agent weakly disprefers any positive-defect garbling (heeded regime, A0 at the pair) | C | exact | — | `w_guarded_no_deception` (strict, proved directly); `w_guarded_through_theorem` (r2: all six hypotheses discharged *through the theorem* at `brCell`, `a₀ = 0`, `a = 1`) | proved |

## T5 — the scan decision (load-bearing 4)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `ruleValue_sub_const`, `bayesValue_sub_const` | mandate T5 ("the harm is sunk"); substitution.md R4 item 16 | a cost paid in every option and signal shifts the Bayes value by its expectation | L / P | exact | — | — | proved |
| `signalGain_comap_fst`, `sensorValue_comap_fst`, `expect_distrProd_fst` | mandate D6 | a channel reading one coordinate has the marginal's value | L | n/a | — | — | proved |
| `expect_sunkHarm` | none: infrastructure | `E[d·𝟙[nc]] = q·d` | L | n/a | — | — | proved |
| `scanValue_sub_noScanValue` | substitution.md R4 item 16; corr-wf14-040 | `E[V ∣ scan k'] − E[V ∣ no scan] = VOI(k') − VOI(button) − q·d` | C (`bayesValue_sub_const`, where the `P` lives, + `sensorValue_comap_fst` + `expect_sunkHarm` + `ring`; regraded from P, r2) | exact | — | `w_t5_eps5` | proved |
| `scans_iff` | substitution.md R4 item 16 | scans iff `q·d < VOI(k') − VOI(button)` | L | exact | — | `w_t5_scans_iff` (`q < 7/125`) | proved |
| `never_scans_of_le` | substitution.md R4 item 18; corr-wf14-040 | `εh ≤ q·d` ⟹ no channel is worth the scan (T3) | C (`scans_iff` + `voiSensor_le_vopi` + `twoState_vopi` + `voiSensor_nonneg` + `linarith`; regraded from P, r2 — now agrees with `twoState_voiSensor_le_min`'s row) | exact (the sufficient condition; the source's general form is `[conjectured]`, F-7) | — | — | proved |
| `scans_perfect_iff` | substitution.md R4 item 18 | for the perfect scan: scans iff `q·d < min(εh, (1−ε)c) − VOI(button)` | C | exact | — | `w_t5_scans_iff` | proved |
| `consentModel_belowThreshold_iff` | substitution.md R4 item 17 | compliance on the augmented model ↔ on `twoState`, for all `q, d`, under either action | L | exact | — | — | proved |

## T6 — asking before scanning (load-bearing 4)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `askModel_Xo` | mandate T6 (bridge) | the ask model's `X_o` is `twoValue VOI (d − VOI)` | L | exact | — | — | proved |
| `askModel_heeded_iff` | substitution.md R5 item 25; corr-wf14-041 | heeded iff `(1−q)α_N VOI ≤ qβ_N(d − VOI)` (`corr-three-step`'s base-rate inequality at the instance) | C | exact | — | `w_ask_q100` (fails there) | proved |
| `askModel_D1At_iff` (r2) | substitution.md R5 item 25, read as desideratum 1; audit r2 fidelity N4 | `D1At ()` at the ask model ⟺ `(1−q)α_N VOI ≤ qβ_N(d − VOI)` — the T6 rows' "heeded" is literally `corr-three-step`'s desideratum 1, not merely `0 ≤ Δ₋` | C (`d1At_iff_deltaMinus_nonneg` + `twoState_cont/stop_partBest` + `twoState_deltaMinus_nonneg_iff`) | exact | — | `w_ask_q100` (fails there) | proved |
| `askModel_heeded_iff_ratio` | substitution.md R5 item 25 | the ratio form under positivity | C | exact | — | — | proved |
| `askModel_asks_iff` | substitution.md R5 item 25 | "asks" (`0 < VOI₂`) iff `ε* < q` in the regime | C | exact | — | — | proved |
| `askModel_alphaN_zero_heeds` | substitution.md R5 item 25 ("obeys at every `q > 0`") | `α_N = 0` heeds for every `q > 0` (theorem in `q`; the press cell's sign on the closed form) | L (regraded from P, r1) | exact | — | `w_ask_alphaN_zero_fails` (heeds even at `q = 99/100`) | proved |
| `askModel_alphaN_zero_asks_iff` | substitution.md R5 item 25 ("asks at every `q > 0`") | with `α_N = 0`, asks iff `q(1−β_N)(d − VOI) < (1−q)VOI` — the universal claim is false (F-10) | C (Good's equality clause `voiSensor_pos_iff` at the instance; regraded from P, r1) | exact (the true criterion) | — | `w_ask_alphaN_zero_half` (`23/40` at `q = 1/2`), `w_ask_alphaN_zero_fails` (`0` at `q = 99/100`) | **refuted** as stated (the source's universal "asks"); true on the scan region `q·d < VOI` (`askModel_alphaN_zero_asks_of_scan_region`), false only where the agent would not scan anyway |
| `askModel_alphaN_zero_asks_of_scan_region` (r1) | substitution.md R5 items 24–25 (the scope item 24 sets up) | on the scan region `q·d < VOI`, `α_N = 0` asks at every `q > 0` — the source's sentence with the scope it needs | L | exact (the source's claim, scoped) | — | `w_ask_alphaN_zero_scan_region` (`q = 1/10`: `q·d = 1/2 < 3/2` machine-checked through the theorem; `VOI(ask) = 63/200`). `w_ask_alphaN_zero_half` (`q = 1/2`, `q·d = 5/2 > VOI`) asks *outside* the region: the region is sufficient, not necessary | proved |
| `askModel_perfect_objection_asks` | substitution.md R5 item 25 | with `β_N = 1` too, asks at every `q ∈ (0,1)` | L | exact | — | — | proved |
| `askModel_scans_regardless` | mandate T6 (trap: below `VOI ≤ d`) | if `d ≤ VOI`, scanning is press-optimal and the ask is worthless | L | exact | — | — | proved |

## T7 — the 1a discount

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `checkI_gain_R`, `checkI_gain_Wr`, `checkI_button_gain_*` | substitution.md R7 item 30 | the signal gains of reading (I): after `R` the world masses are `(1−ε) : εeρ`; the `Wr` cells are nonpositive | L | exact | — | — | proved |
| `selfCheckI_voiGiven_eq` | substitution.md R7 item 30 (regime-free form derived here) | `VOI(button ∣ check) = max(A,0) + max(B,0) − max(A+B,0)` (`h ≥ 0`) | P | stronger: regime-free | — | `w_1a_offregime` (`31/50`) | proved |
| `selfCheckI_voiGiven_closed` | substitution.md R7 item 30; miri I10.8(b); corr-wf14-042 | `= (εeρβh − (1−ε)αc)⁺` under the post-check regime in product form | C | exact | — | `w_1a_regime` (`9/25`); `w_1a_offregime` (N−: overstates off the regime, `41/50 ≠ 31/50`) | proved |
| `selfCheckI_silent_of_le`, `selfCheckI_voiGiven_closed_of_le` | substitution.md R7 item 30 | under `α ≤ β` the mandate's single hypothesis `εeρh ≤ (1−ε)c` suffices | L / C | exact | — | `w_1a_regime` | proved |
| `selfCheckI_voiGiven_pos_iff` | substitution.md R7 item 30 | positive iff `(1−ε)αc < εeρβh` | L | exact (strict form) | — | — | proved |
| `selfCheckI_stops_on_Wr` | substitution.md R7 item 30 | after `Wr` stop is optimal on both cells (reading I) | L | exact | — | — | proved |
| `checkII_gain_*`, `checkII_button_gain_*` | mandate T7 (reading II) | the signal gains of reading (II): odds `εeρ : (1−ε)(1−e+eρ)` after `R`; the `Wr` branch carries right-world mass `(1−ε)e(1−ρ)` | L | exact | — | `w_readingII_continues_on_Wr` (`6/25 > 0`) | proved |
| substitution.md R7 item 30, "after 'scan says `Wr`' the agent shuts down", under the prose's reading (II) | substitution.md l. 98–100 (F-2) | false in general: the `Wr` signal's gain is `6/25 > 0` at `(1/100, 1/2, 1/2, 1, 1)` — the agent continues after its own check says `Wr`; true unconditionally in the script's reading (I) (`selfCheckI_stops_on_Wr`) | N+ | n/a | — | `w_readingII_continues_on_Wr` | **refuted** (the source sentence, in reading (II); F-2) |
| `selfCheckII_voiGiven_eq`, `selfCheckII_voiGiven_closed` | mandate T7 (reading II); Known issue 2 | regime-free form; `R`-branch closed form with the factor `(1−e+eρ)` under four product-form conditions (the `Wr`-decisiveness ones automatic in (I), not in (II) — F-2) | C / C (`_eq` regraded from P, r2: `sensorValue_eq_sum_max` + six cell lemmas + `ring`, no sign reasoning) | exact | — | `w_readings_differ` (N+, r2: at `(1/5, 1/2, 1/2, 1/10, 1/2, 1, 5)` both closed forms hold through their theorems and give *different values*, `VOI_I = 9/200 < 13/200 = VOI_II` — `w_readingI_factor`, `w_readingII_factor`); `w_readingII_closed` (N−, regraded from N+ in r2: `1/8` at `α = 0`, where the `αc` term carrying the factor vanishes and reading (I) is also `1/8`, `w_readingI_at_alpha_zero`; audit r2 adversarial B1) | proved |
| `selfCheckII_voiGiven_pos_iff` (r2) | substitution.md R7 item 30 (reading II) | under the four conditions, `VOI_II > 0 ↔ (1−ε)(1−e+eρ)αc < εeρβh` | L | exact | — | `w_readingII_factor` | proved |
| `selfCheckI_le_selfCheckII`, `selfCheck_readings_gap` (r2, push) | mandate T7 (both readings); Known issue 2 — the natural next result | wherever both closed forms hold, reading (II) values the button at least as much as reading (I); in reading (I)'s positive part the gap is exactly `(1−ε)·e(1−ρ)·αc` — zero iff `α = 0`, `e = 0`, `ρ = 1`, `ε = 1` or `c = 0`, the complete list of where the prose and the script agree in value | C (both closed forms + `factor_term_le` + monotonicity of `max` / `ring`) | exact | — | `w_readings_gap` (`1/50` through the theorem, all seven hypotheses discharged; `w_readings_differ`) | proved |

## T8 — Blackwell monotonicity and the substitution corollaries

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `sensorValue_mono`, `voiSensor_mono` | corr-core-012/013; 2-078 (1); miri I11.2(a) | `BlackwellLE k₂ k₁ → 𝒱(k₂) ≤ 𝒱(k₁)` (and `VOI`), via `tt-finite-frames` | C / L | exact | — | `w_deceived_lt_honest` | proved |
| `sensorValue_trivial_le` | corr-core-012 | the ceteris-paribus lemma: only `k ↦ trivialExp` changes, value weakly falls | L | exact | — | — | proved |
| `voiSensor_nonneg`, `voiGiven_nonneg` | corr-wf13-012 (Good's inequality); mandate D2 | `0 ≤ VOI(k)`; `0 ≤ VOI(k₂ ∣ k₁)` | L | exact | — | — | proved |
| `scans_iff` (T8(c) first clause) | corr-core-013; 2-078 (1) | prefers scan iff `κ < VOI(k') − VOI(button)` — `scans_iff` with `q·d` read as `κ` | L | exact | — | `w_t5_scans_iff` | proved |
| `repair_after_scan_worth` (T8(c) second clause) | corr-core-013 | after a perfect scan repair at `κ_r` is worth `−κ_r` | L | exact | — | — | proved |
| `scan_preferred_to_repair` (T8(c) third clause; r1) | armstrong l. 162 | scan at `κ_s` weakly preferred to repair to any `k_r` at `κ_r` whenever `κ_s ≤ κ_r` (`sensorValue_mono` at `blackwellLE_perfect`) | L | stronger: any repair target | — | — | proved |
| `garbling_chosen_iff` (T8(d) 2-081's S-form; r1) | 2-081 | a channel-breaking `a₁` saving `σ` is chosen iff `σ >` the VOI it destroys, which is `≥ 0` under the garbling hypothesis (the iff conjunct is the definition of "chosen" rearranged — `T` on its own; the row is `L` for the first conjunct, T8(a); audit r2 adversarial N3) | L | exact | — | — | proved |
| T8(c) N+ general-`W` witness: `w_general_scan` (r1) | mandate T8 N+ | on `Fin 3` with prior `(1/2, 1/4, 1/4)`, stakes `(1, −1, −2)`, the noisy two-cell button `threeButton` (press `1/10, 1/2, 9/10`) and the noiseless scan: `VOI(perfect) = 1/2`, `VOI(button) = 11/40`, scan strictly preferred at every `κ < 9/40` | N+ | exact | — | itself (`w_t2_eps10` is the two-state cell) | proved |

## T9 — pointwise trust after a scan; cellwise vs averaged; the confidence ball (load-bearing 5)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `obsExpect_press_eq_sum_cells`, `belowThresholdIneq_of_cells` | substitution.md R3 item 12; radical I18.2 | the aggregate is the sum of the cells; cellwise ⟹ aggregate | L | exact | — | `w_s4_cellwise_fails` (converse fails) | proved |
| `cellModel_pressExpectOn`, `cellModel_pressExpectOn_eq_signalGain` | substitution.md R3 item 13; `scan_test.py` §R3' | the cell inequality on the joint model is `(1−ε)αc·k_R(s) − εβh·k_W(s)`, = the press-cell's gain in `⟨button, k⟩` | L | exact | — | — | proved |
| `cellModel_aggregate` | radical I18.2; corr-wf14-039 | adjoining a conditionally independent scan leaves `E[X 1_Pr]` unchanged | L | exact | — | — | proved |
| `pointwiseTrust_iff_cells` | substitution.md R3 item 13; corr-wf13-013 | pointwise trust ⟺ the cell inequality (`corr-three-step`'s `pressExpectOn ≤ 0`) on every cell | L | exact | — | — | proved |
| `pointwiseTrust_iff_ratio` | substitution.md R3 item 13 | the ratio form under positivity (`∀ s` for `min_s`) | L | exact | — | — | proved |
| `pointwiseTrust_perfect_iff` | substitution.md R3 items 13–14 | for the perfect scan, pointwise trust ⟺ `α = 0` | P | exact | — | — | proved |
| `mixModel_cell`, `mixModel_aggregate`, `mixModel_aggregate_eq_twoState`, `mean_eps_mem` | radical I18.2; `s4_press.py` | cell `i`'s inequality is `P i((1−ε_i)αc − ε_iβh)`; the aggregate is `twoState`'s at `ε̄` (a refinement leaves it unchanged) | L | exact | — | `w_s4_cellwise_fails` (`−7/40` vs `1/40`), `w_s4_refinement` (`−3/20` unchanged, cell `1/36 > 0`) | proved |
| `cell_fails_of_pos` | 2-086; anthropic-davis §2.2 items 6–7 | the confidence ball: a positive press-cell is one where desideratum 1 fails (the reachable form; F-14 — the package's output on 2-086 is the finding, not this theorem) | T (modus tollens; regraded from L, r2) | exact | — | `w_s4_cellwise_fails` | proved |

## T10 — free versus forced channel

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `freeValue_sub_forcedValue` | radical I11.2; corr-wf13-012 | `V_free − V_forced = ∑ s max(E[X 1_{Pr,s}], 0)` (`sensorValue_eq_sum_max` with the `Fin 2 × S` split) | C (regraded from P, r1) | exact | — | `w_forced_lt_none` | proved |
| `forcedValue_le_freeValue` | radical I11.2 | `V_forced ≤ V_free` | L | exact | — | — | proved |
| `freeValue_eq_forcedValue_iff` | radical I11.2 ("vanishing iff (TT) in every cell") | equality iff the cell inequality holds on every press-cell | P | exact | — | — | proved |
| `twoState_forcedValue` | radical I11.2; `s4` single-cell rows | on `twoState` (trivial partition): `V_forced = max(Δ₊, 0)`, `V_free = 𝒱(button)` | L | exact | — | `w_forced_lt_none` (`17/20 < 9/10`: an incentive `1/20` to disable) | proved |
| `sensorValue_trivial_le` (Good, free channel) | radical I11 | `𝒱(trivialExp) ≤ 𝒱(k)` | L | exact | — | — | proved |
| `sum_max_eq_max_sum_iff`, `voiSensor_eq_zero_iff`, `voiSensor_pos_iff` | radical I11 (Good's equality clause) | `VOI(k) = 0` iff one act is optimal on every signal (null signals automatic) | P | exact (finite form) | — | `w_ask_q100` (all gains ≥ 0 ⟹ `VOI = 0`) | proved |

## T11 — the value decomposition

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `value_eq_priorMax_add_voi` | 2-011 / miri I11.1 | `E[V] = priorMax + VOI` — the definition rearranged | **T** | exact | — | — | proved (labelled T, as the mandate asks) |
| "depends on the sensor only through VOI" | 2-011 | = T8(a) `sensorValue_mono` | C | exact | — | — | not stated separately; = `sensorValue_mono` |
| `directCost_not_A1`, `directCost_deceived_le`, `directCost_twoOptionValue` | 2-011(c); miri I11.3(b) | A1 fails; the deceived button is a garbling; the value is the A1 value minus `κ·P(Pr)` (the direct term) | L | exact | — | `w_direct_cost` (`133/400 > 53/200`: prefers the garbling) | proved |

## T12 — D1 and D4 stand or fall together; the inverted sensor; the successor form

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `voiButton2_eq_zero_iff`, `voiButton2_pos_iff` | corr-wf13-006 / miri Prop. 10.5 (general clause) | under A1, `0 < VOI₂` iff no act is optimal on both observations | C / L | exact (two-option menu) | — | `w_inverted` | proved |
| `twoState_voiButton2_pos_iff_both` | miri Prop. 10.5 (C2 clause, `β ≥ α`) | on `twoState` with `α ≤ β`: `0 < VOI₂ ↔ 0 < Δ₋ ∧ 0 < Δ₊` | P | exact | — | — | proved |
| `beta_lt_alpha_of_inverted` | miri I10.6 | `Δ₋ < 0 ∧ Δ₊ < 0 → β < α` (`c, h ≥ 0`) | P | weaker: implication (the "iff" is false; F-3) | — | `w_inverted` | proved |
| `inverted_exists` | miri I10.6 (68 grid points) | for every `β < α` some `(ε, c, h)` realises the inverted case | N+ | exact | — | itself | proved |
| `twoState_cont_partBest`, `twoState_stop_partBest`, `inverted_voi_pos_not_d1` | miri I10.6 | in the inverted case `VOI₂ > 0 ∧ ¬ D1At` | L / C | exact | — | `w_inverted` | proved |
| `parent_prefers_compliant_iff` | 2-085; holtman C13 | the parent prefers the compliant successor iff `0 ≤ Δ₋` (`jointExpect_shPolicy_sub_cont` re-read) | L | exact (two-successor menu) | — | — | proved |
| `d1At_iff_parent_prefers_compliant` | harms item 26; 2-085 | D1 ⟺ that preference (Harms 26 in the dictionary) | L | exact | — | — | proved |

## T13 — the concealment axis

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `inParallelogram_mix`, `inParallelogram_self`, `linFamily_mem`, `linFamily_chain` | christiano T1; mandate T13 | the parallelogram is convex; the linear family toward `m` is a garbling chain | L / P | exact | — | — | proved |
| `concealF_sensor_antitone` | christiano T1; 2-072 | the sensor term is antitone along a chain (T8(a)) | C | exact | — | `w_concealment_u` | proved |
| `sensorValue_const_button` | mandate T13 | a constant sensor is worth `trivialExp` | L | exact | — | — | proved |
| `concealF_one_ge_zero_iff` | christiano T1 | `F 1 ≥ F 0 ↔ τ ≥ VOI(button₀)` (both cost readings; under the one structural hypothesis that the fully concealed sensor is constant, `β 1 = α 1`; `sensorValue_const_button` plus the definition) | L (regraded from P, r1) | exact | — | `w_concealment_u` | proved |
| `concealF_one_sub_zero`, `concealF_zero_lt_one_iff` (r2) | christiano T1 (the strict form); 2-072; audit r2 fidelity N3 | `F 1 − F 0 = τ − VOI(button₀)` exactly; hence `F 0 < F 1 ↔ VOI(button₀) < τ` — the strict, domain-independent endpoint comparison, what `concealF_not_antitone`'s proof establishes | L | exact | — | `w_concealment_u` (`F(0) = −1/25 < F(1) = 0` with `VOI(button₀) = 71/100 < 3/4 = τ`) | proved |
| `concealF_not_antitone` | christiano T1 (the conjecture); 2-072 | for every prior, stakes, family, cost with `τ > VOI(button₀)`: `F` not antitone — corollary of the strict form (`Antitone` over all of `ℝ` is the weaker reading; cite `concealF_zero_lt_one_iff`) | L | variant: universality over the parameters in place of "no assumption" (F-6); weaker than the strict form | — | `w_concealment_u` (`F(1/2) < F(0) < F(1)`) | proved |

## T14 — Holtman C9

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `deception_pays_iff` | holtman C9 (Case A) | deception pays iff `qm + δ < E[X 1_Pr; a⁰]` | L | exact | (c) over Holtman's value expressions taken as stated (see the definitions row) | `w_holtman_cell` | proved |
| `pos_of_deception_pays` | holtman C9 | deception paying ⟹ the below-threshold inequality fails | L | exact | (c) as above | — | proved |
| `honest_dominates_of_nonpos` | holtman C9 | the inequality ⟹ honesty dominates for all `q, δ ≥ 0` | L | exact | (c) as above | — | proved |
| `honest_dominates_forall_iff` | holtman C9; corr-wf13-018 | the iff holds over the family `(q, δ)`, not at a fixed pair (F-5); the forward direction is the instance `q = δ = 0` | L (regraded from P, r1) | exact (the universal form) | (c) as above | `w_holtman_fixed_fails` (N−: converse fails at fixed `(q, δ)`) | proved |
| `deceptiveAdvisory` (r2) | holtman C9 (Case B, second display) | the advisory deceiver's value `v + m − δ` (it continues always; no `q`) | D | exact | (c) Holtman's expression taken as stated | — | — |
| `honest_advisory_dominates` (restated r2) | holtman C9 (Case B) | Holtman's display: `v + m − δ ≤ v + max(m, Q)` for every `δ ≥ 0` (`p`, `q` do not enter) — "D2 because D1 is hollow" | L | exact (the source's display; the r1 form compared against Case A's *binding* deceiver, with `q` idle — audit r2 adversarial N4) | (c) as above | — | proved |
| `honest_advisory_dominates_binding`, `deceptiveBinding_zero` (r2) | holtman C9 (Case B) | the r1 form kept as a corollary: for `m ≥ 0`, honesty with an advisory press also beats the binding deceiver's `v + (1−q)m − δ` at every `q ∈ [0, 1]` | L | weaker: compares against Case A's deceiver, `q` idle | (c) as above | — | proved |
| `holtman_on_twoState` | holtman C9–C10 | `P = −Δ₋`, `m = (1−ε)c − εh`, `E[X 1_¬Pr] = Δ₊` on `twoState` (the *quantities*, not the values) | L | exact | — | `w_holtman_cell` (`2/25`, `2/7`, `18/25`, `4/5 − δ`) | proved |
| `honestBinding_twoState` (r1) | holtman C9 (Case A) on `twoState`; audit r1 adversarial N2 | the honest binding value is `v + Δ₊` — the silence cell's expectation whatever its sign; equals T10's `forcedValue = max(Δ₊, 0)` iff `Δ₊ ≥ 0` (Holtman's honest agent continues on silence by fiat) | L | exact | — | — | proved |

## E1 — the channel bound made tight

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `max_sub_eq_self_iff`, `twoState_signalGain_eq` | mandate E1 | per-signal steps | L | n/a | — | — | proved |
| `twoState_attains_iff` | mandate E1 | `𝒱(k) = (1−ε)c` iff every signal is supported in one world | P | exact | — | `splitScan_attains` | proved |
| `twoState_voi_attains_iff` | mandate E1 | `VOI(k) = min(εh, (1−ε)c)` iff `𝒱(k) = (1−ε)c` | L | exact | — | `w_perfect_attains` | proved |
| `twoButton_attains_iff` | mandate E1 (corollary) | a binary sensor attains it iff `(0,1)` or `(1,0)` (F-12) | P | stronger: the inverted perfect sensor included | — | — | proved |
| `splitScan_attains` | mandate E1 (corollary) | a three-signal split of `right` attains it | N+ | n/a | — | itself | proved |

## Stretch and the mandate's generalisations

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| S1 option value | 2-080 | `E[X] + VOI(E)` with `VOI(E) ≥ 0` — this *is* `voiSensor_nonneg` | L | exact | — | — | proved (as `voiSensor_nonneg`) |
| S2 the successor menu | 2-079; soares T3 | **not attempted** (see report) | — | — | — | — | not attempted |
| S3 the third time index | 043 | **not attempted**; the well-posed version's needs are F-8 | — | — | — | — | not attempted (finding filed) |
| S4 (a),(d) with any `k' ≥ button` | corr-core-013 | (a) is the hypothesis; (d) is `AccuracyOnly` applied to `BlackwellLE button k'` | L | exact | — | — | not stated as declarations; consequences of D5 and the hypothesis (r1: status renamed from "proved (inline)") |
| S4 (b) with any `k' ≥ button` | corr-core-013; miri I10.8 | **false**: `VOI(button ∣ k') = 0` needs the perfect scan (F-13) | N+ | n/a | — | `w_second_button_worth` (`9/1000 > 0`) | **refuted** (the generalisation) |
