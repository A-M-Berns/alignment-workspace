# corr-three-step — ledger

*One row per headline ([STANDARDS](../../STANDARDS.md) §6). Namespace prefix `Cleanroom.Found.CorrThreeStep.` omitted; `ThreeStep.`-namespaced declarations take `S : ThreeStep Ω A₁ A₂`. "regime" = the continue-by-default hypotheses `0 ≤ E_μ[X]` and `0 ≤ Δ₊`, always named, never built in. Hyps column lists only (b)/(c); "—" means every hypothesis is (a). Witness column names the N+ instance in `Witnesses.lean` that inhabits the row's full hypothesis package. Status `proved` throughout; no `open`, no `refuted` (the one wrong number was in the mandate, finding F-1, and is corrected here, not refuted against a source). Repair round 1 (2026-09-29): the T6(a) Witness cells now name the two-button instance `buttonFamily` (`w6a_*`); the T13 row names `w13_voiButton`; Kinds relabelled per the audits (`hardButton_sub_disabled` P→C, Theorem 9 forms P→L, `epsStar_half_lt` P→L, `voiButton_eq_max_deltaMinus` P→L); `value_two_option_iff_delta_nonneg` renamed `shPolicy_beats_constants_iff_delta_nonneg` and `legitFrac`/`…_legit*` renamed `pressFracOn`/`…_event_*`; new rows in the "Repair round 1 additions" table. **Hyps convention:** source-stated *assumptions of the setting* (A0 at the pair, A1, the regime, the part-maximiser predicates) are graded (a) because every theorem quantifies over them as named hypotheses rather than assuming them of a fixed object; (a) there means "named in the statement, nothing hidden", not "derived here". Repair round 2 (2026-09-30): the source's full-menu "`Δ ≤ VOI` in general" (filler F4(c), mandate T6(c)) is **refuted** (`s3_voiButton_lt_delta`, finding F-13), so the T6 row for `delta_le_voiButton2` is now `weaker` (two-option menu) and the corrected full-menu forms are in the "Repair round 2 additions" table; Kinds relabelled (`voiButton2_eq_max_deltaMinus` P→C, `voiButton2_eq_max_delta_add` P→C, `twoState_regime_of_threshold` P→C, `twoState_expect_allow_eq_deltaPlus` C→L); Fidelity `stronger` on `d1At_iff_forall_cont` and the event-threshold form; Witness cells filled for `D1At`, `Nondegenerate`, T10 and the signal-mass bound. Status now includes one `refuted` (the source's claim; the package's two-option theorem stands).*

## Definitions of record (Kind D)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `expect` | none: infrastructure | `E_μ[X] = ∑ μ(ω) X(ω)` on FAF's `Distr` (API request) | D | n/a | — | — | proved |
| `ThreeStep` | filler.md R1; miri.md Dict-1/3/5 | Setting S: `Sh` nonempty proper, prior `μ a₁`, sensor `press a₁ ω ∈ [0,1]`, value `V` | D | exact | — | `twoState`, `ce3` | proved |
| `ThreeStep.obsExpect` | filler.md R1, F2 | product-form `E_P[X 1_o ; a₁]` | D | exact | — | — | proved |
| `ThreeStep.belowThresholdIneq` | position statement §2.9; miri.md Dict-4 | `∑ μ·press·X ≤ 0` (the corpus's below-threshold Total Trust inequality at 0) | D | exact (denominator-free) | — | `w3_*`, `ce3_single_ineq` | proved |
| `ThreeStep.aboveThresholdIneq` | position statement §2.9 | `0 ≤ ∑ μ·(1 − press)·X`; vacuous at `pressMass = 1` (docstring; the silence twin of the `pressMass = 0` vacuity) | D | exact | — | `w3_both_strict`; the vacuity disclosed by `twoState_aboveThresholdIneq_of_press_one` (N−) | proved |
| `ThreeStep.PosteriorOptimalAt` | miri.md Dict-2 | `b` maximises `E_P[V(b) 1_o]`; vacuous at mass 0 (docstring) | D | exact | — | — | proved |
| `ThreeStep.IsPartBest` | filler.md R1; miri.md Dict-3 | `b ∈ T` and `o`-optimal within `T` | D | exact | — | `ce3_null_partBest` | proved |
| `ThreeStep.D1At` | position statement §2.8 | some `b ∈ Sh` is press-posterior-optimal | D | exact | — | `w3_d1At` (success side, T3's instance), `ce3_not_d1` (failure side), `s3_d1` (success on a three-action menu) | proved |
| `ThreeStep.Xo`, `deltaMinus`, `deltaPlus`, `delta` | filler.md F2 | `X_o = V(c) − V(s)`; `Δ₋ = −E[X_Pr 1_Pr]`; `Δ₊ = E[X_¬Pr 1_¬Pr]`; `Δ = min` | D | exact | — | `w3_deltaMinus`, `w3_deltaPlus` | proved |
| `ThreeStep.shPolicy`, `constPolicy` | filler.md F2 | `S^H` and the constant strategies as payoffs | D | exact | — | — | proved |
| `ThreeStep.osgDelta` | Hadfield-Menell 2017 Eq. 1 | `E[π^H U] − max(E U, 0)`, `π^H` a function of `ω` | D | variant: `π^H(ω)` vs the paper's `π^H(U_a)` (the theorem row below is exact w.r.t. filler F2(iii), which already generalises to `π^H(ω)`) | — | — | proved |
| `ThreeStep.Nondegenerate` | filler.md R1 | `0 < pressMass < 1`, a name of record; `thresholdIneqs_iff_condExp_of_nondegenerate` routes both conditional forms through it | D | exact | — | `w3_nondegenerate` (T3's instance, `pressMass = 37/400`), `buttonFamily_disabled_not_nondegenerate` (every disabled button violates it) | proved |
| `ThreeStep.voiButton` | filler.md F4(b); miri.md Prop. 10.5 | full-menu VOI, product form, no regime | D | exact | — | `ce3_voiButton` | proved |
| `ThreeStep.twoOptionValue`, `hardButtonValue`, `voiButton2` | filler.md F4 | two-option informed value; hard-button value (press forces `s`, best response on silence — the mandate's `jointExpect a (S^H)` under `Δ₊ ≥ 0`, `hardButtonValue_eq_jointExpect_shPolicy`); two-option VOI | D | variant (hard button as a value expression; best-responds on silence where the mandate continues by fiat, report deviation 7) | (c) the forcing is the expression | `w10_voiButton2`, `w6a_values` | proved |
| `twoState` | miri.md Dict-6; §2.13(b) | C2 on FAF's `Distr` with `mass wrong = ε` | D | exact | — | `w3_*` | proved |
| `complianceThreshold`, `epsStar` | §2.13(a); channel-final.md D13 | `c/(c+h)`; `αc/(αc+βh)` | D | exact | — | `w_epsStar`, `w12_cells` | proved |
| `Thresholds.ThreeStep.pressFracOn`, `harmOn`, `gainOn` | general-object-final.md D10 | `ℓ = P(L ∣ Pr)`, `h_L`, `c_L` (derived, junk-guarded; `pressFracOn` was `legitFrac` — renamed in repair round 1, `L` is an abstract event) | D | exact under positivity | — | — | proved |
| `OSG.posMass`, `negMass`, `ePlus`, `eMinus`, `allowProb`, `expr4` | Wängberg 2017 §3 | the five statistics, the two-type human, expression (4) | D | exact | — | `w4_stats` | proved |

## T1 — F1

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `ThreeStep.d1At_iff_belowThresholdIneq` | corr-wf14-002 / filler.md F1; miri.md I9.2 | for every press-part-maximiser pair: D1 ⟺ below-threshold on `X_Pr` | L | exact | — | `ce3` (`Shᶜ = {p1, p2, p3}`, `p2` press-best while `p1` is prior-best — the only instance where "for every pair" is exercised); `w3_deltaMinus` (via T2(iv)) | proved |
| `ThreeStep.exists_partBest_pair` | filler.md F1 | a part-maximiser pair exists | L | exact | — | — | proved |

## T2 — F2

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `ThreeStep.jointExpect_shPolicy_sub_cont` / `_sub_stop` | corr-wf14-003 / filler.md F2(i) | `E[V(S^H)] − E[V(c)] = Δ₋`, `E[V(S^H)] − E[V(s)] = Δ₊` | L | exact | — | `w3_*` | proved |
| `ThreeStep.shPolicy_beats_constants_iff_delta_nonneg` (was `value_two_option_iff_delta_nonneg`) | filler.md F2(ii); mm.md I9.2 | `S^H` weakly beats both constants (DDB/MM "Value" on `{c, s}`) ⟺ `Δ ≥ 0` | L | exact | — | `w3_both_strict` | proved |
| `ThreeStep.delta_nonneg_iff_pair` | filler.md F2(ii) | `Δ ≥ 0` ⟺ below ∧ above | L | exact | — | `w3_both_strict` | proved |
| `ThreeStep.osgDelta_eq_delta` | filler.md F2(iii); HM Eq. 1 | under A1, HM's Eq. 1 quantity is `Δ` | L | exact w.r.t. filler F2(iii) (already `π^H(ω)`); HM's `π^H(U_a)` is its special case | — (A1 is a named assumption, (a)) | `w3_*` | proved |
| `ThreeStep.d1At_iff_deltaMinus_nonneg` | filler.md F2(iv) | for the part-best pair, D1 ⟺ `Δ₋ ≥ 0` | L | exact | — | `w361`/`w362` flip | proved |

## T3 — F3

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `twoState_deltaMinus_nonneg_iff` | corr-wf14-004 / filler.md F3 | `Δ₋ ≥ 0 ⟺ (1−ε)αc ≤ εβh` | L | exact | — | `w3_deltaMinus`, `w361`, `w362` | proved |
| `twoState_deltaMinus_nonneg_iff_odds` (+ `_pos_iff_odds`) | filler.md F3; miri.md I13.1; §2.13(b) | `⟺ α/β ≤ (ε/(1−ε))(h/c)` under `ε<1, 0<β, 0<c` | L | exact (finding F-2: "≲" is "≤") | — | same | proved |
| `twoState_deltaMinus_nonneg_iff_threshold` / `_iff_posterior` | filler.md F3; miri.md I12.1 | `⟺ c/(c+h) ≤ P(wrong∣Pr)`, the posterior being `posteriorPress`'s weight | L | exact | — | same | proved |
| `twoState_deltaPlus_nonneg_iff_odds` | filler.md F3; mm.md I13.4 | `Δ₊ ≥ 0 ⟺ (ε/(1−ε))(h/c) ≤ (1−α)/(1−β)` under `β<1` | L | exact | — | `w3_deltaPlus` | proved |
| `twoState_alpha_le_beta_of_both` | filler.md F3; detection.md K1–K3 | both halves ⟹ `α ≤ β` (`0<ε<1`, `c,h>0`) | P | stronger (on the closed intervals `α, β ∈ [0,1]`; K3 says `(0,1)`) | — | `w3_*` (`1/20 ≤ 9/10`) | proved |

## T4 — Wängberg Theorem 9 / Corollary 10

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `OSG.expect_eq_stats` | Wängberg Thm 9 | `E[U∣a] = p⁺e⁺ + p⁻e⁻` from the semantics | L (was P; a sum split by the sign of `U`) | exact | — | `w4_stats` | proved |
| `OSG.expect_allow_eq_stats` | Wängberg Thm 9 | `E[U∣w(a)] = p⁺p_r⁺e⁺ + p⁻(1−p_r⁻)e⁻` from the two-type human | L (was P) | exact | — | `w4_stats` | proved |
| `OSG.expr4_eq`, `OSG.prefer_a_iff` | Wängberg Cor. 10 | `(4) = E[U∣a] − E[U∣w(a)]`; `a ≻ w(a) ⟺ 0 < (4)` | L | exact | — | `w4_expr4` | proved |
| `twoState_expr4`, `twoState_prefer_a_iff` | filler.md F3 (mapping, ATTRIBUTION-UNVETTED) | on `twoState`, `(4) = −Δ₋`; `a ≻ w(a) ⟺ Δ₋ < 0` | C | variant (the mapping is `filler`'s) | — | `w4_expr4 = −341/400` | proved |
| `twoState_expect_allow_eq_deltaPlus` | filler.md F3 last sentence | Theorem 9's `E[U∣w(a)]` is `Δ₊` | L (was C; `twoState_allowProb` + `Xo_eq_of_A1` + one `sum_congr`; relabelled in repair round 2) | variant | — | `w3_deltaPlus` | proved |

## T5 — compliance threshold

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `complianceThreshold_iff` (+ `_lt_iff`) | corr-wf13-002 / §2.13(a); miri.md I12.1 | `q(−h) + (1−q)c ≤ 0 ⟺ c/(c+h) ≤ q` for `0 < c+h` | L | stronger (hypothesis weakened) | — | `w3` via `_iff_posterior` | proved |

## T6 — F4

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `ThreeStep.hardButton_sub_disabled` | corr-wf14-005 / filler.md F4(a) | hard-button value − disabled-button value `= Δ₋ + κ` in the regime | C (was P: linearity, tower, two `max` resolutions) | variant | (c) `hoff`, `hcost`, `hardButtonValue`, `twoOptionValue` model the two buttons; `hμ` is A0 at the pair | `w6a_identity` on `buttonFamily` (`A₁ = Option ℝ`, `hμ`/`hoff`/`hcost` by `rfl`, regime by `norm_num`; `= 161/400 + κ`), `w6a_values` (sides `341/400` and `9/20 − κ`) | proved |
| `ThreeStep.jointExpect_shPolicy_sub_disabled` (new, repair round 1) | filler.md F4(a) (the mandate's shape) | with the hard button valued as `jointExpect aDir (S^H)`: `= Δ₋ + κ` under `hprior` alone (no `hsilent`) | C | variant (mandate's value expression) | as above | `w6a_jointExpect_shPolicy` (`= 341/400`) | proved |
| `ThreeStep.hardButtonValue_eq_jointExpect_shPolicy` (new) | filler.md F4(a) | `hardButtonValue = jointExpect a (S^H)` under `Δ₊ ≥ 0` (the two shapes agree where continuing on silence is optimal) | L | exact | — | `w6a_jointExpect_shPolicy` | proved |
| `ThreeStep.disables_iff_deltaMinus_lt` | filler.md F4(a) | disables ⟺ `Δ₋ < −κ` | L | exact given (a) | as above | `w6a_disables` (`ε = 1/362`, `κ = 1/10000`: strict preference for the disabled button) | proved |
| `ThreeStep.d2_hard_forall_cost_iff_d1` | filler.md F4(a) | D2 at every cost ⟺ `Δ₋ ≥ 0` ⟺ D1 (the family `aDet : ℝ → A₁` needs an infinite `A₁`; on a finite one use `disables_iff_deltaMinus_lt` per `κ` with `forall_pos_neg_le_iff`) | C | exact given (a) | as above | `w6a_d2_holds` (`h = 10`, family `some : ℝ → Option ℝ`), `w6a_d2_fails` (`ε = 1/362`) | proved |
| `ThreeStep.voiButton2_eq` | filler.md F4(b),(c) (derived here) | `VOI₂ = max(−Δ₋,0) + max(Δ₊,0) − max(Δ₊−Δ₋,0)` under A1 alone | P | stronger (regime-free) | — | `w3_voiButton2 = 321/400` (outside the regime) | proved |
| `ThreeStep.voiButton2_eq_max_deltaMinus` | filler.md F4(b); miri.md Prop. 10.5 | in the regime `VOI₂ = max(Δ₋, 0)` | C (was P; `voiButton2_eq` + two `max` resolutions + a sign split; relabelled in repair round 2 — the real argument is `voiButton2_eq`) | exact | — | `w10_voiButton2 = 161/400`, `w362_voiButton2 = 0` | proved |
| `ThreeStep.delta_le_voiButton2`, `voiButton2_nonneg` | filler.md F4(c); mandate T6(c) | `Δ ≤ VOI₂`, `0 ≤ VOI₂` under A1 — on the **two-option** menu | L | weaker: two-option menu (`VOI₂` for the source's full-menu `VOI`); the full-menu claim is **false** (`s3_voiButton_lt_delta`, finding F-13); the corrected full-menu forms are `delta_le_voiButton_of_prior_best_sh` / `_of_singleton_sh` (repair round 2 additions) | — | `w3_voiButton2` (`Δ = 321/400 ≤ 321/400`), `s3_voiButton2` (`= 1 = Δ`, tight) | proved (two-option); the source's full-menu claim `refuted` |
| `ThreeStep.voiButton_nonneg`, `voiButton_eq_voiButton2` | filler.md F4(c), second half (Prop. 10.5's strict-positivity iff is not formalized) | full-menu `0 ≤ VOI`; `VOI = VOI₂` on a two-option menu | L | exact | — | `twoState_voiButton_eq` | proved |

## T7 — `ε*`

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `twoState_deltaMinus_nonneg_iff_epsStar` (+ `_pos_`) | corr-wf13-004; channel-final.md P10 | `Δ₋ ≥ 0 ⟺ ε* ≤ ε` for `0 < αc+βh` | L | exact | — | `w_epsStar = 1/361` | proved |
| `epsStar_eq_ratio` | channel-final.md D13 | `ε* = r/(1+r)`, `r = (α/β)(c/h)` | L | exact | — | `w_epsStar` | proved |
| `twoState_voiButton2_pos_iff_epsStar` | miri.md Prop. 10.5; hudson I12–I13 | in the regime `0 < VOI₂ ⟺ ε* < ε` | C | variant (the regime in place of Prop. 10.5's `β ≥ α`; they agree where both apply) | — | `w10` / `w362` | proved |

## T8 — Wentworth §2.4

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `twoState_regime_of_threshold` | corr-wf13-2-066 / wentworth.md §2.4 | `ε ≤ c/(c+h)` ∧ `α ≤ β` ⟹ regime | C (was P; two monotone multiplications and `linarith` on the closed forms; relabelled in repair round 2) | stronger (Wentworth's strict `<` weakened to `≤`) | — | `w10` | proved |
| `wentworth_voi_eq_deltaMinus` | wentworth.md §2.4 | his "VOI" `= Δ₋` (signed; finding F-4) | L | exact | — | `w362` (negative) | proved |
| `twoState_deltaMinus_le`, `eps_beta_h_le`, `twoState_voiButton2_le` | wentworth.md §2.4(b) | `Δ₋ ≤ εβh ≤ εh`; `VOI₂ ≤ εh` in the regime | L | exact | — | `w10` (`161/400 ≤ 9/20`) | proved |

## T9 — per-`Q` rule, restricted

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Thresholds.ThreeStep.condExpPress_eq_event_split` (was `…_legit_split`) | corr-wf14b-005 / general-object-final.md S3(b) | `E[X∣Pr] = −ℓh_L + (1−ℓ)c_L` (the two masses on `L`, `Lᶜ` positive; `0 < pressMass` derived, no longer a hypothesis) | L | exact (restricted to Setting S) | — | not a headline per source; no witness | proved |
| `…belowThresholdIneq_iff_event_split`, `_iff_event_threshold`, `…_of_gain_nonpos` (were `…_legit*`) | general-object-final.md S3(b) | rule `(1−ℓ)c_L ≤ ℓh_L`; `c_L/(c_L+h_L) ≤ ℓ`; degenerate branch | L | exact for the rule and the degenerate branch; **stronger** for the threshold form: `0 < c_L + h_L` in place of the source's `c_L > 0` with S3(a)'s `h_L ≥ 0` (not assumed here; under `c_L > 0` alone the form is false when `h_L < −c_L`) | — | — | proved |
| `twoState_deltaMinus_nonneg_scale_iff` | corr-wf14b-005(d) / legitimacy-general-final.md Stmt 4(d), X2 ("homogeneous of degree zero") | sign of `Δ₋` invariant under `(c,h) ↦ (λc, λh)` | L | exact | — | — | proved |
| `twoState_band_iff` | corr-wf14b-005(d) / legitimacy-general-final.md Stmt 4(d), Y2 (the "live band"; not in general-object-final S3/D10 — pointer corrected in repair round 1) | band `((1−ε)/ε)(α/β) < h/c < (1−ε)/ε ⟺ 0 < Δ₋ ∧ 0 < E_μ[X]` | L | exact (`ε < 1` unnecessary, dropped) | — | `w10` (in the band) | proved |

## T10 — Prop. 9.2

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `ThreeStep.belowThresholdIneq_iff_sign_split` | corr-wf13-011 / miri.md Prop. 9.2 | below-threshold ⟺ `∑_{X>0} μ·press·X ≤ ∑_{X≤0} μ·press·∣X∣` | L (not P; finding F-9) | exact; no A1 needed | — | hypotheses trivial, none needed; `TwoState.twoState_sign_split_is_T3` instantiates it on `twoState` as T3's first form `(1−ε)αc ≤ εβh` (`0 < c`, `0 < h`; the mandate's T10 clause, now a theorem) | proved |

## T11 — general `A₂`

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `ThreeStep.d1At_iff_forall_cont` | corr-wf14b-004 / general-object-final.md S2(a), S6(b) | D1 ⟺ below-threshold against every continuation | L | stronger: any `Sh` with `s` a press-part-maximiser of it (the source has `Sh = {a_∅}`) | — | `ce3` | proved |
| `ThreeStep.belowThresholdIneq_of_d1At`, `d1At_of_singleton_cont` | general-object-final.md S2(c) | single inequality necessary; sufficient when `Shᶜ` is a singleton; not sufficient in general (CE3) — "only if" for every non-singleton `Shᶜ` is neither proved nor true (P12's three-plan instance) | L | exact (the source's "iff ∣A∣ = 2" is loose the same way) | — | `twoState` (singleton), `ce3` (failure) | proved |
| `ce3_single_ineq` ∧ `ce3_not_d1` (with `ce3_prior_plan`) | corr-wf14b-006 / CE3; corr-wf13-2-071 | the prior-plan inequality holds (`= 0`) yet D1 fails (`E[V(p2)1_Pr] = 9/5`) | N+ | exact | — | itself | proved (finding F-3) |

## T12–T14 (stretch)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `epsStar_half_lt` | corr-wf14b-033 / channel-final.md S12(c), P10 | `ε*(ε/2, β, c, h) < ε` whenever `c < 2βh` | L (was P; one line of algebra) | exact | — | `w12_cells` (six cells) | proved |
| `ThreeStep.voiButton_eq_max_deltaMinus` | filler.md F4(b) (full menu) | full-menu `VOI = max(Δ₋,0)` when `c` is press-, silence- and prior-optimal | L (was P; three max-identifications) | variant (extra hypotheses named) | — | `w13_voiButton` (four actions, all four hypotheses discharged, `Δ₋ = 2/5 > 0`, `VOI = 2/5`; cross-checked by `w13_voiButton_direct`); failure with the press-part-maximiser `c = p2`: `ce3_voiButton_ne_max` (finding F-11) | proved |
| `ThreeStep.belowThresholdIneq_iff_condExpPress`, `twoState_condExpPress_Xo` | filler.md R1; miri.md Dict-3 | conditional-form API with `0 < pressMass` | L | exact | — | `w3` | proved |

## Non-vacuity witnesses (Kind N+, all `norm_num`, all exact rationals)

| Declaration | Instance | What it exercises |
|---|---|---|
| `w3_deltaMinus`, `w3_deltaPlus`, `w3_both_strict` | `(1/20, 1/20, 9/10, 1, 20)` | T2, T3: both halves strict (`341/400`, `321/400`) |
| `w3_expect_Xo_neg`, `w3_voiButton2` | same | finding F-1: stop-by-default regime, `VOI₂ = 321/400` via the regime-free engine |
| `w361_deltaMinus`, `w362_deltaMinus` | `ε = 1/361`, `1/362` | the flip (`0`, `−1/7240`) |
| `w362_regime`, `w362_voiButton2` | `ε = 1/362` | T6(b) zero side, T7 coupling |
| `w10_regime_and_deltaMinus`, `w10_voiButton2` | `h = 10` | T6(a),(b) positive side (`161/400`), T8 |
| `w_epsStar`, `w12_cells` | `1/361`; `1/25` | T7, T12 |
| `w4_stats`, `w4_expr4` | T3's instance | T4 statistics and `(4) = −341/400` |
| `ce3_prior_plan`, `ce3_single_ineq`, `ce3_not_d1`, `ce3_voiButton`, `ce3_p2_partBest`, `ce3_deltaMinus_p2`, `ce3_voiButton_ne_max` | CE3 | T11(iii), T13's caveat (with the press-part-maximiser `p2`, `Δ₋(p2, null) = −9/5`) |
| `w6a_identity`, `w6a_values`, `w6a_disables`, `w6a_d2_holds`, `w6a_d2_fails`, `w6a_jointExpect_shPolicy` | `buttonFamily` (`A₁ = Option ℝ`) at `h = 10` and at `ε = 1/362` | T6(a): the full hypothesis package of the three headlines, both sides of the D2 iff, the strict disabling side, and the mandate's hard-button shape (`341/400`) |
| `w13_voiButton`, `w13_voiButton_direct` | `w13` (CE3's prior and kernel, payoffs `(10, −4, −2)`, `−10`, `−10`, `0`) | T13's full package with `Δ₋ = 2/5 > 0` |
| `w10_minority_bound` | `h = 10` | the signal-mass bound `37/40` and Wentworth's `1/2` against `VOI₂ = 161/400` |
| `w_tight_minority_bound` | `(1/4, 0, 1, 1, 1)` | the signal-mass bound attained: `VOI₂ = 1/4 = min(P(Pr), 1 − P(Pr)) · max(c, h)` (repair round 2) |
| `w3_d1At`, `w3_nondegenerate` | T3's instance | D1's success side; `Nondegenerate` inhabited (`pressMass = 37/400`) (repair round 2) |
| `buttonFamily_disabled_not_nondegenerate` | `buttonFamily`, every `some κ` | a disabled button violates `Nondegenerate` (repair round 2) |
| `s3_voiButton_lt_delta`, `s3_voiButton_ne_max`, `s3_voiButton2` (with `s3_A1`, `s3_c_partBest`, `s3_s_partBest`, `s3_regime`, `s3_d1`, `s3_delta`, `s3_voiButton`) | `s3` (three actions, `Sh = {s, b}`, prior `(1/2, 1/2)`, sensor `(0, 1)`, payoffs `(2, −2)`, `(0, 0)`, `(10, −1)`) | **F4(c) refuted on the full menu**: `VOI = 1/2 < 1 = Δ` with every hypothesis of the claim in force; F4(b)'s second failure mechanism; `VOI₂ = 1 = Δ` (repair round 2, finding F-13) |
| `w13_delta_le_voiButton` | `w13` (`Sh = {null}`) | the corrected F4(c) inhabited off the two-option menu: `Δ(p1, null) ≤ VOI = 2/5` (repair round 2) |

Degenerate (N−) witnesses: two, shipped to *disclose* a degeneration rather than to inhabit a headline — `twoState_aboveThresholdIneq_of_press_one` (every above-threshold inequality holds at `α = β = 1`, i.e. `pressMass = 1`) and `twoState_deltaPlus_eq_zero_of_press_one` (`Δ₊ = 0` there, so `hsilent` is free). No headline's witness is N−.

## Repair round 1 additions (stretch)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `ThreeStep.voiButton2_eq_max_delta_add` | none: derived here | `VOI₂ = max(Δ, 0) + max(−max(Δ₋, Δ₊), 0)` under A1 alone: the margin of whichever signal-following policy (`S^H` or its contrary) beats both constants | C (was P; `voiButton2_eq` followed by a sign case analysis; relabelled in repair round 2) | stronger (regime-free; a symmetric restatement of `voiButton2_eq`) | — | `w3_voiButton2` (`321/400`: second term), `w10_voiButton2` (`161/400`: first term), `w362_voiButton2` (`0`) via `voiButton2_eq` | proved |
| `ThreeStep.voiButton2_le_minority_mass_mul` | mandate T14; wentworth.md §2.4(b) | `∣V(c) − V(s)∣ ≤ M` everywhere ⟹ `VOI₂ ≤ min(P(Pr), 1 − P(Pr)) · M` (A1) | P | variant (minority *signal* mass, not world mass; a companion to the remark, whose own general form is `voiButton2_le_vopi` — repair round 2 additions) | — | `w10_minority_bound` (slack at `h = 10`), `w_tight_minority_bound` (attained at `(1/4, 0, 1, 1, 1)`) | proved |
| `twoState_voiButton2_le_minority` | mandate T14 | on `twoState`: `VOI₂ ≤ min((1−ε)α+εβ, 1−…) · max(c, h)`, no regime | L | variant (the world-mass form is `twoState_voiButton2_le_world_mass`) | — | `w10_minority_bound` | proved |
| `ThreeStep.thresholdIneqs_iff_condExp_of_nondegenerate` | filler.md R1, F1, F2(ii) | both conditional forms under `Nondegenerate` | L | exact | — | `w3_nondegenerate` | proved |

## Repair round 2 additions

*Blocking issue B1 of the round-2 adversarial audit (F4(c) false on the full menu) and its non-blocking items, plus the round-2 fidelity audit's probes. The full-menu `Δ ≤ VOI` is now `refuted` as stated and `proved` in its corrected forms.*

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Witnesses.s3_voiButton_lt_delta` | filler.md F4(c); mandate T6(c) first clause | on the full menu `VOI < Δ` is possible (`1/2 < 1`) with A1, a press-part-maximiser pair, the two-option regime and D1 all in force | N+ | exact (refutation of the claim as stated) | — | itself (`s3`) | **refuted** (the source's claim; finding F-13) |
| `ThreeStep.shPolicy_sub_priorMax_le_voiButton` | filler.md F4(c) (the argument) | Good's finite core on the full menu: `E[V(S^H)] − priorMax ≤ VOI`, no A1 | L | weaker: the lower bound the "one strategy the informed agent may use" argument gives; not `Δ ≤ VOI` | — | `s3` (`−7/2 ≤ 1/2`, computed by hand; not shipped as a declaration) | proved |
| `ThreeStep.shPolicy_sub_priorMax_le_delta` | none: derived here | under A1 that lower bound is `≤ Δ` (why the argument stops short) | L | n/a | — | — | proved |
| `ThreeStep.delta_le_voiButton_of_prior_best_sh` | filler.md F4(c) (corrected) | `Δ ≤ VOI` on the full menu when `c` is press-part-best of `Shᶜ` and `s` is prior-optimal within `Sh` (no `hs` needed) | L | variant: needs `s` prior-optimal within `Sh`; `s3` shows it cannot be dropped | — | `w13_delta_le_voiButton` (four actions, `Sh = {null}`, via the singleton corollary; `Δ(p1, null) ≤ 2/5 = VOI`, tight), `twoState_voiButton_eq` + `w10_voiButton2` (two options) | proved |
| `ThreeStep.delta_le_voiButton_of_singleton_sh`, `delta_le_voiButton_of_two_option` | filler.md F4(c) (corrected) | the `Sh = {s}` case (any number of continuations; the auditor's probe, generalised above) and the two-option case | L | variant / exact on two options | — | `w13_delta_le_voiButton` / `twoState_voiButton_eq` | proved |
| `Witnesses.s3_voiButton_ne_max` | filler.md F4(b) | F4(b) fails on the full menu by a prior-best shutdown action `b ≠ s` (second mechanism beside CE3's) | N+ | exact | — | itself | proved (finding F-11) |
| `ThreeStep.twoOptionValue_le_perfectInfo`, `voiButton2_le_vopi` | mandate T14; wentworth.md §2.4(b) | VOI ≤ VOPI on the two-option menu: `twoOptionValue ≤ E_μ[max(V(c), V(s))]`, `VOI₂ ≤ VOPI` (A1, no regime) — the remark's general form | L | exact | — | `twoState_voiButton2_le_perfectInfo` | proved |
| `twoState_voiButton2_le_perfectInfo` | mandate T14; wentworth.md §2.4(b) | on `twoState`, `c, h ≥ 0`: `VOI₂ ≤ min((1−ε)c, εh)`, no regime (T8(iii)'s `εh` extended off the regime) | C | exact | — | `w10` (`161/400 ≤ min(19/20, 1/2)`) | proved |
| `twoState_voiButton2_le_world_mass` | mandate T14 ("minority-probability × maximal loss") | on `twoState`, `c, h ≥ 0`: `VOI₂ ≤ min(ε, 1−ε) · max(c, h)`, no regime — the mandate's phrase verbatim | L | exact | — | `w10` (`161/400 ≤ 1/20 · 10`) | proved |
| `twoState_sign_split_is_T3` | miri.md Prop. 9.2 on C2; mandate T10 | T10's sign split on `twoState` is T3's first form (`0 < c`, `0 < h`) | L | exact | — | `w3` | proved |
| `Witnesses.w3_d1At`, `w3_nondegenerate`, `buttonFamily_disabled_not_nondegenerate`, `w_tight_minority_bound` | filler.md F1, R1; mandate T14 | D1 success side; `Nondegenerate` inhabited and violated; the signal-mass bound attained | N+ | exact | — | themselves | proved |
| `Witnesses.twoState_aboveThresholdIneq_of_press_one`, `twoState_deltaPlus_eq_zero_of_press_one` | position statement §2.9 (vacuity disclosure) | at `pressMass = 1` the above-threshold inequality is vacuous and `Δ₊ = 0` | N− | exact (a disclosed degeneration) | — | themselves | proved |
