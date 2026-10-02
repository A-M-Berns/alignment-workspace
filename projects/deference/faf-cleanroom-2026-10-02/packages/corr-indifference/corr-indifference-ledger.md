# corr-indifference — ledger

*One row per headline ([STANDARDS](../../STANDARDS.md) §6). Namespace prefix `Cleanroom.Corrigibility.CorrIndifference.` omitted; `SoaresModel.`-namespaced declarations take `M : SoaresModel O A₁ A₂`. Hyps column lists only (b)/(c); "—" means every hypothesis is (a). "named, unused" marks a hypothesis carried for the statement's meaning (the domain of a quotient of record, or a source's standing assumption) that the proof does not consult; each such case is disclosed in the docstring. Refutation rows quote the source sentence, fix the reading, and name the surviving neighbour (plan §0.4 rule 3). Kinds are graded by what the proof does, not by the mandate's pre-label; where they differ the report says why.*

## Definitions of record (Kind D)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `SoaresModel` | corr-refs-001 / soares-2015 §1.2 | `Press ⊆ O`, kernel `p : A₁ → Distr O`; utilities are parameters | D | exact | — | `Witnesses.M5`, `coinArm`, `driveModel` | proved |
| `SoaresModel.best`, `IsBest` | soares-2015 §1.2 | the value `max_{a₂} U` and the predicate; no selection | D | exact | — | — | proved |
| `SoaresModel.EU`, `branchSum`, `pressMass` | soares-2015 §1.2 | `∑_o p(o) best(o)`; the branch sum over `S`; FAF's `prob` of `Press` | D | exact | — | — | proved |
| `SoaresModel.vN`, `vS` | soares-2015 §2.1 eq. (7), §3, §4.1 | the conditional values as quotients; junk `0` at mass 0, disclosed | D | exact (division convention disclosed) | — | `twoObs_vN`, `twoObs_vS` | proved |
| `SoaresModel.condKernel` (D-4) | corr-wf13-2-004 / miri.md I2.3 | `p(· ; a₁)` conditioned on silence, a FAF `Distr` under `p(Press) < 1` | D | exact | — | `CoinArm.condKernel_zero_where_world_positive` | proved |
| `SoaresModel.mixU` (D-2) | soares-2015 §2.1 eqs. (5), (6), (8) | `U_S = chigh/clow` by `Sh` on `Press`, `U_N` off it; arbitrary finite `O` | D | stronger (any `O`, `Press`; the source's `Obs` is `twoObs`) | — | `M5` | proved |
| `SoaresModel.f`, `indiffU` (D-3) | soares-2015 §3 eqs. (11), (13) | `f = vN − vS`; `U_N` off `Press`, `U_S + f` on it | D | exact | — | `coinArm`, `M6` | proved |
| `SoaresModel.twoObs` | soares-2015 §2.1 | `O = Obs`, `Press = {press}`, press probability `q a₁` | D | exact | — | `M5`, `M6` | proved |
| `SoaresModel.ofObsProd` | soares-2015 §4.2 eq. (17) | `O = Obs × C`, `Press = {press} × C` | D | exact | — | `coinArm`, `driveModel` | proved |
| `coinArm q`, `coinUN` | soares-2015 §4.2 eqs. (17)–(18); corr-refs-2-029 | the coin/arm kernel with press rate `q`; `U_N = 10` on heads | D | stronger (`q`; the source is `q = 0`) | — | itself | proved |
| `driveModel ε`, `driveUN π` | fallenstein-2014 | null / ticket / drive with win probability `ε`; prize `π` | D | exact (honest ticket added) | — | itself | proved |
| `ThreeStepBridge.toSoares`, `postU` | corr-wf13-2-004 / miri.md I9.1 | the Setting-S instance as a Soares model on `O = Obs` with the posterior-value utility | D | variant: `O = Obs`, not the mandate's `Obs × Ω` (report deviation, finding F6) | — | — | proved |
| `Estimators.E`, `SeqUnbiased`, `SeqUnbiasedChain` (D-5) | armstrong-2016 "Probability estimators", "Sequentially unbiased" | `E_ρ X` a function of the state; `E_{ρ_i} E_{ρ_j} X = E_{ρ_i} X` for all `X`, all `i < j` | D | exact | — | `twisted_not_seqUnbiased` (failure), `seqUnbiased_condKernel` (success); `SeqUnbiasedChain` consumed by `Dchain_eq_zero_of_chain` (audit r2 adversarial N-7) | proved |
| `Estimators.cls`, `classMass`, `condExp`, `condKernel`, `Refines` | armstrong-2016 (conditioning estimators) | partitions as label maps; `E_P[X ∣ π]` junk-safe; the kernel under positivity | D | exact | — | `curse_strict` (the two kernels on `Bool`) | proved |
| `Estimators.comp`, `compValue`, `Dterm` | armstrong-2016 "Hacking", "Double indifference"; armstrong.md I5.3 | `C(ρ') = E_{ρ'}(Y) − E_{ρ'}(Z)`; its current valuation; `D = −(E_μ[C(ρ_j)] − c_i)` | D | variant: the causal-counterfactual reduction (c) disclosed (the independent coin makes the conditionals unconditional); and I5.3's number form `c_i = E_μ Y − E_μ Z` at the current state in place of the random variable `C(ρ_i)` (report deviation 5) | (c) as stated | `echannel_witness` | proved |
| `Estimators.Dchain` | armstrong-2016 (`D_t` in terms of `D_{>t}`) | the `n`-change `D`-terms by downward recursion | D | exact (finite chain) | — | — | proved |
| `Estimators.selectedKernel` | corr-core-024 | a selection rule measurable to the current class | D | exact | — | — | proved |
| `Stratified.StratModel`, `stratValue`, `actualValue` (D-6) | corr-refs-2-027/030 / armstrong-2017 | `∑ P (I_u u + (1 − I_u) v)`; the actual value under a choice mechanism | D | variant: SCM layer folded into `u`, `v` (`corr-scim-cid` owns the SCM) | (c) as stated | `lottery`, `coinArmStrat` | proved |
| `Stratified.pStrat`, `value2016` | corr-refs-2-027 / armstrong-2016 | the 2016 `p_αβ` as `E_P[I_u ∣ strat]`; the 2016 form with the worked example's `+` | D | exact (sign per the worked example; erratum F7) | — | — | proved |
| `Stratified.lottery`, `coinArmStrat` | corr-refs-2-028/029 | the lottery model (the source's second scenario embedded as its third action); the coin/arm embedding (ATTRIBUTION-UNVETTED) with Soares' button-independent `U_N` | D | exact / variant (the inventory's embedding; its shutdown-term `u` is `coinArmStratShut`) | — | themselves | proved |

## T1 — the model (Kind L, derived objects)

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `SoaresModel.branchSum_compl_eq_mul_vN`, `branchSum_press_eq_mul_vS` | soares-2015 eq. (7) | product forms `∑_{o ∉ Press} p best = (1 − p(Press)) vN`, `∑_{o ∈ Press} p best = p(Press) vS`, **unconditionally** (junk case: every summand has mass 0) | L | exact | — | — | proved |
| `SoaresModel.expect_condKernel_best` | soares-2015 Theorem 5; miri.md I2.3 | `E_{condKernel a}[best U_N a] = vN a` | L | exact | — | `CoinArm` | proved |
| `SoaresModel.twoObs_vN` | soares-2015 §2.1 eq. (7) | on `O = Obs` with `q a < 1`, `vN a = max_{a₂} U_N(a, ¬Pr, a₂)` | L | exact | — | `M5_vN` | proved |
| `ThreeStepBridge.EU_postU` | miri.md I9.1(i) | the Soares `EU` of the posterior-value utility is `obsMax press + obsMax silent` | L | exact | — | — | proved |
| `ThreeStepBridge.EU_indiffU_postU` | miri.md I9.1(iii) | the indifferent agent on the Setting-S carrier is `obsMax silent / (1 − pressMass)`, for any `U_S` | L | exact | — | — | proved |

## T2 — Theorems 1 and 2 as iffs

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `SoaresModel.EU_mixU` | soares-2015 eq. (7) | `E[U ; a] = (1 − p(Press)) vN + p(Press) chigh` | L | exact | — | `M5` | proved |
| `SoaresModel.theorem1_iff` | corr-refs-002 / Theorem 1 | for the Theorem-1 shape: `E[U ; a⋆] < E[U ; a⁻] ⟺ chigh < vN(a⁻) − q⋆ χ / δ` | P | stronger (iff; explicit `ζ`; any finite `O`) | — (`hq⋆` the package's identification condition — §2.1's `v_N` is a cell value, the quotient `vN` equals it under `q < 1`, `twoObs_vN` — and `hχ` the source's shape; both named, unused; only `hδ` is consulted; audit r2 adversarial N-3) | `Witnesses.w2_theorem1` (both sides: `chigh = 3` yes, `5` no; `ζ = 4`); `w2_direct_values` (the `EU`s from eq. (7) without the iff) | proved |
| `SoaresModel.theorem2_iff` | corr-refs-003 / Theorem 2 | for the Theorem-2 shape: `E[U ; a⋆] < E[U ; a⁺] ⟺ vN(a⁺) + q⋆ χ' / δ' < chigh` | P | stronger (iff; explicit `ζ'`) | — (`hq⁺` the package's identification condition for `vN(a⁺)`, `hχ` the source's shape; both named, unused; only `hδ` is consulted) | `Witnesses.w2_theorem2` (both sides: `chigh = 14` yes, `12` no; `ζ' = 13`); `w2_direct_values` | proved |

## T3 — the equal-value choice

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `SoaresModel.EU_mixU_equal_value` | corr-refs-004 / eq. (10) | `E[U ; a] = Mx − (1 − p(Press ; a))(Mx − vN(a))` | L | exact | — | `w3_ceiling` | proved |
| `SoaresModel.no_prevent_steering_at_equal_value` | eq. (10), the sentence after it | with `chigh` bounding the silent best values, no Theorem-1-type action is ever preferred | P | exact (the prevent-`Press` half) | — | `Witnesses.w3_no_prevent` (`9 < 11`) | proved |
| `SoaresModel.cause_steering_at_equal_value_iff` | eq. (10), footnote 5 | `E[U ; a⋆] < E[U ; a⁺] ⟺ χ' < (chigh − vN(a⋆)) δ' / q⁺`: pairwise cause-steering survives at `chigh = M` | C | exact (Theorem 2 re-parametrised at the equal-value choice) | — (`hg`, `hδ'` named for the shape, unused; only `hq⁺` is consulted) | `Witnesses.w3_cause_both_sides` (`χ' = 1 < 2` yes, `3` no); `w3_direct_values` | proved; the source sentence **refuted in the paper's pairwise sense** (F2, imprecision): "averts any incentives to steer towards one case or the other" — reading fixed: true for preventing; for causing, false pairwise; true weakly at the global optimum on `O = {Pr, ¬Pr}` **when every action has `p(Press ; a) < 1`** (`twoObs_honest_is_global_optimum`; equivalently, when (10)'s max is carried by an action that can be silent), and false strictly whenever no `vN` attains (10) — on a general `O` (`strict_cause_steering_general_O`) or on `O = {Pr, ¬Pr}` when only a certain-press action carries the ceiling (`strict_cause_steering_twoObs`; audit r2 B-1); true weakly on every finite `O` at the corrected ceiling `c_high = max_{a : p(Press ; a) < 1} vN(a)` (`vNmax_is_global_optimum`); surviving neighbour: footnote 5 |
| `SoaresModel.EU_mixU_le_of_bound`, `EU_mixU_eq_of_press_one` | eq. (10) | `E[U ; ·] ≤ Mx`; `= Mx` at every certain-press action | L | exact | — | `w3_ceiling` | proved |
| `SoaresModel.EU_mixU_eq_of_vN_eq`, `EU_mixU_le_of_vN_eq` | eq. (10), the sentence after it (audit r1 NB-1) | an action attaining the ceiling (`vN(a₀) = Mx`) is worth `Mx` and is a global optimum: the global, weak reading of "averts any incentives" | L / C | exact (the global reading) | — | `twoObs_honest_is_global_optimum`; `w3_ceiling` | proved |
| `SoaresModel.twoObs_honest_is_global_optimum` | eq. (10), the sentence after it (audit r1 NB-1; audit r2 B-1) | on `O = {Pr, ¬Pr}` with every `q a < 1` and `chigh = silentMax`, some `a₀` has `vN(a₀) = silentMax` and `E[U ; a] ≤ E[U ; a₀]` for all `a` — the honest action is never strictly beaten, when every action can be silent | C | exact (the source's setting, every action silent-capable) | — (`hq1`: every action silent-capable; **load-bearing**: without it a certain-press action can carry (10) with its `vN` the junk `0`, `Witnesses.strict_cause_steering_twoObs`) | `Witnesses.M5` at `chigh = 12` (`w3_ceiling`, `w3_direct_values`); the guard's witness `Witnesses.strict_cause_steering_twoObs` | proved |
| `Witnesses.strict_cause_steering_general_O` | eq. (10) (audit r1 NB-1, the auditor's example) | on `O = {Pr, ¬Pr₁, ¬Pr₂}` at `chigh = 12` (bounds and attained, so it is `M`): `E[U ; star] = 10 < 12 = E[U ; sure]` — the strict global incentive to cause the press, absent on the source's carrier when every action can be silent | N+ | variant: general finite `O`; what the strict failure needs is "no `vN` attains `M`", not the size of `O` (audit r2 B-1) | — | itself | proved |
| `Witnesses.strict_cause_steering_twoObs` | eq. (10) (audit r2 B-1, the auditor's probe with `U_N(sure, Pr) = 0`) | on `O = {Pr, ¬Pr}` with `star` (press `½`, `U_N = 10`) and `sure` (press `1`, `U_N = 0` on the press, `12` on its unreachable silent cell): `12` bounds and is attained, so it is the literal (10); `E[U ; star] = 11 < 12 = E[U ; sure]` at `chigh = 12` although `E[U_N ; star] = 10 > 0 = E[U_N ; sure]` — the strict global incentive to cause the press on the source's own carrier; at `chigh = max vN = 10` the two tie | N+ | exact (the source's two-observation setting; the literal (10)) | — | itself; `vNmax_twoObs` (the tie as an instance of `vNmax_is_global_optimum`) | proved |
| `SoaresModel.EU_mixU_le_of_vN_bound`, `vNmax_is_global_optimum` | eq. (10), the sentence after it (audit r2 B-1; the natural sharpening) | `E[U ; ·] ≤ Mx` when `vN(a) ≤ Mx` at every silent-capable `a`; at `chigh = vN(a₀)` with `a₀` the `vN`-maximiser among silent-capable actions, `E[U ; a] ≤ E[U ; a₀]` for every `a` — the weak global reading at the corrected ceiling, on any finite `O`, for any press probabilities | L / C | variant: the ceiling is `max_{a : p(Press ; a) < 1} vN(a)`, not (10)'s cell maximum (equal to it on `O = {Pr, ¬Pr}` under `hq1`) | — (`ha₀` silent-capable: named, unused, the domain on which `vN(a₀)` is the conditional value) | `Witnesses.vNmax_twoObs` (`chigh = 10`, both actions worth `10`) | proved |
| `SoaresModel.silentMax`, `best_le_silentMax`, `exists_eq_silentMax` | eq. (10) | the source's `chigh`; it bounds and is attained | D/L | exact | — | — | proved |

## T4 — the identity

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `SoaresModel.branchSum_indiffU_press`, `branchSum_indiffU_compl` | corr-refs-005 / Theorem 4 proof | the two branches of `indiffU` are `p(Press) vN` and `(1 − p(Press)) vN`, unconditionally | L | exact (product form) | — | `CoinArm.EU_indiffU` | proved |
| `SoaresModel.EU_indiffU_eq_vN` | Theorem 4 proof, eq. (15); corr-core-020 | `E[indiffU U_N U_S ; a] = vN U_N a` for every `U_S`, every `a` | L | exact; unconditional as an equation (junk cases disclosed) | — | `CoinArm.EU_indiffU`, `Drive.EU_indiffU` | proved |
| `SoaresModel.condPress_indiffU`, `condSilent_indiffU` | eq. (15) | the conditional forms under `0 < p(Press)` / `p(Press) < 1` | L | exact | — | — | proved |
| `SoaresModel.theorem4_boundary` | Theorem 4; fallenstein-2014 | `vN(a♯) < vN(a⋆) ⟹ E[U ; a♯] < E[U ; a⋆]` under `p(Press ; ·) < 1` only | L | stronger (boundary included) | — (named, unused) | `CoinArm.armTails_preferred` (`q = 0` allowed) | proved |
| `SoaresModel.theorem4` | Theorem 4 | the same at `0 < p < 1` (the domain of the source's conditional `v_N`, `v_S`; the source never states it, F3) | L | exact | — (the bounds: the package's identification condition for the quotient `vN`, not a stated assumption of the source; named, unused; audit r2 adversarial N-3) | `Witnesses.w6_theorem6` | proved |

## T5 — Theorems 3 and 5

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `SoaresModel.isBest_indiffU_press_iff` | corr-refs-006 / Theorem 3, eq. (14) | on `Press` the best-sets of `indiffU` and `U_S` coincide | L | exact | — | `isProducedBy_indiffU_iff` | proved |
| `SoaresModel.isBest_indiffU_silent_iff` | Theorem 5 | off `Press` the best-sets of `indiffU` and `U_N` coincide | L | exact | — | same | proved |
| `SoaresModel.EU_indiffU_le_iff` | Theorem 5 | the ordering on `A₁` is `vN`'s | L | exact | — (named, unused) | `M6` | proved |
| `SoaresModel.EU_indiffU_eq_expect_condKernel` | Theorem 5; miri.md I2.3 | "believes the button will not be pressed" = plans under D-4's kernel | L | exact | — | `CoinArm` | proved |

## T6 — Theorem 6 and `U_S`-invariance

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `SoaresModel.theorem6` | corr-refs-007 / Theorem 6 | `ε > 0`, `δ > 0` ⟹ the agent prefers `a⋆`; `hδ` named and unused — that is the theorem | L (mandate: P) | exact | — (`hδ`, nondegeneracy named, unused) | `Witnesses.w6_theorem6` (`ε = 1/1000`, `δ = 10⁶`, both nondegenerate) | proved |
| `SoaresModel.EU_indiffU_US_invariant` | Theorem 6, §4.1; corr-core-021 | `E[indiffU U_N U_S ; a] = E[indiffU U_N U_S' ; a]` for all `U_S, U_S', a` (which reading of desideratum 4 this refutes is ATTRIBUTION-UNVETTED) | L (mandate: P) | stronger (identity, no nondegeneracy) | — | `w6_theorem6` | proved |

## T7 — the coin/arm model

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `CoinArm.vN_watch`, `vN_armTails`, `vN_armHeads` | corr-refs-008 / eqs. (19)–(21) | `5`, `10`, `0` for every `q < 1` | L | exact (generalised to `q`) | — | themselves | proved |
| `CoinArm.EU_indiffU` | eqs. (19)–(21) | the indifferent agent's three values, for every `U_S` | N+ | exact | — | itself | proved |
| `CoinArm.armTails_preferred` | §4.2 ("would execute `a₁ᵃ`") | `5 < 10`: the arm-on-tails is preferred (D3-type shape) | N+ | exact | — | itself | proved |
| `CoinArm.armHeads_removed` | §4.2 ("incentivizes removing that arm") | `0 < 5`: removing the arm-on-heads is preferred (D2-type shape) | N+ | exact | — | itself | proved |
| `CoinArm.condKernel_zero_where_world_positive` | corr-wf13-2-004 / miri.md I2.3, I3.2 | the planning kernel gives `(Pr, T)` mass `0` where the world gives `1/2` and the arrival point mass `1` | L | exact | — | itself | proved |

## T8 — the drive

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Drive.EU_indiffU` | corr-refs-009 / fallenstein-2014; corr-core-021(iii) | `EU null = 0`, `EU ticket = ε π`, `EU drive = π` for every `ε ∈ (0,1]`, `π`, `U_S` (only `0 < ε` needed; the round-1 `ε < 1` dropped, audit r1 N-1) | N+ (regraded from P: a parametric computation) | stronger (quantified; honest ticket) | — | itself | proved |
| `Drive.drive_preferred` | fallenstein-2014 | `ε π < π` for `π > 0` | N+ | exact | — | itself | proved |

## T13 — Fallenstein's policy lemma

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `SoaresModel.Policy`, `IsProducedBy`, `trajectory` | corr-refs-011 / fallenstein-2015 | policies; produced-by as predicates; the trajectory law by `Distr.map` | D | exact | — | — | proved |
| `SoaresModel.isProducedBy_iff_of_same_bests` | fallenstein-2015 l. 52–58 | same best-sets and maximiser set ⟹ same produced policies ("generalised impossibility") | L | exact | — | `isProducedBy_indiffU_iff` | proved (finding F5: presentation) |
| `SoaresModel.isProducedBy_indiffU_iff` | fallenstein-2015 (the display); Theorems 3, 5 | the indifferent utility's policies characterised, on the domain `∀ a, p(Press ; a) < 1` where the display's `argmax E[U_N ∣ O ∉ Press ; a₁]` is defined | L | exact (on that domain; audit r1 B-2) | — (`hnd` named, unused: the domain of `vN`) | `Witnesses.certainPress_junk` (the guard is not decorative: at a certain-press action the junk `vN = 0` beats `U_N ≡ −5`) | proved |

## T14 — double indifference

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Estimators.condExp_condExp` | corr-wf13-2-012 / armstrong-2016 | the tower `E_P[E_P[X ∣ π'] ∣ π] = E_P[X ∣ π]` for `π'` refining `π`, as functions, no positivity | P | stronger (junk-safe) | — | `tower_instance` (`id` strictly refining `fst` on `Bool × Bool` under the uniform prior: `E[X ∣ id] = X`, `E[X ∣ fst] = 1/2`) | proved |
| `Estimators.seqUnbiased_condKernel` | same | sequential unbiasedness of conditioning kernels along a refinement — derived | C | exact | — | — | proved |
| `Estimators.echannel_witness`, `twisted_not_seqUnbiased` | corr-core-022 / armstrong-2016 "Hacking"; armstrong.md I6.1 | a non-conditioning estimator valued `1 > 1/2` by compensation alone; it is not SU | N+ | exact | (c) the counterfactual reduction in `comp` | themselves | proved |
| `Estimators.compValue_add_Dterm` | armstrong-2016 "Double indifference"; I6.1 | `E_μ[C(ρ')] + D(ρ') = c_i` for every `ρ'` | L | exact | (c) as above | `echannel_Dterm` (`−1/2`; totals tie at `1/2`) | proved |
| `Estimators.Dterm_eq_zero_iff`, `Dterm_eq_zero_of_seqUnbiased` | armstrong-2016 ("So `D_t = 0`") | `D = 0 ⟺` SU for `Y − Z` at the state; SU ⟹ `D = 0` (one evaluation of the hypothesis) | L / L (regraded from C, audit r1 NB-4) | exact | (c) as above | `Dterm_condKernel_eq_zero` | proved |
| `Estimators.Dterm_condKernel_eq_zero` | armstrong-2016; corr-wf13-2-012 | `D = 0` at every state for conditioning kernels along a refinement | C | exact | (c) as above | — (hypotheses trivially satisfiable, `Refines π π`; `tower_instance` inhabits a strict refinement; no `D`-term value computed on it) | proved |
| `Estimators.Dterm_eq_illegit_part` | corr-wf13-046 / armstrong.md I5.3 | under conditional SU on `L` and `L ⊥ (Y − Z)`: `D = −μ(Lᶜ) E_μ[(E_{ρ_j} − E_μ)(Y − Z) ∣ Lᶜ]` (`Lᶜ` may be null; the round-1 `0 < μ(Lᶜ)` dropped, audit r1 N-2) | C | exact | (c) as above; I5.3's two conditions named; `hL` positivity of `L` | `Dterm_eq_zero_of_univ` (`L = univ` gives `D = 0`) | proved |
| `Estimators.Dchain_eq_zero` (S7) | armstrong-2016 ("recurse … `D` always zero") | along a fixed SU chain every `D`-term `D_n, …, D_0` is `0` (all `d ≤ n`; the round-1 `d < n` omitted `D_0`, audit r1 B-1), by induction; the chain is fixed — the `n`-step menu form (the total the same for every chain the agent could pick) is not stated, the one-step menu form is `compValue_add_Dterm` (audit r2 adversarial N-1) | C (regraded from P: each step is one evaluation of the pair's SU once the later terms vanish; audit r2 adversarial N-2) | exact (finite `n`, fixed chain) | (c) as above | `Dchain_one_change` (the `n = 1` first term, the post's own case); `Dchain_zero_def` (`d = 0` is definitional); `Dchain_eq_zero_of_chain` (from D-5's `SeqUnbiasedChain`) | proved |
| `Estimators.seqUnbiased_selectedKernelGen`, `seqUnbiased_selectedKernel` (S8) | corr-core-024 | a selection measurable to the current class among *any* candidates each sequentially unbiased from the current kernel keeps SU (`…Gen`, the claim's premise as stated; audit r2 N-1); among conditioning refinements as its corollary via `seqUnbiased_condKernel` (the round-0 theorem) | P / C | exact (the claim's premise verbatim) / exact (the refinement subclass) | — | `selectedKernel_su`, `selectedKernel_non_constant` (uniform prior on `Bool × Bool`, menu {learn all, learn nothing}, selection `id`: refine on one class only; the composite estimate is `0` and `1/2` at two states) | proved; corr-core-024 **refuted** in the tower reading (F8), for its premise as stated: "the estimator selected by `argmax_k E_ρ(· ∣ ρ → ρ'_k)` is not sequentially unbiased" — reading fixed: selection by the current information keeps the tower, and the claim's own rule is a tie (`selection_rule_ties`); surviving neighbour: `expect_sup_ge`, `curse_strict` (selection by the estimate biases the estimate) |
| `Estimators.compValue_eq_of_seqUnbiased`, `selection_rule_ties` (S8) | corr-core-024 (audit r2 adversarial N-6, the auditor's probe) | under the claim's premise every candidate's compensation is valued `E_ρ(Y − Z)(w)` by the current estimator — `argmax_k E_ρ(· ∣ ρ → ρ'_k)` is a tie | L | exact | (c) the counterfactual reduction in `comp` | — (hypotheses trivially satisfiable; `Dterm_all_zero`-type content is `Dterm_eq_zero_of_seqUnbiased`) | proved |
| `Estimators.expect_sup_ge`, `curse_strict` (S8) | corr-core-024 flag; armstrong.md I6.2 | `E_μ[max_k E_{ρ'_k} X] ≥ E_μ X` (the state-wise max dominates each candidate; not Jensen — I6.2's Jensen step is `Critiques.good_refinement`; audit r2 N-6); strict on the fair coin (`3/4 > 1/2`) | L / N+ | exact | — | `curse_strict` | proved |

## T15 — stratified indifference

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Stratified.lottery_values`, `lottery_preferences` | corr-refs-2-028 / armstrong-2016 §"Examples" | `13/40`, `3/10`, `3/4`; declines the manipulation, accepts the direct change | N+ | exact | (c) SCM folded into `u`, `v` | themselves | proved |
| `Stratified.value2016_eq_stratValue` | corr-refs-2-027 (flag) | the 2016 form equals the SCM form when `u − v` is constant on each stratum | P | variant: a sufficient condition, the one the worked example uses (the inventory's "`(u, v)`-values determine the background facts" would make `I_u` constant on strata and give the identity with no condition on `u − v`; audit r2 N-5) | (c) as above | `value2016_lottery` (the 2016 strata `lotStrat`; `lotStrat_const` discharges the condition for all three actions; `13/40`, `3/10`, `3/4`; `pStrat lostU = 1/2`; machine-checks F7's `+`) | proved |
| `Stratified.coinArmStrat_values`, `coinArmStrat_tie_breaks` | corr-refs-2-029 (ATTRIBUTION-UNVETTED embedding) | all three coin/arm actions worth `5(1 − q) + q chigh`: indifference, not prevention; any cost/benefit breaks the tie | N+ / L | exact under the embedding with Soares' button-independent `U_N` (the three-way tie rests on that choice; audit r1 NB-5) | (c) as above; the embedding | themselves | proved |
| `Stratified.coinArmStratShut_values` | corr-refs-2-029 (the inventory's `u` with a shutdown term; audit r1 NB-5) | under "`0` if shut down": watch and arm-on-tails still `5(1 − q) + q chigh`, arm-on-heads `q chigh`, strictly dispreferred for `q < 1`; `a^a = a^w` holds under both `u`s | N+ | variant (the inventory's `u`) | (c) as above; the embedding | itself | proved |
| `Stratified.stratValue_eq_actualValue`, `actualValue_sub_actualValue` | corr-refs-2-030 | agreement when `Hum a = I_u`; the actual-value difference under two mechanisms | L | exact | (c) as above | `coinArmStrat_actual_differs` | proved |
| `Stratified.coinArmStrat_actual_differs` | corr-refs-2-030 | the mechanism counting the arm's press moves the arm's actual value by `(1 − q)/2 · chigh`; `stratValue` cannot move | N+ | exact under the embedding | (c) as above | itself | proved |

## T7(b), (c) — the Setting-S valuation and the garbling

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `CoinArmS.settingSValue` | coin_arm.py block 3 | `½ informed(S_heads) + ½ informed(S_tails)` with `armed`/`sensed` per face; the coin's `10` is paid only on `cont` here (`coin_arm.py` l. 14), unlike `coinUN` | D | exact (the scratch's computation as a definition of record) | (c) the coin-average decomposition is the definition, not derived (the `ThreeStep` carrier observes only the button; audit r1 NB-12) | itself | proved |
| `CoinArmS.settingSValue_eq`, `watch_best` | corr-wf13-2-004 / coin_arm.py | `213/50`, `102/25`, `179/50`; watch strictly best | N+ | exact | — | themselves | proved |
| `CoinArmS.isGarbling_arm`, `blackwellLE_arm_watch` | corr-wf13-2-004 (T7(c)) | the arm is watching post-processed by "press if tails"; `armExp ≤ watchExp` (Blackwell's value theorem is not proved here; `102/25 < 213/50` is a separate computation) | N+ / L (regraded from P / C: a 16-cell verified instance, and the witness packaged; audit r2 N-3) | variant: signal `Obs × Coin` (the mandate's `Obs` cannot express the channel) | — | itself | proved |

## T10 — Armstrong 2010

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Armstrong2010.U`, `E1`, `E0`, `v`, `Saturated` | corr-refs-013 / armstrong-2010 §2 | the intrinsic utility (junk at mass 0, disclosed), the class cuts, the rescaled utility, unions of classes | D | exact | — | — | proved |
| `Armstrong2010.prop_2_2` | Proposition 2.2 | `V(E₁) = V(E₀)` under `P(E₁), P(E₀) > 0` | L | exact | — | — (no instance shipped; the positivity hypotheses are the report's §3 singularity) | proved |
| `Armstrong2010.class_sum_v` | Theorem 2.3 (its proof's content) | `∑_{E} P v_P = P(E) U_P(E₀)`, unconditional | P | exact | — | — | proved |
| `Armstrong2010.theorem_2_3` | Theorem 2.3 | same class masses, `E₀`-conditionals and off-`ΩX` masses ⟹ same `v`-expectation on every saturated set, each prior with its own `v`; `P(E₁ ∣ E)` arbitrary | C | exact (the precise form; the source's wording conflates `p` and `X`, F10) | — | — | proved |

## T11, T12 — Armstrong 2015, Arbital

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Armstrong2015.twoPeriod`, `lift`, `meta_eq_indiffU` | corr-refs-014 / armstrong-2015 eq. (6) | the two-period model; eq. (6) *is* `indiffU` with `Press = {switch} × Y` | D / L | exact | — | — | proved |
| `Armstrong2015.EU_meta_eq_stayValue` | Theorem 4.1, Lemmas 4.2–4.4 | `E[meta ; a] = E(u ∣ stay ; a)`: "pure `u`-maximiser" = stay-conditional maximiser (F9) | L | exact (the identity; the headline sentence is weaker than it sounds) | — (`ha` named, unused) | `CoinArm` (the same identity) | proved |
| `Armstrong2015.EU_meta_v_invariant` | Lemma 4.3 | indifference to `v`-only actions = Theorem 6 | L | exact | — | — | proved |
| `Arbital.sup_add_theta` | corr-refs-012 / arbital (the `θ` display) | `max_a (E[U_Y ∣ a] + θ) = max_a E[U_X ∣ a]` | L | exact | — | `Arbital.witness` | proved |
| `Arbital.twoStageValue_eq`, `twoStageValue_EY_invariant` | arbital objection (b) | the two-stage value is `M_X(a₁)`, independent of `U_Y` and `p_s` | L | variant: the two-stage value stated as an inlined formula over the reachable maxima, not as the `EU` of a `twoObs` model (the independence assumptions in the docstring; audit r2 N-2, consistent with `mixture_identity`) | — | `Arbital.witness` (`Fin 2 × Fin 2`, choice unchanged when `U_Y`'s maxima drop from `(10, 0)` to `(0, −10)`) | proved |

## T16 — the constitutive press

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Constitutive.constit`, `checkH`, `checkH0`, `checkHt` | corr-wf14-032 / legitimacy.md R4; checks.py check H | Setting S with the `C`-latent, sensor rows per action, `V` violating A1 on `C`; the parameter point | D | exact | — | themselves | proved |
| `Constitutive.sign_gamma_zero`, `sign_gamma_tenth` | check H | press-conditional sign `+` at `γ = 0` (`¬ D1At`), `−` at `γ = 1/10` (`D1At`) | N+ | exact | — | themselves | proved |
| `Constitutive.values_kprime_zero`, `values_kprime_k`, `steering` | check H | informed values `(200781/200000, 3, 8899/10000)` / `(770781/200000, 3, 38899/10000)`; force wins at `k' = 0`, disable at `k' = 30` | N+ | exact (exact rationals for the scratch's decimals) | — | themselves | proved |
| `Constitutive.constancy_gamma_one` | check H (`k' = k`) | at `γ = 1`, `k = k' ≥ 0` every first action is worth `k` | L | exact (constancy; the identification with D-3 is ATTRIBUTION-UNVETTED) | — | — | proved |

## T9, X2 — the stochastic wire

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `SoaresModel.condVal`, `replaceU`, `branchSum_replaceU`, `EU_replaceU`, `indiffU_eq_replaceU` | corr-refs-010 / fallenstein-2014 (both utilities) | the cell-replacement pattern; `∑_R p best = p(R) E[u ∣ R']`; the §3 utility is `replaceU U_N U_S Press Pressᶜ` | D / L | exact | — | `wireU`, `indiffU` | proved |
| `Wire.wireU`, `wireQ` | fallenstein-2014 "Stochastic events" | his second utility; his `q` as a FAF `Distr` under `0 < p((1,0))` (direct construction; equality with `Distr.mix` of the two conditionals not proved) | D | exact (construction disclosed) | — | `Wire.Instance.MInd`, `wireDriveM` | proved |
| `Wire.EU_wireU_eq_expect_wireQ` | fallenstein-2014 ("maximizes the expectation of `u` with respect to `q`") | `E[U ; a] = E_q[best_u]` | P | exact | — (`h` the junk guard) | `Wire.Instance.no_drive` (the package inhabited, value `1/3`); `Wire.wire_drive` | proved |
| `Wire.expect_wireQ_sub_EU` | mandate X2 (the decomposition) | `E_q − E_p = p(s=1)(E[u ∣ (1,0)] − E[u ∣ s=1])` | L | exact | — | — | proved |
| `Wire.expect_wireQ_eq_EU_of_independent` | fallenstein-2014 (the open mini-question) | under `p = p_x ⊗ p_{sy}` and `u` ignoring `x`: `E_q[best_u] = E_p[best_u]`, no drive | P | exact (finite model; the source's displayed independence condition is mis-stated, F11 — the Lean renders the prose) | — (independence: the source's one stated assumption; `u` ignores `x`: the mandate's X2 addition, exactly the residual of `expect_wireQ_sub_EU`) | `Wire.Instance.no_drive` (`p_x = (½, ½)`, `p(s = 1) = 1/3`, `u = [s]`, `p((1,0)) = 1/6`; both sides `1/3`); `Wire.x_drive` (the guard is load-bearing) | proved (the open question answered as: under independence the drive is exactly the `x`-residual `p(s=1)(E[u ∣ (1,0)] − E[u ∣ s=1])` of `expect_wireQ_sub_EU`, zero when `u` ignores `x`; without that a drive exists — audit r2 adversarial N-5) |
| `Wire.x_drive` | fallenstein-2014 (the businessperson who bets on the signal; the open mini-question); audit r2 adversarial N-5 (the auditor's probe) | on the uniform four-cell law (independence holds, `p_x = p_{sy} = ½`) with `u = [x = 0]`, which reads `x`: `E_q[best_u] − E_p[best_u] = 1/4` (`3/4` vs `1/2`) — a drive under independence alone | N+ | exact | — | itself | proved |
| `Wire.wire_drive` | fallenstein-2014 ("Is this bad?": the device that makes `x` true unless the agent wins); mandate T9 consequence (a) | on the wire model, for every `ε ∈ (0,1]`, `π`, `v`: `EU ticket = ε π`, `EU drive = π` — the T8-shaped drive | N+ | exact | — | itself | proved |
| `Wire.sxU`, `EU_sxU_eq_condVal` | fallenstein-2014 (the `s = x` variant; mandate T9) | the `s = x` utility in the source's own cell-replacement pattern; `E[U ; a] = E[u ∣ s = x ; a]` (unconditional as an equation; junk `0` at `p(s = x) = 0`, disclosed) | D / L | variant: the printed display's two conditioning events swapped back (F12) | — | `sx_display_witness` (value `1`) | proved |
| `Wire.sxUDisplayed`, `EU_sxUDisplayed`, `sx_display_witness` | fallenstein-2014 (the third displayed `U`, verbatim) | the display as printed has `E[U ; a] = ∑_{s=x} p best_u + p(s≠x)(E[v ∣ s≠x] − E[v ∣ s=x] + E[u ∣ s≠x])`, not `E[u ∣ s = x]`: on the uniform four-cell law with `u = [s = x]`, `v = 0` it is `1/2` while `E[u ∣ s = x] = 1` | D / L / N+ | exact (to the print) | — | `sx_display_witness` | proved; the printed display **refuted** as a rendering of the prose (F12): "makes the agent act as if it's maximizing … with respect to `p(· ∣ s = x ; a₁)`" — reading fixed: true for the corrected `sxU`, false for the display as printed; surviving neighbour: `EU_sxU_eq_condVal` |

## S13, S9 — stretch

| Declaration | Source | Claim | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Critiques.sup_affine_convex` | corr-refs-021 | `p ↦ max_a (p v_a + (1 − p) w_a)` is convex (chord form) | L | exact | — | — | proved |
| `Critiques.good_refinement` | corr-wf13-046 / armstrong.md I6.2 | `max_a E[u_a ∣ π] ≤ E[max_a E[u_a ∣ π'] ∣ π]` for `π'` refining `π` | C | exact | — | — (hypotheses trivially satisfiable; `Estimators.tower_instance` inhabits a strict refinement, no `good_refinement` value computed on it) | proved |
| `Critiques.mixture_identity`, `mixture_identity_certain` | corr-wf13-047 / armstrong.md I13.2 | `P(Pr) P(W ∣ Pr) + P(¬Pr) P(W ∣ ¬Pr) = ε`; the certain-update case | L | variant: the two-state formulas inlined by hand, not stated over `twoState` (audit r1 NB-9) | — | themselves | proved |
