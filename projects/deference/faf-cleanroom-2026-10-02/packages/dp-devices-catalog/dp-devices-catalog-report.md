# dp-devices-catalog — report

Formalizer: Fable 5.1 [scrubbed], 2026-09-30. Mandate: `dp-devices-catalog-mandate`. Ledger: [dp-devices-catalog-ledger](dp-devices-catalog-ledger.md). Findings: [dp-devices-catalog-findings](dp-devices-catalog-findings.md). Open list: `packages/dp-devices-catalog/dp-devices-catalog-open.txt`. Lean: `Cleanroom/Decision/DpDevicesCatalog/` (root module `Cleanroom/Decision/DpDevicesCatalog.lean`, namespace `Cleanroom.Decision.DpDevicesCatalog`). Depends on `dp-core-tree`, `dp-calibration`, `dp-local-opt` (imported file by file). **FAF objects: none** (the plan and every survey agree; this package is over `dp-core-tree`'s trees, `dp-calibration`'s states and senses, `dp-local-opt`'s evaluators).

## State of the package

*(updated as sections land; the last line of this block is the current status)*

- 2026-09-30: T1–T8 core done, T11(d) core done, the extension proved (both directions, `ε`-free), T9 five rows (three in all seven columns), T11(b)–(c), T12; **gate PASS** (`scripts/wp-audit` on the 18 modules incl. the root, run after the last Lean edit: 3233 declarations audited transitively, standard axioms only, no `sorry`; 307 own top-level declarations in 5280 lines). Open list empty. Not done (stretch, recorded below): T10 (ZO-3's per-occurrence state, ZO-11, Parfit/doppelgänger trees), T11(a), T13, D4 on the AMD, D1 and D3 on TN-V2, T7(g)'s `k`-fold pins.
- 2026-09-30, repair round 1: the one blocking issue (B1, SL-17's docstrings/findings) fixed — docstrings quote SL-17's definitional sentence in full and say the package renders its applications; findings F12 records the source's self-contradiction; `Trap`'s way out now has to be κ-calibrated (witnessed by the new label `tysStateWayOut` for masked, `tysState` for limit); the Definition-16 form shipped (`FailsRegardlessOfLabelEv`, `tys_masked_fails_ev`, `tys_limit_fails_ev`); plus the cheap non-blocking fixes and three small pushes (`selTree_approved_iff_any`, `miniature_fixedEps_tie_state_iff`, the `tysObsAlt` `N+` for the vacuity criterion). Gate after the repair: PASS, 3274 declarations (`## Repair round 1`). Last edit: this report.

## Modelling choices (disclosed once)

1. **Scalars are `ℚ`** for every catalogue statement (`Fidelity: variant: payoffs in a linearly ordered field`), inherited from `dp-core-tree`'s catalogue; stated in the module docstring of `Values.lean`.
2. **Procedures on multi-point trees are parametrised by one number per point**: `tnProc x y` (probability of `large` at `d_F`, `d_E`), `tysProc u v` (mass on `ten` at `d₅`, `d₁₀`), `proc2 p q` (dp-local-opt) on `Pt2`, `procQ q` on one-point trees. The lemmas `Proc.tnPt_eq_tnProc`, `Proc.five10_eq_tysProc`, `Proc.unit_eq_procQ` show every procedure is one of these, so every "for every procedure" claim is discharged by the parametrised statement plus the lemma.
3. **Conditionals are cross-multiplied** (STANDARDS §3): `MyopicallySatisfiedAt` is division-free; the null-deviation reading is disclosed in its docstring. Where a definition of record from dp-calibration already divides (`condExp`, `limitVal`), every use here carries the positivity / tremble-realizability guard as a hypothesis or a proved lemma (`condExp_const`, `limitVal_of_const`, `limitVal_of_pos` in `Devices.lean`).
4. **Every AMD statement names its action-event encoding** (last-draw `amdActEvLast`, first-draw `amdActEvFirst`, the grid's unrecorded encoding `amdActEvUnrec` rendered as empty events); every "none"/"every `q`" cell is a universal over `q ∈ [0,1]` and small `ε`, never sample points.
5. **Remark 3.14's definitions are this package's proposal** (SL-17 is an ADOPT amendment, not v2 text): `FailsRegardlessOfLabel`, `FailsRegardlessOfLabelEv`, `Trap`, `Dilemma` carry `Source: sl-amendments SL-17 (proposed Remark 3.14)`, with the class indexed by the instantiation (the zero-respecting class depends on the labels) and "makes the good outcome inconsistent" rendered both as `V < v` (value form) and as `ν(X) = 0` (Definition-16 form; on `B_P` the second implies the first). `Trap` and `Dilemma` render SL-17's three *applications*, not its definitional sentence, which contradicts them (findings F12; the docstrings quote the sentence in full); `Trap`'s way out must itself be κ-calibrated where it attains the outcome (repair round 1).

## T1 — The value-polynomial library (`Values.lean`)

Reuse (cited, not restated): `amd_value`, `amd_value'`, `miniature_value`, `mug1_value`, `mug2_value` (dp-core-tree / dp-calibration), `twoPoint_value`, `amdShape_value`, `mergedStag_value`, `twoStag_value`, `kfold_*_value`, `deathDamascus_value`, `threeCoal_value_prof` (dp-local-opt).

New, each derived from the tree by `value_decision`/`value_chance`/`value_leaf` then `ring` (kind `P`, no hypotheses beyond the parameter bounds):

| Tree | Declaration | Closed form |
|---|---|---|
| `tnV1 p L S` under `tnProc x y` | `tnV1_value` | `x·[p(L + (1−x)S) + (1−p)(1−y)S] + (1−x)·[(1−p)(L + (1−x)S) + p(1−y)S]` |
| `tnV2 p L S` under `tnProc x y` | `tnV2_value` | `xy·[p(L + (1−x)S) + (1−p)(1−y)S] + (1−xy)·[(1−p)(L + (1−x)S) + p(1−y)S]` |
| `toldYouSo` under `tysProc u v` | `toldYouSo_value`, `toldYouSo_value_all` (every `C`) | `5(1−u) + u(10v + 5(1−v))` |
| `selectionForcing ua ub ra rb` under `procQ q` | `selectionForcing_value`, `selectionForcing_value_all` | `⅓(q ua + (1−q) ub) + ⅓ ra + ⅓ rb` |
| `treeJ` under `procQ q` | `treeJ_value` | `q + 4q(1−q)` |
| `routingRoot`, `gate`, `coinQuery` (every `C`) | `routingRoot_value`, `gate_value`, `coinQuery_value` | `0` (kind `T`: all leaves pay `0`) |
| `opaqueNewcomb p L S` under `procQ q` | `opaqueNewcomb_value` | `L(qp + (1−q)(1−p)) + (1−q)S` |
| `tickle ρ γ₁ γ₀ α β` under `procTickle q₁ q₀` | `tickle_value` | `ρ(q₁α − γ₁β) + (1−ρ)(q₀α − γ₀β)` |
| `fantasy241`, `fantasy541`, `fr12`, `threat` under `proc2 p q` | `fantasy241_value`, `fantasy541_value`, `fr12_value`, `threat_value` | instances of `twoPoint_value` |

Infrastructure: `FinDistr.box`, `FinDistr.five10`, `tnProc`, `tysProc`, `Proc.tnPt_eq_tnProc`, `Proc.five10_eq_tysProc`, `procBoth_eq`, `procLarge_eq`, `tnProc_deviate_E/F`.

## T2 — Proposition 9 (`TransparentNewcomb.lean`)

- Table: `tnV1_value_11/12/21/22`, `tnV2_value_11/12/21/22` (kind `N+`, instances of T1).
- `tnV1_12_dominates_11` (`P`): `V(1,1) ≤ V(1,2)`, strict iff `p < 1` (hyp `0 < S`).
- `tnV1_pureOpt_iff` (`P`): with `L > S > 0`, `½ < p`: `(1,2)` is a maximiser among the four pure policies iff `(2p−1)L ≥ pS`; `(2,2)` iff `(2p−1)L ≤ pS`. v2's "iff `(2p−1)L > pS`, else `(2,2)`" is this pair with the boundary a tie.
- `tnV1_empty_box_one_boxers` (`P` + refutation): "no optimal V1 policy one-boxes at the empty box" holds for `p < 1`; **at `p = 1` it fails**: `(1,1)` ties `(1,2)` at `L` (findings F4).
- `tnV2_pureOpt_iff` (`P`): `(1,1)` is the unique pure maximiser iff `(2p−1)L > S` (hyp `0 < S`).
- `tnV2_emptyBox_deviation_cost` (`P`): `V(1,1) − V(1,2) = (2p−1)L − pS`, positive under `(2p−1)L > S`.
- `tn_instance_values` (`N+`): at `(¾, 4, 1)`: V2 `3, 7/4, 5/4, 2`; V1 `3, 13/4, 5/4, 2`. The mandate's `5/2` for V2's `(1,2)` was a slip (`(1−p)L + pS = 7/4`).
- **T2s** `tnV2_large_isOptimal` (`P`, hyps `0 < S`, `½ ≤ p ≤ 1`, `(2p−1)L > S`): `(1,1)` is `IsOptimal` among *all* procedures — from the full polynomial via `pL − V(x,y) = ((2p−1)L − S)(1−xy) + S·[(1−p)x(1−y) + py(1−x) − (2p−1)xy(y−x)]`, the bracket nonnegative (`tnV2_mixed_key`). The maximum is at a vertex.
- **T2s contrast** `tnV1_mixed_beats_pure` (`N+`): in V1 at `p = 1`, `L = 3/2`, `S = 1` the mixed `(9/10, 0)` has `V = 77/50 > 3/2`, the maximum of the four pure values — Proposition 9's "optimum" does **not** extend to mixed policies in V1 (findings F5). `tnV1_large_not_isOptimal` (`N+`): V1's one-boxer is not optimal for `p < 1`.

## T3 — Proposition 10 (`TransparentNewcomb.lean`)

- `MyopicallySatisfiedAt obs C B d` (`D`): `0 < ν_C(O_d) ∧ ∀ a, paySum_{C[d↦a]}(O_d)·ν_C(O_d) ≤ paySum_C(O_d)·ν_{C[d↦a]}(O_d)`. Null-deviation reading disclosed in the docstring; on V2 with `p > 0` every deviation realizes `O_E` (`tnV2_nu_E`), so it is not exercised.
- `tnV2_nu_E` (`L`): `ν_{(x,y)}(O_E) = xy(1−p) + (1−xy)p`; `tnV2_paySum_E` (`L`): `paySum(O_E) = ν(O_E)(1−y)S`.
- (iii) `tnV2_nu_E_11_12` (`P`): `1 − p` and `p`. Conditional masses `tnV2_paySum_E_11_12` (`P`): `0` and `S·ν`.
- (i) `tnV2_large_not_myopic` (`P`, hyps `0 < p < 1`, `0 < S`).
- (ii) `tnV2_myopic_imp_both` (`P`, **every procedure**, T3s done): myopic satisfaction forces `y = 0`; `tnV2_both_value_le` (`P`): `V(x, 0) ≤ (1−p)L + S`, and `(1−p)L + S < pL ↔ (2p−1)L > S`; `tnV2_myopic_pure` (`C`): v2's pure statement as a corollary.
- `tnV2_wedge_instance` (`N+`) at `(¾, 4, 1)`.

## T4 — Remark 7.1 and ZO-9 (`TransparentNewcomb.lean`)

- `tnV2_occ_E` (`P`): `occ(d_E) = univ`, from the tree; `tnV2_mass_occ_E`, `tnV2_offOcc_E` (`L`).
- `tnV2_ssaValue_E` (`C`, no hypotheses): `ssaValue C B d_E m = V(C[d_E ↦ m])` for every `C`, `m` — **Remark 7.1's content** (via `ssaValue_eq_div`, `value_deviate_eq_ssaNum_add_offOcc`).
- `tnV2_large_coherentAt_E` (`P`, hyps `0 < S`, `½ ≤ p ≤ 1`, `(2p−1)L > S`): `(1,1)` is `CoherentAt … E` (mixed Definition 22); the docstring cites `coherentAt_iff_ssa` for the reading as Theorem 2's verdict.
- ZO-9: `zo9Proc`, `zo9Tree`, `zo9PerRunState` (prior-calibrated = per-run at `d_E`), `zo9MaskedState`; `zo9_perRunSSCAt` (`N+`: per-run SSC at `E`, masses `½, ¼, ¼`), `zo9_act_values` (`T`: `8/3, 1` vs `0, 1`), `zo9_maskedOCAt` (`L`). The two labellings are states over one tree; the content is the two value pairs.

## T5 — Told-You-So (`ToldYouSo.lean`, `Remark314.lean`)

Inherited (cited, not re-proved): `tys_fiveTen_strictOC/maskedOC/limitOC`, `tys_take10_strictOC/limitOC`, the refuted masked clause `tys_take10_not_maskedOCV` (dp-calibration F2).

- (a) `tys_value_of_zeroRespecting` (`P`, hyp (a) zero-respecting for `tysState`): `V = 5` for **every** zero-respecting procedure (`A⁺_{d₅} = {five}` forces `C(d₅)(ten) = 0`); `tys_value_of_take10` (`P`): `V = 10`; `procFiveTen_value`, `procTake10_value` (`N+`); `procTake10_isOptimal` (`P`, no hyps): `C*` is `V`-optimal (`5(1−u) + u(10v + 5(1−v)) ≤ 10` on `[0,1]²`).
- (b) `procFiveTen_not_coherentPureAt_five` (`P`): deviation `d₅ ↦ ten` gives `10 > 5` (`procFiveTen_deviatePure_five_ten : C₀[d₅ ↦ ten] = C*`); `procTake10_coherent` (`C`, from optimality); Theorem 1: `tys_siaSum_five` (`P`, every `C`: `Φ(five) = 5`, `Φ(ten) = 10 C(d₁₀)(ten) + 5 C(d₁₀)(five)`), `tys_siaSum_ten`, `procFiveTen_sia_five` (`5` vs `10`, `¬ Thm1At`), `procFiveTen_tremble_sia_five` (`5` vs `10 − 5ε/2` under `C₀^ε`, the source's number derived); Theorem 2: `tys_occ_five`, `tys_ssaValue_five` (`ssaValue = V(C[d₅ ↦ m])`), `procFiveTen_ssa_five` (`5` vs `10`). **The bridge** `fiberForced_eq_siaSum` (`L`): dp-calibration's D3/D3⁰ functional is dp-local-opt's `siaSum`, so `occEdtConsistent_iff_thm1` (D3⁰ = Theorem 1) and `occTrembleEdtConsistent_iff` (D3 = Theorem 1 under `C^ε`); `procTake10_occEdtConsistent` (`P`: `C*` satisfies D3⁰, `C₀` does not); `procTake10_occTrembleEdtConsistent` (`P`: `C*` satisfies D3 at every `ε ∈ (0,1]`; the `d₅` comparison at `ε = 1/100` is `5` vs `399/40`).
- (c) `procFiveTen_d2At` (`P`): D2's body holds for `C₀` at every `ε ∈ (0,1]`; `procTake10_not_d2At` (`P`): fails for `C*` at every `ε` — `ν_{C*^ε}(ten ∧ O₅) = 0` while `ν_{C*^ε}(five ∧ O₅) = ε/2 > 0`, so the escape clause does not fire and `A⁺_{d₅}(ε) = {five} ⊉ {ten}`; `tys_d2_inverts` (`P`): `EventTrembleEdtConsistent` for `C₀`, not for `C*`. **Findings F1**: v2 §7.1 remarks (2)/(4) presuppose a draw-conditioned evaluator (D3), for which the verdict is the opposite (`procTake10_occTrembleEdtConsistent`). Supporting: `tys_tremble_nu_five/ten`, `tys_tremble_condExp_ten` (`10` vs `5` at `d₁₀` under every tremble), `tys_nuPoly_obs_five/ten_ne_zero`.
- (d) Remark 3.14 (`Remark314.lean`): definitions `FailsRegardlessOfLabel`, `Trap`, `Dilemma` (`D`, this package's proposal); the label lemmas `tys_maskedOCAt_five_pr` (`P`, every `C`, every `s`: masked-calibrated ⟹ `P_{s₅} = δ_{(5,5)}`; the vacuity disjunct is impossible since the uniform self-model realizes `O₅`) and `tys_limitOCAt_five_pr` (`P`: limit-calibrated ⟹ `P_{s₅} = δ_{(5,5)}`, via `nuPoly(X ∩ O₅) = [(5,5) ∈ X]·nuPoly(O₅)`); the verdicts `tys_strict_dilemma` (`N+`: at the label `π = 1`, `tysStateOne`, the member `C*` is zero-respecting, strictly calibrated — Definition 8 vacuous at `d₅` — and attains `10`), `tys_strict_not_fails`, `tys_masked_trap` and `tys_limit_trap` (`P`: every member gets `5 < 10` at every calibrated label — in the Definition-16 form `ν(m=10) = 0`, `tys_masked_fails_ev`/`tys_limit_fails_ev`, from which the value form follows on `B_P`, `tys_failsEv_imp_fails` — while `C* ∉ 𝒞` attains `10` at a label at which it is itself calibrated: `tysStateWayOut` with `procTake10_maskedOC_wayOut` for masked, `tysState` with `tys_take10_limitOC` for limit); `tys_masked_wayOut_everywhere`/`tys_limit_wayOut_everywhere` (`P`: at *every* calibrated instantiation, for any procedure, `C*` is outside the class and attains `10`); `tys_masked_limit_not_dilemma`, `Trap.not_dilemma`. The definitions render SL-17's applications, not its definitional sentence (F12). D1 (CA-17′): `procFiveTen_limitStateEdt` (`C`: D1 approves `C₀` with `tysState`), `procTake10_not_limitStateEdt` (`P`: D1 rejects `C*` with **every** state assignment — the limit state at `d₅` is certain of `m = 5`).

## T6 — The miniature and selection forcing (`Miniature.lean`, `Selection.lean`)

Cited: `miniState_V_a/b`, CA-13′'s set (`miniature_tEdt_pure_a/b`, `miniature_tie_approved`), `miniature_not_eventTremble` (D2 empty, the faithful no-fixed-`q` form), `miniature_adviceEdt_iff` (D4 = `{2/3}`), `sel_compare`, `sel_edt_no_fixed`, `sel_aPlus`.

- (a) `qeps`, `miniature_tremble_act_values` (`P`: `2(1 − q_ε)`, `q_ε` derived from `calibratedState (tremble (procQ q) ε) miniature ⊤` via `miniState_V_*`), `FixedEpsTie` (`D`), `qstar`, `miniature_fixedEps_tie_iff` (`P`: tie iff `q = (4−3ε)/(6(1−ε))`), `qstar_mem` (`P`: `∈ [2/3, 1]` for `ε ≤ ½`; `qstar_values`: `3/4`, `5/6`), `qstar_injective` (`P`).
- (b) `FloorRatifiable` (`D`, on the miniature's two act values, disclosed), `floorRatifiable_iff_small` (`P`: exactly `2/3` for `0 < ε ≤ 1/3`), `floorRatifiable_iff_corner` (`P`: exactly the corner `1 − ε` for `1/3 < ε ≤ ½`) — **dp-sl-2-014's UNREVIEWED detail confirmed**; `floorRatifiable_instance` (`N+`, `ε = 2/5`, `q = 3/5`); `two_devices_differ` (`N+`: at `ε = 1/3` the two devices select `3/4` vs `2/3`, at `2/5` they select `7/9` vs `3/5`).
- (c) `miniature_siaSum` (`P`: `3(1−q)`, `3q`; difference `V'(q) = 3 − 6q`), `miniature_tie_equilibrium_not_optimum` (`N+`: `V(2/3) = 2/3 < 3/4`; `¬ Thm1At`, `¬ CoherentAt`, `CoherentPureAt` at `2/3`).
- (d) `selectionForcing_sum/nu/paySum/condExp/nu_act_pos` (general parameters), `selTree_approved_iff` (`P`: strictly-calibrated-and-approved iff `q = 7/11`; both pure labels rejected because `A⁺ = A`), `selTree_tremble_condExp`, `selTree_forced_tremble_diff` (`P`: at `q = 7/11` the trembled difference is exactly `1210ε/(3(12−ε)(10+ε)) > 0`), `selTree_not_eventTremble` (`P`: D2 empty for every `q ∈ [0,1]`), **stretch** `selSym_eventTremble_iff` (`P`: on `(−20,−20;10,10)` D2 = `{½}` exactly).

## T7 — The mugging (`Mugging.lean`)

Cited: `mug_maskedOC_all`, `mug1_masked_not_strict`, `mug1_perRun_not_strict`, `mug1_occ`, `mug1_value`, `mug2_value`, `mug1_nu`, `mug2_nu`, `no_uniform_optimum`. New infrastructure: `mug1_count` (`#_d ≡ 1`), `mug1_countMass` (`= ν`), `mug1_paySum`, `mug2_paySum`, `mugH`, `mug1_nu_H` (`= ½`).

- (a) `mug1_strictOC_iff` (`P`): strict at `d` for `procQ q` iff `q = q₀`.
- (b) `mug1_not_perRunSSC_all`, `mug1_not_perOccSSC_all` (`P`, every procedure).
- (c) FP-1 for every state: `mug1_strictOCAt_H_zero`, `mug1_limitOCAt_H_zero`, `mug1_maskedOCAt_H_zero` (`P_s(H) = 0`), `mug1_perRunSSCAt_H_half`, `mug1_perOccSSCAt_H_half` (`P_s(H) = ½`) — all `P`/`C`, hypothesis = the sense at `d`.
- (d) FP-2 typed: `mug1_strict_states_agree` (`L`, via `strictClausesAt_unique`), `mug1_strictOCAt_transfer_invisible` (`P`: a strict state for `(C, B₁(x,y))` is one for `(C, B₁(x,y'))`).
- (e) FP-4: `thirdCarrier` (`D`, the pushforward to `MugW`), `thirdCarrier_value` (`T`: `½(y−x)`), `mug1_nu_H_pay_zero` (`T`: the event `H ∧ pay` is empty on this carrier) — **findings F8**: dp-cf-2-013's carrier presumes the 12-atom product algebra; on the four-world carrier the "uncalibratable" clause is trivial.
- (f) `mug_fp6` (`N+`): `mugState1` and `mugState2` `Agree`; `V_{B₁} − V_{B₂} = y(2q−1)/2`, so the values differ iff `q ≠ ½` — **findings F7** (the mandate's "every interior `q`" is a slip).
- (g) `AnthropicIndiff` (`D`, `P_s ≪ μ(· ∣ occ(d))` as support inclusion), `perRunClause1_imp_anthropicIndiff` (`P`, hyp `0 < μ(occ(d))`), `mugState1_anthropicIndiff` (`N+`), `mugState1_density_bound_fails` (`N−`: `q₀ ≤ q₀/2` fails at `tPay`). ID-16's `k`-fold pins: not done (needs a world-typed `k`-fold; recorded).

## T8 — The device table (`Devices.lean`, `TableMugging.lean`, `TableNewcomb.lean`, `TableToldYouSo.lean`, `AmdDevices.lean`)

General lemmas (`Devices.lean`, `L`): `condExp_const` and `limitVal_of_const` (an event whose leaf-worlds all pay `c` has conditional value and tremble-limit value `c`), `limitVal_of_pos`, `nu_pos_of_leaf(_fullSupport)`, `nuPoly_ne_zero_of_leaf`, `nuPoly_eq_zero_of_no_leaf`. Every D2/D4 cell below is derived from the tree through these (no act value is an input).

**The filled table** (source `calibration.md:88–98`; each cell gives the Lean name; "universal" = a theorem quantified over every label/procedure, not the source's sample points):

| device | mugging `{pay, refuse}` (`0 < x < y`) | AMD `{δ_a, δ_b, ⅓, ⅔}` (last-draw events) | TN-V2 at `(¾, 4, 1)` `{(1,1),(2,2),(1,2)}` | Told-You-So `{C₀, C*}` |
|---|---|---|---|---|
| D1 limit-state EDT | pay, refuse; every mixed `q` rejected — `mug1_limitStateEdt_pure`, `mug1_not_limitStateEdt_interior` (universal) | `δ_a, δ_b` — **skipped** | all three — **skipped** | `C₀` — `procFiveTen_limitStateEdt`; rejects `C*` for every state — `procTake10_not_limitStateEdt` |
| D2 event-tremble EDT | refuse — `mug1_eventTremble_iff` (`↔ q = 0`, universal) | none — `amd_last_not_eventTremble` (universal in `q`); first-draw: `δ_b` — `amd_first_eventTremble_iff`; unrecorded: every `q`, vacuously — `amd_unrec_eventTremble` | `(2,2)` — `tnV2_eventTremble_iff` (`↔ C = procBoth`, every procedure, every `0 < p < 1`, `S > 0`); the optimum is D2-inconsistent — `tnV2_optimum_d2_inconsistent` | `C₀` — `tys_d2_inverts` |
| D4 advice EDT | refuse — `mug1_adviceEdt_iff` (universal) | `⅔` — **skipped** | `(2,2)` — `tnV2_adviceEdt_iff` (every procedure) | `C₀` — `tys_adviceEdt_iff` (every procedure) |
| D3, `ε > 0` | pay — `mug1_occTremble_iff` (universal) | none — `amd_not_occTremble` (universal; the source's `133/50` vs `267/100` at `ε = 1/100` is `amd_d3_at_hundredth`) | **skipped** | `C*` — `procTake10_occTrembleEdtConsistent` (`5 < 399/40`) |
| D3⁰ Theorem 1 | pay — `mug1_occEdt_iff` (universal) | `⅓` — `amd_thm1At_iff` (dp-local-opt) via `occEdtConsistent_iff_thm1` | `(1,1)` (`6` vs `19/4`; `3` vs `5/4`), `(2,2)` (`3` vs `13/4`; `2` vs `11/4`), not `(1,2)` (`11/4` vs `3`) — `tnV2_thm1_cells`, from `tnV2_siaSum` (general polynomial) | `C*`, not `C₀` — `procTake10_occEdtConsistent` |
| Dev pure | pay — `mug1_coherentPureAt_iff` | `[0, ⅔]` — `amd_coherentPureAt_iff` | `(1,1)`, `(2,2)` — implied by the mixed row | `C*`; not `C₀` — `procFiveTen_not_coherentPureAt_five` |
| Dev mixed | pay — `mug1_coherentAt_iff` | `⅓` — `amd_coherentAt_iff` | `(1,1)`, `(2,2)`, not `(1,2)` — `tnV2_coherent_cells` | `C*` — `procTake10_coherent`; not `C₀` — `procFiveTen_not_coherent` |
| `V`-optimal | pay — `mug1_isOptimal_iff` | `⅓` — `amd_isOptimal_iff` | `(1,1)` only — `tnV2_isOptimal_cells` | `C*` — `procTake10_isOptimal`; not `C₀` — `procFiveTen_not_isOptimal` |

Notes. (i) The two "exploration" devices give opposite verdicts on the mugging (D2 refuse, D3 pay) and on Told-You-So (D2 `C₀`, D3 `C*`): ZO-18's warning made into theorems. (ii) TN-V2's D2 and D4 rows are universal in the procedure *and* the parameters: the act-conditional values at `d_F` are `L` vs `L + S` and at `d_E` `0` vs `S` under every tremble (`tnV2_tremble_condExp`), so no procedure with `large` in any support survives. (iii) The AMD's D2 cell is encoding-dependent, as F10 of dp-calibration said: last-draw none, first-draw `{δ_b}`, unrecorded every `q` (vacuous). (iv) Skipped: D4 on the AMD (needs second-order coefficients of `nuPoly`/`payPoly` at the boundary labels; the interior case would follow from `limitVal_of_pos` + `amd_last_condExp`), D1 and D3 on TN-V2.

## Extension — the vacuity criterion (`Grid.lean`)

The package's one theorem, proved in both directions and `ε`-free:

- `D2BodyAt` (the body of D2 at one point; `d2At_iff : D2At ↔ ∀ d ∈ queried, D2BodyAt`), `D2VacuousAt` (the escape clause fires: no `a ∧ O_d` realized under `C^ε`), `D2VacuousAt.body` (a vacuous point satisfies the body).
- `d2VacuousAt_iff` (`P`, no hypotheses): for any `ε ∈ (0,1]`, `D2VacuousAt … ε d ↔ ∀ a ℓ, Positive B ℓ → world B ℓ ∉ actEv d a ∩ obs d`. Proof: under a full-support tremble a chance-positive leaf has positive mass (`leafLaw_pos_of_fullSupport`), and a chance-null leaf has mass `0` under every procedure (`leafLaw = chanceWeight · drawsWeight`).
- `d2VacuousAt_eps_free` (`C`): "for all sufficiently small `ε`" ⟺ the same tree-level condition. So vacuity of a D2 cell is a property of `(B, obs, actEv)` alone — independent of the procedure and of the tremble size.
- `eventTremble_of_unrealised` (`C`): if the condition holds at every queried point, **every** procedure is D2-consistent — the dryness finding as a theorem.
- The guarded senses: `nu_eq_zero_iff`, `strictOCAt_vacuous_iff` (`L`: `StrictOCAt` is vacuous at `d` iff no positive-mass leaf lies in `O_d`, a property of `(B, C)`), `strictOCAt_of_vacuous`.
- Instances: `amdActEvUnrec` (`D`, the grid's unrecorded encoding rendered as empty action events; any events disjoint from the leaf-worlds behave alike), `amd_unrec_d2Vacuous`, `amd_unrec_eventTremble` (`N−`: "the AMD is event-tremble-EDT-consistent at every `q`" — vacuously), `grid_amd_unrec_vac`.

The converse the mandate anticipated as the likely OPEN item is proved; the open list is empty.

## T9 — The three-valued grid (`Grid.lean`)

`Verdict` (`T | Tstar | vac | F`, `D`) and `GridVerdict Q ok vac : Verdict → Prop` (`D`), ZO-19's reading rule: `T` = all queried points satisfy `ok` and are non-vacuous; `T*` = all `ok`, some vacuous, some not; `vac` = all vacuous; `F` = some point violates `ok`. Each column instantiates `(ok, vac)`: strict `(StrictOCAt, ν(O_d) = 0)`, masked `(MaskedOCAt, no admissible self-model realizes O_d)`, limit `(LimitOCAt, nuPoly(O_d) = 0)`, per-run `(PerRunSSCAt, μ(occ) = 0)`, per-occurrence `(PerOccSSCAt, 𝔼[#_d] = 0)`, `T_EDT` `(TEdtAt, A⁺ = ∅)`, trembleEDT at `ε` `(D2BodyAt, D2VacuousAt)`.

Rows shipped (kind `T`, each a theorem stating the printed verdict):

| row | strict | masked | limit | per-run | per-occ | `T_EDT` | trembleEDT |
|---|---|---|---|---|---|---|---|
| Told-You-So, `C₀` | `T*` `grid_tys_fiveTen_strict` | `T*` `grid_tys_fiveTen_rest.1` | `T` `grid_tys_limit.1` | `T*` `grid_tys_fiveTen_rest.2.1` | `T*` `grid_tys_fiveTen_rest.2.2` | `T` `grid_tys_tEdt.1` | `T` `grid_tys_tremble.1` (every `ε`) |
| Told-You-So, `C*` | `T*` `grid_tys_take10_strict` | `F` `grid_tys_take10_rest.1` | `T` `grid_tys_limit.2` | `F` `grid_tys_take10_rest.2.1` | `F` `grid_tys_take10_rest.2.2` | `F` `grid_tys_tEdt.2` | `F` `grid_tys_tremble.2` |
| Remark 4.3 miniature, `q = 2/3` | `T` `grid_miniature_tie.1` | `T` `grid_miniature_tie_rest.1` | `T` `grid_miniature_tie.2.1` | `T` `grid_miniature_tie_rest.2.1` | `T` `grid_miniature_tie_rest.2.2` | `T` `grid_miniature_tie.2.2` | `F` `grid_miniature_tie_tremble` (every `ε ∈ (0,1)`) |
| `B₁` no-doubt mugging, `C = pay` (interior `q₀`) | `F` | `T` | `F` | `F` | `F` | `F` | `F` — all seven in `grid_mug1_pay` |
| AMD, any `q` (unrecorded encoding) | · | · | · | · | · | · | `vac` `grid_amd_unrec_vac` |

All seven columns of the three named rows and of the mugging row are shipped (`GridMore.lean`: the SSC clauses collapse to prior calibration where `#_d` is constant, `perOccClausesAt_of_priorCalibrated_of_count_const`; on `B_P` the `d₁₀`-occurrence is the `O₁₀`-event, `tys_countMass_ten`). The AMD rows' `·` (no states) are the grid's own. Not attempted: the other 69 rows (the extension replaces the enumeration for the `vac` cells).

## T10 — Remaining numeric witness tables (stretch)

Not done. ZO-3's per-run state on the AMD at `q = ¼` is already `amd_perRun_not_perOcc` (dp-calibration `Chain.lean`, masses `(¼, 3/16, 9/16)`); its per-occurrence state `(1/7, 3/14, 9/14)`, ZO-11 (TN-V1 masked at both points, SSC fails at `d_F`), Parfit and the doppelgänger trees are not shipped. ZO-10 needs `dp-referents-cdt`'s `UDT_{s°,ρ}` — recorded only.

## T11 — Vocabulary (stretch, except (d))

(d) **core, done** (`LabelReading.lean`): `exists_polynomial_nu_deviate` (`P`, **every** tree, no `QueriesExactly` hypothesis: `q ↦ ν_{C[d ↦ (q,1−q)]}(X)` is a polynomial), `no_mixing_detector_polynomial` (`P`), `no_mixing_detector` (`C`: no event of any Definition-6 tree has probability `𝟙[0 < q < 1]`), `probeB`/`probeTree` (`D`), `probeTree_nu` (`P`: `1 − q^k − (1−q)^k` for `k ≥ 1`, from Bernstein's partition of unity), `probe_instance` (`N+`: `58024/59049 > 49/50` at `q = 2/3`, `k = 10`), `probe_threshold` (`T`: `c ≥ 19683/29012`; dp-sl-065's "`c ≳ .68`" is this at `k = 10` and ill-posed without `k`).
(b) done (`Vocabulary.lean`): `ExpIdentifiable obs actEv C B d` (`D`: at every tremble-realizable act event within `O_d`, `limitVal` = `siaSum`; the forcing value is unnormalised, disclosed — equal to the normalised one when `𝔼[#_d] = 1`, as on both witnesses), `coinQuery_expIdentifiable` (`N−`: every payoff `0`), `mug1_not_expIdentifiable` (`N+`: `−x ≠ (y−x)/2` — D4 refuses, D3⁰ pays).
(c) done as a pointer catalogue in `Vocabulary.lean`'s module docstring, with one new declaration, `APlusNonempty` (A5); A3 = dp-core-tree's `mass_edge`/`node_mass_edge` (cited), A2 = `StrictOCAt`, A6 = `SelfTransparent`, A7 = `IsCalibrated`/`MakesInconsistent`, A1 = the two devices of T6; A4/A8/A9/A10 have no theorem (stipulations or declined referents).
(a) not done: `DecisionDetermined` and the sloppy-Omega witness. F3 located/dislocated: recorded only (dp-fairness-reloc not imported).

## T12 — Coupling-uncertainty refuser (`Coupling.lean`, thin by design)

`mug1_coupling_gap` (`T`: `V_{B₁(x,y)}(q) − V_{B₁(x,0)}(q) = qy/2`), `mug1_coupling_gap_zero_iff` (`T`: `= 0 ↔ q = 0`), `mug1_mixture_pays_iff` (`T`: the `π`-mixture pays iff `π > x/y`), `rootMug` (`D`) and `rootMug_value` (`T`: `(y−x)/2 = V_{B₁}(δ_pay)`). The learning claim is not in the type; recorded only.

## T13 — sl-workflow trees (stretch)

Not done (the announcement tree, the smoking-robots steelman).

## T14 — The candidate protocol (data)

`Template.lean`/`check.sh` of the cf-workflow are superseded by `scripts/lean-check`/`scripts/wp-audit`; nothing was ported.

## Reuse list (plan sub-targets already covered by existing declarations)

`amd_value`, `amd_value'`, `miniature_value`, `mug1_value`, `mug2_value`, `twoPoint_value`, `amdShape_value`, `mergedStag_value`, `twoStag_value`, `kfold_*_value`, `deathDamascus_value`, `threeCoal_value_prof` (T1); `miniState_V_a/b`, `miniature_tEdt_pure_a/b`, `miniature_tie_approved`, `miniature_not_eventTremble`, `miniature_adviceEdt_iff`, `sel_compare`, `sel_edt_no_fixed`, `sel_aPlus` (T6); `mug_maskedOC_all`, `mug1_masked_not_strict`, `mug1_perRun_not_strict`, `mug1_occ`, `mug1_nu`, `no_uniform_optimum` (T7); `tys_fiveTen_strictOC/maskedOC/limitOC`, `tys_take10_strictOC/limitOC`, `tys_take10_not_maskedOCV`, `tys_zeroRespecting` (T5); `amd_thm1At_iff`, `amd_coherentPureAt_iff`, `amd_coherentAt_iff`, `amd_isOptimal_iff`, `amd_siaSum_a/b` (T8, AMD); `tnV2_occ_F`, `tnV2_E_nu` (T4, whose hypotheses were checked: `tnV2_E_nu` is at `p = 1` for `procLarge.deviate .E m` only, so `tnV2_nu_E` here is the general statement), `amd_perRun_not_perOcc` (T10 ZO-3's per-run state).

## STANDARDS conflicts

None found. One mandate slip beyond those in findings: the mandate's `tnV1_pureOpt_iff` phrasing ("`(2p−1)L > pS ↔ (1,2) is the unique maximiser") is false at `p = 1` (a tie with `(1,1)`); shipped as the ≥/≤ pair plus a separate strictness statement (findings F4).

## Repair round 1

Audits: `dp-devices-catalog-audit-r1-fidelity` (verdict blocking, one issue B1, nine non-blocking N1–N9) and `dp-devices-catalog-audit-r1-adversarial` (verdict pass, eight non-blocking items). Repairer: Fable 5.1 [scrubbed], 2026-09-30, fresh context.

**B1 (fidelity) — `Trap`/`Dilemma` docstrings misquote SL-17 and the findings file omits SL-17's self-contradiction: fixed.** (a) The module docstring and the docstrings of `FailsRegardlessOfLabel`, `Trap`, `Dilemma` now quote SL-17's definitional sentence in full ("call the failure a *dilemma* rather than a *trap* if some procedure outside the class attains more") and say explicitly that the package renders the sentence's three *applications* ("a dilemma of selection", "a trap with a way out", "a trap and no dilemma" for a no-way-out tree is **not** rendered — such a tree is neither under the package's definitions), not the definitional clause; `Fidelity:` lines of `Trap` and `Dilemma` say `variant: SL-17's applications rather than its definitional clause`. (b) Findings F12 records the contradiction with the three applications quoted and the two well-posed readings (the package's, and the literal one under which `tys_masked_trap`/`tys_limit_trap` would be dilemmas and a no-way-out tree the only trap), with a proposed fix to SL-17's wording; F3 points to it. (c) Theorem names kept (`tys_masked_trap`, `tys_limit_trap`, `tys_strict_dilemma`), since the names are SL-17's own words for these cases. Also done in the same pass, as the auditor recommended: the way-out clause strengthened (N3, below).

**Non-blocking, fixed.**
- N3 / adversarial 7 (`Trap`'s way out carried no calibration requirement): `Trap` now requires the way out to be `κ`-calibrated at the instantiation where it attains `v` (`∃ I ∈ AP, ∃ C, C ∉ 𝒞 I ∧ IsCalibrated κ obs I.s C I.B ∧ v ≤ value C I.B`). Witnesses: for masked, the new label `tysStateWayOut` (`s₅ = δ_{(5,5)}`, `s₁₀` the `O₁₀`-conditional of `C*[d₁₀ ↦ uniform]`) with `procTake10_maskedOC_wayOut` (`N+`: `C*` *is* masked-calibrated there — the stipulated `tysState` is not, dp-calibration F2) and `procTake10_not_zeroRespecting_wayOut`; for limit, `tysState` with `tys_take10_limitOC`. The adversarial auditor's alternative strengthening (the way out at the *same* labels at which the class fails) is `tys_masked_wayOut_everywhere` / `tys_limit_wayOut_everywhere`: at every masked- (limit-) calibrated instantiation of `Σ_{B_P}`, for any procedure, `C*` is outside the zero-respecting class and attains `10`. `Trap.wayOut_value` recovers the old value-only clause; `Trap.not_dilemma`, `tys_masked_limit_not_dilemma` make the exclusivity explicit.
- N4 / adversarial 2 (Definition-16 form): `FailsRegardlessOfLabelEv κ obs AP 𝒞 X := ∀ I ∈ AP, ∀ C ∈ 𝒞 I, IsCalibrated … → ν_{C,I.B}(X) = 0`, with `failsRegardlessOfLabelEv_iff_makesInconsistent` (for a constant class it is Definition 16 with `δ = 0` member by member); `tys_masked_fails_ev`, `tys_limit_fails_ev` (every zero-respecting member has `ν(m=10) = 0` at every masked/limit-calibrated label); `tys_failsEv_imp_fails` (on `B_P`, `V = 5 + 5ν(m=10)`, so the event form implies the value form for any class and sense). The two trap theorems now derive their universal clause through the event form. `FailsRegardlessOfLabel` keeps the value form as the definition the verdicts are stated in, with the docstring saying why both exist.
- N1 (`selTree_approved_iff` fixes the state): `selTree_approved_iff_any` — some state assignment is strictly calibrated for `procQ q` at `⊤` and `T_EDT`-approves it iff `q = 7/11` (via `strictClausesAt_unique` and the fact that `T_EDT` reads only `P_s`/`V_s` on the two act events, both `P_s`-positive); the original's docstring says why the fixed state is without loss.
- N2 (`FixedEpsTie` on the closed forms): `miniature_fixedEps_tie_state_iff` states the tie on the calibrated state of `C^ε` at `⊤` (`V(a) = V(b) ↔ q = q*(ε)`); `FixedEpsTie`'s docstring and ledger row disclose the closed-form variant.
- N5 (F1 weaker than the package's theorems): F1 now cites `tys_adviceEdt_iff` — remark (2) fails under both event-conditioned readings (D2 at each `ε`, D4's limit), independently of the Remark-3.12 construal.
- N6 (F9 overstates): reworded to "underspecified in `k`, confirmed at `k = 10`".
- N7 (F8 sharpening): machine-checked — `thirdCarrier_perRunSSC` (`Mugging.lean`): `thirdCarrier` is exactly the `P` of the per-run-SSC-calibrated state at `C = δ_pay` (dp-calibration's `mug1_perRun_not_strict`, the calibrated state at `⊤`), so FP-4's nearest rendering here is a calibrated state at the SSC grade; F8 says so.
- N8 / adversarial 4, 5 (kind labels, unused hypotheses): `perRunClause1_imp_anthropicIndiff` relabelled `L`; `tys_strict_dilemma` ledgered `N+`; the T8 D2 row says "P; the unrecorded AMD cell N−" and carries `0 < S`; `mug_fp6` ledgered `P / N+`; `tnV1_pureOpt_iff` lost its two unused hypotheses (`S < L`, `½ < p`) and is ledgered `stronger`.
- N9 (D1 row wording): the T8 D1 row now attributes "every state" to `mug1_not_limitStateEdt_interior` only.
- Adversarial 3 (stale text): `Grid.lean`'s module docstring and the first T9 ledger row now say the three rows' masked/per-run/per-occ cells are shipped (`GridMore`).
- Adversarial 8 (presentation): `mug1_eventTremble_iff`'s docstring says `0 < x` is load-bearing, with `mug1_eventTremble_x_zero` (`N−`, probe P6 ported); `floorRatifiable_boundary` closes the `ε` range (nothing above `½`, `{½}` at `½`; probe P5 ported).
- Adversarial 6 (the extension exercised only at the empty-event end): `tysObsAlt` (Told-You-So with `O₁₀ := {(5,10)}`, a non-leaf world) — `tysObsAlt_d2Vacuous_ten` (`N+`: the escape clause fires at `d₁₀` for every procedure and tremble, with non-empty action events, `tysActEv_nonempty`) and `tysObsAlt_not_d2Vacuous_five` (`N+`: it does not fire at `d₅`), `tysObsAlt_unrealised_ten` (the criterion's tree-level side).

**Disputed.** Nothing.

**Not done (recorded).** Adversarial 6's full ZO-19 rows (CX1, Claim-B, AMD+e) are not built; the `tysObsAlt` witness has the shape the item asked for on an existing tree. The per-run witness in N7 is at `C = δ_pay` only (the carrier's pushforward), as FP-4's act-supposition is.

**Gate after the repair.** `scripts/lean-build Cleanroom.Decision.DpDevicesCatalog` completed (1541 jobs); `scripts/wp-audit Cleanroom.Decision.DpDevicesCatalog`, run after the last Lean edit (`thirdCarrier_perRunSSC`): **PASS**, 3274 declarations audited transitively (3233 before the repair), axioms `propext`/`Classical.choice`/`Quot.sound` only, no `sorry`; open list still empty.
