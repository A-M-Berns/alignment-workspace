# corr-three-step — findings about the sources (and the mandate)

*Written 2026-09-29 by the formalizer agent (Claude Fable 5.1, [scrubbed]) for the `corr-three-step` work package. Severity scale per [STANDARDS](../../STANDARDS.md) §5: blocking the note's conclusion / local error / imprecision / presentation. Each finding names its pointer and, where one exists, the Lean declaration that establishes it. Attribution claims are labelled ATTRIBUTION-UNVETTED per `research/CLAUDE.md`.*

## F-1. The mandate's F4 witness numbers are wrong for T3's instance (local error, in the mandate not the sources)

**Pointer.** `corr-three-step-mandate.md` T6, "Witness: T3's instance (`voiButton = 341/400`)".

**What is true.** T3's instance `(ε, α, β, c, h) = (1/20, 1/20, 9/10, 1, 20)` has `E_μ[X] = (1 − ε)c − εh = 19/20 − 1 = −1/20 < 0`: the agent would *stop* on its prior, so the instance is outside the continue-by-default regime that F4(b) assumes. The two-option value of the button there is `Δ₊ = 321/400`, not `max(Δ₋, 0) = 341/400`. Proved: `Witnesses.w3_expect_Xo_neg`, `Witnesses.w3_voiButton2` (via the regime-free formula `Identities.voiButton2_eq`, itself a new statement: `VOI = max(−Δ₋, 0) + max(Δ₊, 0) − max(Δ₊ − Δ₋, 0)` under A1 alone).

**What the package does instead.** The F4 witnesses are `h = 10` (in the regime: `E_μ[X] = 9/20`, `Δ₋ = 161/400`, `VOI = 161/400`; `Witnesses.w10_voiButton2`) and `ε = 1/362` with `h = 20` (in the regime, `Δ₋ < 0`, `VOI = 0`; `Witnesses.w362_voiButton2` — this half of the mandate's claim was right). T3's own witness (both halves strict) is unaffected.

**Why it matters.** The same slip is a live hazard for dependents: `filler.md` F4(b)'s `VOI = max(Δ₋, 0)` is regime-conditional, and the regime is *not* implied by "D1 holds strictly" — the corpus's flagship instance violates it. The regime-free formula is the safe object.

## F-2. §2.13(b) writes "≲" for an exact "≤" and omits the silence half (imprecision)

**Pointer.** `workflow-2026-09-13/position-statement.md` §2.13(b), l. 95–97 ("compliance stays rational only while `α/β ≲ …`"); the silence half is `positive/mm.md` I13.4.

**Lean.** `TwoState.twoState_deltaMinus_nonneg_iff_odds` (exact `≤`, with the positivity `ε < 1`, `0 < β`, `0 < c` that the odds form needs) and `TwoState.twoState_deltaPlus_nonneg_iff_odds` (the silence half, needing `β < 1`). Under both halves `α ≤ β` is a theorem: `TwoState.twoState_alpha_le_beta_of_both` (`0 < ε < 1`, `0 < c`, `0 < h`).

## F-3. §2.9's `X` names `a₂^cont` without requiring the posterior-best continuation at the press (imprecision)

**Pointer.** `position-statement.md` §2.9 ("let `X = V(a₁,o,a₂^cont,ω) − V(a₁,o,a₂^sh,ω)`"); `filler.md` F1 remark (a) states the requirement; `general-object-final.md` S2(c), S6(b) and CE3 show the prior-plan reading fails.

**Lean.** The identity needs the press-part-maximiser pair (`Identities.d1At_iff_belowThresholdIneq`, quantified over every such pair); the single inequality is necessary (`GeneralMenu.belowThresholdIneq_of_d1At`), sufficient when `Shᶜ` is a singleton (`GeneralMenu.d1At_of_singleton_cont`), and not sufficient in general: CE3 as a `ThreeStep` (`Witnesses.ce3`) with the prior plan `p1` (`ce3_prior_plan`), the single inequality holding with equality (`ce3_single_ineq`) and D1 failing because `p2` is strictly better after the press (`ce3_not_d1`, `E_P[V(p2) 1_Pr] = 9/5`).

## F-4. Wentworth §2.4's "VOI" is the signed policy difference `Δ₋` (imprecision)

**Pointer.** `workflow-2026-09-13/critique/wentworth.md` §2.4, l. 98–115 ("`VOI = εβh − (1 − ε)αc`").

**What the source says.** Wentworth knows his quantity is signed — his own clause (a) reads "VOI > 0 iff εβh > (1−ε)αc iff α/β < (ε/(1−ε))·(h/c) — exactly the compliance condition of PS 2.13(b)" — so the finding is not that a sign was overlooked but that the *name* is loose: the value of information proper is nonnegative (Good's theorem, his own clause (b)), and his displayed "VOI" is the signed policy difference, which is negative exactly when compliance fails (`w362`: `β > α`, `ε < c/(c + h)`, `Δ₋ = −1/7240 < 0`, all within his standing assumptions). His bound (b) `VOI ≤ εβh ≤ εh` holds for both readings.

**Lean.** `TwoState.wentworth_voi_eq_deltaMinus`: his quantity is `Δ₋` exactly, and `Δ₋` is negative whenever D1 fails (e.g. `Witnesses.w362_deltaMinus`). The value of information proper is `max(Δ₋, 0)` in his regime (`Identities.voiButton2_eq_max_deltaMinus`); his bound `≤ εβh ≤ εh` holds for both (`TwoState.twoState_deltaMinus_le`, `eps_beta_h_le`, `twoState_voiButton2_le`). His regime lemma (`ε ≤ c/(c + h)` and `α ≤ β` imply continue-by-default) is proved as `TwoState.twoState_regime_of_threshold`.

## F-5. The Wängberg mapping is `filler`'s and unvetted; the local printout's superscripts are corrupted (presentation + ATTRIBUTION-UNVETTED)

**Pointer.** `references/04-chai/wangberg-2017-…md` l. 262–282 (the pdftotext of Theorem 9 / Corollary 10 has displaced superscripts); `filler.md` F3 last paragraph (the mapping `(p_u⁻, p_ar⁺, p_r⁻, e⁺, e⁻) = (ε, α, β, c, −h)`); `channel-final.md` S12(a) flags it as unvetted.

**Lean.** Theorem 9's closed forms are *proved from the semantics* (a finite prior, `U`, and the two-type human's allow probability `OSG.allowProb`): `OSG.expect_eq_stats`, `OSG.expect_allow_eq_stats`; Corollary 10 as `OSG.expr4_eq` / `OSG.prefer_a_iff`. The bridge `OffSwitch.twoState_expr4` (`(4) = −Δ₋`) and `twoState_prefer_a_iff` (`a ≻ w(a) ↔ Δ₋ < 0`) carry `Fidelity: variant` and the ATTRIBUTION-UNVETTED label; `twoState_expect_allow_eq_deltaPlus` records that Theorem 9's `E[U | w(a)]` is `Δ₊`, the silence half Wängberg et al. state but do not name. Nothing was read off the printed formula.

## F-6. `filler.md`'s "desideratum 5 made decision-relevant" gloss on `Δ₊ ≥ 0` (ATTRIBUTION-UNVETTED, presentation)

**Pointer.** `filler.md` F2(iv). An interpretive claim about Soares et al. 2015; no declaration is named after D5, and the docstrings call `Δ₊ ≥ 0` the above-threshold inequality / the silence half.

## F-7. A0 is substantive; here it enters F4 only as the pair instance `μ aDir = μ aDet` (imprecision; the finding itself is `corr-position-finds`'s)

**Pointer.** `filler.md` F4 ("Add A0 …"); corr-wf13-2-121.

**Lean.** `Identities.hardButton_sub_disabled` takes `hμ : S.μ aDir = S.μ aDet`, the instance of A0 at the two buttons, rather than global `S.A0`; the mandate's "under A0" is honoured at its weakest. The disabled button is a member of `A₁` with `press = 0` (violating nondegeneracy, as the mandate says), and its cost is `V aDet = V aDir − κ`; the "forcing" on a press is the value expression `hardButtonValue` — disclosed as `(c)` in the docstring.

## F-8. `general-object-final.md` S3 lives in a richer setting; T9 takes only what restricts to Setting S (scope)

**Pointer.** S3(a)'s reflection hypothesis (`h_L ≥ 0` from minimal viability) is grade (b) and left out; S3(b)'s identity is proved on an abstract event `L ⊆ Ω` (`Thresholds.condExpPress_eq_event_split`, `belowThresholdIneq_iff_event_split`, `belowThresholdIneq_iff_event_threshold`, `belowThresholdIneq_of_gain_nonpos` — the first three were renamed from `…_legit_split`, `…_iff_legit`, `…_iff_legit_threshold` in repair round 1; pointers updated in repair round 2). As the source says, it is an identity with named hypotheses (the two positive masses on `L` and `Lᶜ`; `0 < pressMass` follows) — Kind `L`, not a headline. The threshold form takes `0 < c_L + h_L` where S3(b) says "`c_L > 0`" with `h_L ≥ 0` supplied by S3(a); in Setting S, `c_L > 0` alone does not suffice (`h_L < −c_L` breaks the form), so the Lean hypothesis is the honest one and the ledger grades it `stronger`.

## F-9. Prop. 9.2 is `L` on the product-form definition, not `P` (presentation; corrects the plan's pre-label)

**Pointer.** `miri.md` Prop. 9.2; plan risk line for T10.

**Lean.** `GeneralMenu.belowThresholdIneq_iff_sign_split` is a `sum_filter` split plus `|X| = −X` on `Ω⁻`. The conditional-form reading adds only the "multiply by `p(Pr) > 0`" step (`Setting.belowThresholdIneq_iff_condExpPress`). The source's "under A1" is not needed for the `X`-form.

## F-10. The eighteen `[checked]` blocks re-verify one inequality (presentation; corr-wf13-2-127)

Recorded as the ledger's single T3 row family; the script counts upgrade no Kind.

## F-11. T13's identity fails off the two-option menu (new; a finding about `filler.md` F4(b)'s scope)

**Pointer.** `filler.md` F4(b) states `VOI = max(Δ₋, 0)` for "the button" without saying the menu is `{c, s}`.

**Lean.** On the full menu the identity needs `c` to be press-, silence- and prior-optimal (`GeneralMenu.voiButton_eq_max_deltaMinus`); in CE3 the press-part-maximiser of `Shᶜ` is `p2` (`Witnesses.ce3_p2_partBest`, `E_P[V(p2) 1_Pr] = 9/5`), `Δ₋(p2, null) = −9/5` (`ce3_deltaMinus_p2`), and the full-menu value of the button is `9/5 ≠ max(Δ₋(p2, null), 0) = 0` (`Witnesses.ce3_voiButton_ne_max`) — `p2` is neither silence- nor prior-optimal (`p1` is), and the press makes `p2` the best response, which is value the button carries even though it never makes the agent stop. (Round-1 wording compared `9/5` with `Δ₋(p1, null)`; `p1` is not the press-part-maximiser, so that comparison failed `hc` rather than the regime hypotheses — corrected in repair round 1.) A second failure mechanism (repair round 2): a prior-best *shutdown* action `b ≠ s`, `Witnesses.s3_voiButton_ne_max` (`1/2 ≠ 1`; see F-13). The identity's full package is inhabited off the two-option menu: `Witnesses.w13_voiButton` (four actions, `Δ₋ = 2/5 > 0`, `VOI = 2/5`). Imprecision in the source; the two-option restriction is load-bearing — and for F4(c) it is more than load-bearing, it is the difference between true and false (F-13).

## F-12. The inventory's band pointer: the band is in `legitimacy-general-final.md`, not `general-object-final.md` (presentation; about the inventory and mandate, not a source)

**Pointer.** `corr-three-step-mandate.md` T9 cites "general-object-final.md S3(b), D10" for the band `((1 − ε)/ε)(α/β) < h/c < (1 − ε)/ε`; neither S3 nor D10 of that file states it. The band is `workflow-2026-09-14b/develop/legitimacy-general-final.md` Statement 4(d) ("defined only where the modification can flip the decision, which is exactly v1 §2.13(b)'s base-rate band") and check Y2 ("the agent continues by itself iff `(1−ε)c₀ > εh₀`, and the legitimate press flips it iff `εβh₀ > (1−ε)αc₀`"); the scale invariance is Statement 4(d)'s "homogeneous of degree zero in the stakes" (check X2). `corr-wf14b-inventory` 005(d) merged the two finals. Docstrings and ledger rows of `twoState_band_iff` and `twoState_deltaMinus_nonneg_scale_iff` now cite the right file (found by the round-1 fidelity audit).

## F-13. `filler.md` F4(c)'s "`VOI ≥ Δ` in general" is false on the full menu (local error; refuted in Lean; found by the round-2 adversarial audit)

**Pointer.** `filler.md` F4(c): "In general (no regime assumption) `VOI ≥ Δ`: letting the button decide is one strategy the informed agent may use, which is Good's theorem. [checked … 3000 … 0 failures]", with `VOI(button) := E_o[max_{a₂} E_P[V | o]] − max_{a₂} E_P[V]` the maxima over the *whole* menu `A₂` (F4(b)). The mandate's T6(c) repeats it: "without the regime, `delta a c s ≤ voiButton a`", `voiButton` being the full-menu object, graded `exact`.

**What is true.** On the two-option menu `{c, s}` the claim holds (`Identities.delta_le_voiButton2`, and `GeneralMenu.delta_le_voiButton_of_two_option` for the full-menu object when the menu has two actions). On the full menu it fails as soon as `Sh` contains a prior-best action other than `s`. **Refutation** (`Witnesses.s3`, adopted from the round-2 adversarial audit's probe 1): three actions `c, s, b` with `Sh = {s, b}`, two worlds with prior `(1/2, 1/2)`, a perfect sensor `(α, β) = (0, 1)`, payoffs `V c = (2, −2)`, `V s = (0, 0)`, `V b = (10, −1)`. Then `(c, s)` is a press-part-maximiser pair (`s3_c_partBest`, `s3_s_partBest`; strictly, `E[V(b) 1_Pr] = −1/2 < 0 = E[V(s) 1_Pr]`), A1 holds (`s3_A1`), the two-option regime holds (`s3_regime`: `E_μ[X] = 0`, `Δ₊ = 1`), D1 holds (`s3_d1`), `Δ₋ = Δ₊ = Δ = 1` (`s3_delta`) — and the full-menu value of the button is `0 + 5 − 9/2 = 1/2` (`s3_voiButton`: press-max `0` at `s`, silence-max `5` at `b`, prior-max `9/2` at `b`). So `Witnesses.s3_voiButton_lt_delta : voiButton < delta`, i.e. `1/2 < 1`. The two-option value there is `1 = Δ` (`s3_voiButton2`), so the gap is exactly what the two-option restriction hides.

**Why the argument does not give the claim.** "Letting the button decide is one strategy the informed agent may use" yields `E[V(S^H)] − priorMax ≤ VOI` (`GeneralMenu.shPolicy_sub_priorMax_le_voiButton`, no A1), and under A1 that lower bound is `≤ Δ` (`shPolicy_sub_priorMax_le_delta`), because the full-menu prior maximum dominates the two-option one; the two coincide only when the prior maxima coincide. The `[checked] 3000` runs presumably used two-option menus.

**The corrected statement.** `Δ ≤ VOI` on the full menu whenever `s` is prior-optimal within `Sh` (`GeneralMenu.delta_le_voiButton_of_prior_best_sh`: the prior-best action of the whole menu is either a continuation, and then the informed agent gains at least `Δ₋`, or a shutdown action no better on the prior than `s`, and then at least `Δ₊`); in particular whenever `Sh = {s}` (`delta_le_voiButton_of_singleton_sh`), any number of continuations. `s3` shows the hypothesis on `s` cannot be dropped. The symmetry with T11(ii) is exact: the single-pair statement is right when the *other* part is a singleton (there `Shᶜ`, here `Sh`).

**Related.** The same instance breaks F4(b) on the full menu by a mechanism different from CE3's (F-11): a prior-best *shutdown* action rather than a better *continuation* after the press (`s3_voiButton_ne_max : voiButton ≠ max(Δ₋, 0)`); both are invisible to the two-option regime hypotheses, which compare `c` with `s` only. Severity: local error in the source (the claim as stated is false; the two-option form and the corrected full-menu form are true); the mandate's T6(c) first clause is thereby refuted, not proved, and its `exact` grade for (c) was wrong.
