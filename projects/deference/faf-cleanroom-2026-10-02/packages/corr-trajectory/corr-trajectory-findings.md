# corr-trajectory — findings about the sources

*[STANDARDS](../../STANDARDS.md) §5. Severity: **blocking** (the note's conclusion does not follow) / **local error** / **imprecision** / **presentation**. Every claim about what a person meant is ATTRIBUTION-UNVETTED; the sources are CLAUDE-authored and unvetted by the author (the final's own register, Known issue 13). Pointers are to `research/corrigibility/workflow-2026-09-14/dynamics/` unless stated. Lean names are in `Cleanroom.Corrigibility.CorrTrajectory`.*

## F-1 — "`Z_t` is a `P*`-supermartingale, i.e. `Δ_t ≤ 0`" presupposes observable realized losses · imprecision (local error in the "i.e.")

**Where.** `invariant-final.md` Statement 8(b) l. 83: "If `Z_t` is a `P*`-supermartingale, i.e. `Δ_t := E*[Ψ_{t+1} ∣ 𝓕_t] + E*[ℓ_t ∣ 𝓕_t] − Ψ_t ≤ 0`"; the second display's Ville bound.

**What.** `Z_t = Ψ_t + ∑_{s<t} ℓ_s` is a supermartingale w.r.t. `(𝓕_t)` only if it is adapted, i.e. the incurred loss `∑_{s<t} ℓ_s` is `𝓕_t`-measurable. S1 defines `𝓕_t` as the *observable* history and S2 step 5 says a complied round's counterfactual never settles — so `ℓ_s` (which contains `W_s`) is **not** observable on complied rounds, and `Z` is not adapted in general. The "i.e." silently adds the hypothesis. What survives without it: the expectation bound (i) needs only `Δ_t ≤ 0` on every atom (`AgentView.expect_Reg_le`, no adaptedness); the uniform Ville bound (ii) needs `Z` adapted and carries the named hypothesis `AgentView.lossesObservable` (`ville_Z`). The refutation rows (A1, A8, A2) are about `Δ`, `Ψ` and `E*[R]` and need neither. In Layer M the hypothesis `Supermartingale Z ℱ μ` *contains* adaptedness, so the Mathlib theorem is exactly the source's statement with the presupposition visible.

**Nearest well-posed version.** State 8(b) as two claims: (i) from `Δ_t ≤ 0`; (ii) from `Δ_t ≤ 0` **and** observable realized losses (or from `Z` adapted to a larger filtration `𝓖_t ⊇ 𝓕_t ∨ σ(ℓ_s : s < t)`, with `Δ` conditioned on `𝓖_t`). This also sharpens Statement 3's "relocation": on complied rounds the certificate's *excursion* bound is about a process the agent cannot observe (adversary item 11 said this for `Reg_T`; it holds for `Z_t` too).

## F-2 — Statement 1's D2 "closed in the product topology" was *stronger* than prefix-witnessing, not merely different · imprecision (2-023 sharpened)

**Where.** `invariant.md` D2 ("equivalently `Φ` is closed in the product topology"); `invariant-adversary.md` item 1; `invariant-final.md` S3 ("`S` carries the discrete topology for D1–D3").

**What.** For every topology on `S`, closed ⟹ prefix-witnessed (`Grades.safetyProp_of_isClosed`); the converse needs discrete `S` (`Grades.isClosed_of_safetyProp`); and on `S = ℝ` the prefix-witnessed set `{s ∣ s 0 ∈ (0,1)}` is not closed (`Grades.safety_not_isClosed_real`). So the develop's wording was not "different" (adversary item 1: "the two notions differ") but one-directionally stronger; the direction the develop *used* (closed ⟹ safety, to put invariants in D2) holds for every `S`. Also: Statement 1(a) (nonempty tail ⟹ dense) and (b′) (closed tail ⟹ `∅` or `univ`) hold for every topology on `S` (`Grades.dense_of_tailProp`, `tail_isClosed_trivial`); the final's "`S` discrete for D1–D3" is needed only for D2's "equivalently". And 1(b) as the source states it — in D2's prefix-witnessing vocabulary, "a tail property is a safety property only if it is `∅` or `S^ℕ`" — is true with no topology at all (`Grades.tail_safety_trivial`, repair round 2, audit r2 fidelity N2): for non-discrete `S` it is the stronger statement, since its hypothesis is weaker than closedness.

## F-3 — Statement 4's identity needs (MI); A6 · imprecision: an unflagged modelling assumption in the develop, named in the final (confirmed in Lean; severity revised in repair round 1)

**Where.** `invariant.md` Statement 4 and Summary ("exactly `∑_t ε_t(1−β_t)h_t`"), S2 step 3 l. 28 ("`Pr_t ∼ Bern(β_t)` if `W_t = 1`"); `invariant-final.md` S2 step 3 ((MI) named), Statement 4 (`≤` with `β^min`, equality under (MI)); adversary items 13 and 67.

**Scope (audit r1, adversarial B2(c)).** In the develop's own S2 step 3 the press depends on `W_t` alone — a magnitude-independent press by construction — so the develop's identity holds *in the develop's model*. What A6 refutes is the identity for a process whose press may depend on the magnitude (the final's S2, where (MI) is a named hypothesis), and the develop's Summary compression "exactly …" stated without the assumption (adversary item 67). The first version of this finding called it a "local error in the develop"; it is an unflagged modelling assumption, hence imprecision.

**What.** `A6.a6`: one round, `ε = 1/10`, `H ∈ {1, 9}` equiprobable given `W`, `β(1) = 1/2`, `β(9) = 1`: true compliance harm `1/40`; the identity evaluated with the *process's own* product-form conditionals `ε = 1/10`, `β̄ = 3/4`, `h̄ = 5` gives `1/8`. The final's repair is confirmed: `harm_le_detection` (with `β^min = 1/2`, discharged on the process: `1/40 ≤ 1/4`) and `harm_eq_detection` under `(MI)` (C7: `89/200`, `(MI)` discharged on every pre-press atom, `C7.detectionEq`). One addition the source does not make: `(βmin)` must be stated **per magnitude** on the pre-press atoms (`detectionLB`), and the harm-weighted form is then a lemma (`detectionLB_harm`) — the source's `ess inf_H β_t(H)` is this.

## F-4 — Statement 5(a)'s non-propagation claim confirmed (C10); the propagating form is strictly stronger than (i) · no source error (rewritten in repair round 1: the mandate's "refuted" label was a mandate error)

**Where.** `invariant.md` Statement 5(a) l. 75; `invariant-final.md` Statement 5(a), C10; inventory corr-wf14-2-022; mandate T4(b).

**Correction (audit r1, B2 in both lenses).** The first version of this finding said Statement 5(a) claimed that "(i) at `t = 0` and `ε_t h_t` non-decreasing propagate (i)" and was refuted by C10. The source says the opposite: l. 75 reads "the weaker premise '(i) holds at `t = 0` and `ε_t h_t` is non-decreasing' does **not** propagate: with `β = 1`, `cα = 1`, … (`1/2 < 3/4`; C10 [checked])", the final repeats it, and inventory 2-022 records it as a witness item. The sentence previously quoted does not occur in the source; it came from the mandate's T4(b) ("**Refuted** (2-022, the develop's 5(a))"), a mandate error carried into the Lean docstring, the ledger and this file without reading l. 75. Per the run's rules (STANDARDS wins over a mandate; flag the conflict) this is recorded here and in the report.

**What.** `Margin.c10` re-proves the source's own C10 on `oddsIneq`: `β = 1`, `cα = 1`, round 0 `(ε, h) = (1/2, 1)` holds with equality, round 1 `(1/4, 2)` has the same `εh` and fails — a confirmation. `Margin.sufficient_form_propagates`: `ε h β ≥ c α` propagates under non-decreasing `εh` (with `0 ≤ ε' ≤ 1`, `β, cα ≥ 0`) and implies the exact form — the source's (a). The one addition the source does not make: at C10's round 0 the sufficient form itself fails (`1/2 < 1`), so the propagating form is strictly stronger than (i).

## F-5 — Statement 7(d)'s factorization conditions on `𝓕_t`, which already contains the press · local error in the `𝓕_t` reading (the bound is false there); well-posed on `𝓕_t^-` (severity revised in repair round 1)

**Where.** `invariant-final.md` Statement 7(d) and its proof ("given the first two and `𝓕_t`, execution happens iff not pressed or pressed-and-defied: probability `≤ (1 − β^min_t) + β^min_t(1 − κ_t)`").

**What.** `δ_t := P*(s_{t+1} ∈ Cat ∣ 𝓕_t)` with `Pr_t ∈ 𝓕_t` (S1: `𝓕_t` is the observable history through round `t`, after the press). Given `𝓕_t` the press is not random, so the factor `(1 − β^min_t κ_t)` cannot arise from conditioning on `𝓕_t` — and the `𝓕_t` form is not merely underivable but false: on an `𝓕_t` atom with `Pr_t = 0` and `κ_t = 1` (unpressed, would have complied) the round executes, so `δ_t = P*(Irr_t ∧ W_t ∣ 𝓕_t)` under the `Irr` inclusion, while the claimed bound is `(1 − β^min_t)` times that (audit r1, fidelity N8). The factorization is a statement on the **pre-press** atoms `𝓕_t^-` (`ShutdownProc.hazard_factorization`), where `κ_t` is measurable and the press is random; the per-round hazard bound of 7(a) stays on `𝓕_t`. Nearest well-posed version: define `δ_t^- := P*(Cat_{t+1} ∣ 𝓕_t^-)`, factorize that, and note `δ_t^-` averages `δ_t` over the press.

## F-6 — Statement 8's two "iff"s and "locality" (develop) — confirmed refuted on `AgentView` instances · local errors, withdrawn in the final

**Where.** `invariant.md` Statement 8 title l. 81 and (c); `invariant-final.md` 8(a)–(c).

**What.** `LossToy.a1` (chain holds, Mart fails, certificate false), `LossToy.a8` (`Δ₀ < 0`, bound holds, forecasts disagree), `LossToy.a2` (honest at both times, `Δ₀ = 3/40 > 0`): the adversary's three counterexamples hold on the `ShutdownProc`/`AgentView` objects, not only in the script. Two remarks the final does not make: (1) the toy's "press" is the uninformative always-on press, so `executed = ¬κ` *is* S2 step 4's rule — the counterexamples are instances of S2, not of a different model; (2) A8's `Δ₀ = −1/8` is strictly negative, so a strict supermartingale certifies — "calibration" is one point of a half-line.

**Scope of `a2_calibrated`** (repair round 2, audit r2 fidelity N1). The develop's 8(b) parenthetical — "`Δ_t ≤ 0` … which holds whenever `P_t` and `P*` agree on the one-step forecasts" (l. 83) — is refuted by A2 *detached from 8(a)*: in A2 both one-step forecasts agree (`E_{P₀}[ℓ₀] = E*[ℓ₀] = 3/10`, `E_{P₀}[Ψ₁] = E*[Ψ₁] = 3/8`) and `Δ₀ = 3/40 > 0`. But 8(a) — the agent's reflection, the unconditional Mart identity — is the develop's standing hypothesis, and under it the parenthetical is exact: `Δ_t = 0` (`AgentView.drift_eq_zero_of_uncondMart_of_calibrated`); A2's agent fails 8(a) (`E_{P₀}[Ψ₁] = 3/8 ≠ 3/10 = E_{P₀}[R₁]`, `LossToy.a2_not_uncondMart`). So the parenthetical's error is one of scope (it reads as if one-step calibration alone sufficed), not a false sentence under its own section's hypothesis; the refuted status of the row is carried by the "locality" sentence, which the final withdrew.

## F-7 — (iv) as S4 defines it does not give 8(a); the certificate re-certifies on the legitimate branch only · local error in the develop (adversary item 37), confirmed and made tight

**Where.** `invariant.md` Statement 8 ("Reflection along the trajectory (iv) is exactly what makes the certificate re-certifiable"); `invariant-final.md` 8(e).

**What.** `LegitToy`: the legitimacy-conditioned identity holds (`27/100 = 27/100`), the unconditional one fails (`59/200 ≠ 8/25`), the round-1 certificate is dishonest exactly on `¬L` (`a3_honest_one`), and the legitimacy budget is tight (`f2`: both sides `1/10`). The source's `E*[R₁ ∣ ¬L] = 1/2 > 1/4` is, in product form, `E*[R₁ 1_{¬L}] = 1/20 > 1/40 = Ψ₁ P*(¬L)`. The final's 8(e) is confirmed with its content located in `(H)` (`legitimacy_budget` is `L + C`).

## F-8 — Statement 9's VOI conjecture (develop) is false, and which experiment "`VOI_t(a)`" names decides whether its hypothesis even holds · local error, withdrawn in the final (confirmed); imprecision in the final

**Where.** `invariant.md` Statement 9 l. 87; `invariant-final.md` S4(ii) ("VOI form"), Statement 9.

**What.** `Coverage.a4` over `corr-channel-voi`'s `voiSensor` with the agent's available experiment `k = trivialExp` (the note fixes none — reading, ATTRIBUTION-UNVETTED): `I₂^VOI` holds, the EV rule executes, the credence is uncovered against `9/10` for every `η < 4/5`. **New:** at the *perfect* experiment `VOI = E[max(X,0)] − max(E X, 0) = 1/10 = E_P[harm]`, so `I₂^VOI` (strict) *fails* at A4's numbers (`Coverage.a4_perfect`): the VOI form is not a condition until the experiment is fixed. The final's S4(ii) should say which experiment `VOI_t(a)` is the value of.

## F-9 — Statement 10(c)'s "coverage persists iff `r_t ≥ v_t`" is ill-posed; the two coverages are separated · imprecision (final), local error (develop)

**Where.** `invariant.md` Statement 10(c); `invariant-final.md` Statement 10(c), Open problem 2; `invariant-adversary.md` item 46.

**What.** The recursion `d_{t+1} = max(0, d_t − r_t + v_t)` is the *definition* of `track` (`Basin.track`); C9a–c are its evaluations (`track_const`, `c9a_lower`); "summable drift is tracked" is the small theorem `track_reaches_zero`. Action-relative coverage (`Coverage.covered`) and the tracking distance `TV(P, δ_{θ*})` are separated both ways (`Basin.two_coverages_witness1/2`: `TV = 1/2` with gap `0`; `TV = 0` with gap `1/2`). No Lean statement can refute "coverage persists iff `r_t ≥ v_t`" because it has no object; Open problem 2 (the link, if any, between coverage persistence and a tracking-rate condition) stays open — a dynamics model relating `P_t`, `θ*_t` and the action family is what is missing.

## F-10 — Statement 11(c) (develop): descent does not imply convergence to the target · local error, withdrawn in the final (confirmed)

**Where.** `invariant.md` Statement 11(c); `invariant-final.md` 11(b).

**What.** `Sequences`: `d ≡ 1`, `d_t = 1 + 1/(t+1)` (strictly decreasing, limit `1`), C8 (converges, not monotone). The surviving neighbour is proved in Layer M: a nonnegative supermartingale converges a.s. to *some* limit (`Martingale.ae_tendsto_of_nonneg`). Reading of "`E[d_{t+1} ∣ s_t] ≤ d_t`" as `Antitone` for deterministic sequences: ATTRIBUTION-UNVETTED on Christiano's text, as the final says.

## F-11 — `joint.md` Prop. 9: the exception clause carries the content — the lever is `h/c`, resumability one way to move it · presentation (sharpening, not a refutation; rewritten in repair round 1)

**Where.** `joint.md` Prop. 9 l. 141 ("**Unless `h_t` is itself of the order of `F_t` (an irreversible catastrophe)**, resumability is what makes (i) satisfiable for a long-horizon agent at all; the design lever is `r_t`, not `α_t`"); §P.10.

**Correction (audit r1, B3 / adversarial B2(b)).** The first version of this finding graded Prop. 9 "refuted as the mechanism claim" on the instance `h = 200` against `c = F = 100`. That instance is exactly the case Prop. 9's own clause excludes (`h` of the order of `F`). On the stated domain — `h` fixed and small against `F`, `c = (1 − r)F + r d` — homogeneity *confirms* the claim: the thresholds move with `(c, h)` only through `h/c`, and with `h` fixed only `r` moves `h/c`. The Lean (`Accounting.prop9_lever_is_ratio`, formerly `prop9_refuted`) is unchanged; its name, the ledger's status and this finding's headline oversold it.

**What.** `Accounting.epsStar_homogeneous`, `complianceThreshold_homogeneous`: both thresholds depend on `(c, h)` only through `h/c`. At `r = 0` (`c = F = 100`) with the harm scaled to the future (`h = 200`) the threshold is `1/3` and `ε* = 1/13` — the same as at `(1, 2)` (`prop9_lever_is_ratio`). So the design lever is the ratio `h/c`; resumability lowers `c`, an irreversible catastrophe scales `h` — which is what the clause says, now with the arithmetic that makes it exact. The rows themselves (`25/26, 25/31`, `1/5, 1/25`, `101/109, 101/149`) are exact (`row_*`). Surviving neighbour: gap accounting `c = F_agent − F_alt`, `h = F_alt − F_mis` — the parent's stakes. S2 vs S2′ (Question 5) is not decided here: `ShutdownProc.executedWL` is defined, nothing is proved about its loss decomposition (Open problem 7).

## F-12 — Test A's claim is false as stated: the quantifier over `E` was dropped · local error (`critique/yudkowsky.md` l. 135)

**Where.** `workflow-2026-09-13/critique/yudkowsky.md` Test A ("Claim to prove or refute: for every `P` satisfying (i)–(iv), (v) fails as `δ → 0`").

**What.** (v) ⟺ `𝒱(E) ≤ 𝒱(Pr)` (`TestA.waiting_iff`), and under the test's own "`E` at least as informative as `Pr`" this is `𝒱(E) = 𝒱(Pr)` (`waiting_iff_eq`). At `E = ⟨Pr, trivialExp⟩` (Blackwell-equivalent to the press) (v) holds at any compliant two-state prior with (i)–(iii) (`testA_claim_false`); the claim is true exactly when `E` is *strictly* more valuable (`testA_claim_iff`), where (ii)–(iv) play no role. The intended claim quantifies over `E` ("as evidence-gathering gets cheap") and is then the 1a escape in LI form: (v) for every gatherable `E` ⟺ `¬ BlackwellLE Pr E` for every gatherable `E` — the press carries information no `E` carries. Not claimed here (OPEN, text). (iv) — legitimacy-conditional reflection with `P(L)` computed by `P` itself — is not modelled in the finite shadow; the verdict does not depend on it.

## F-13 — T13's "law" is not formulable without a model of the overseers' update · imprecision (`joint-final.md` Open problem 1)

**Where.** `joint-final.md` Open problem 1 (l. 274); mandate T13.

**What.** A trajectory of inclusion rounds is cellwise compliant because inclusion is re-imposed (`Inclusion.inclusion_trajectory_cellwise`, `C`, no law). The undisclosed refinement (`undisclosedLift`) cannot satisfy Prop. 1′'s hypothesis on two sub-cells (`undisclosedLift_not_inclusion`); E1 (`Margin.e1`, `Battery`) is the resulting failure. The "transition on `(A_t, y_t, h_t)` under which inclusion is preserved from disclosure" needs the overseers' update rule as an object (how `f_{t+1}` is formed from `f_t` and the agent's disclosure); without it there is no Lean statement to leave open, so it is recorded here as text.

## F-14 — 2-083's `s3_s5_trajectory.py` `range(0,16)` defect · presentation, passed to `corr-landscape`

**Where.** `dynamics/approval-*` scripts (Known issue 11).

**What.** Not this package's source; per the mandate the `range(0, 16)` defect in `s3_s5_trajectory.py` (an off-by-one in the trajectory loop) is passed to `corr-landscape` without further verification here.

## F-15 — Open problems recorded, not formalized (text)

- **Open problem 2** (coverage vs tracking): see F-9.
- **Open problem 3** (is A7's agent reflective on `¬C`?): A7's agent is modelled only through its posterior (`Corruption.a7`); its reflection identity for the loss variable needs the agent's next-self law on both branches — not built. Cheapest Lean test: an `AgentView` on the A7 space with `L = {¬C}` and `condMart`. Why it is not a `sorry`'d entry in `corr-trajectory-open.txt` (audit r1, adversarial N12): the statement needs the `AgentView` as an *object* — its `agentLaw` on both branches is precisely the model the sources do not supply — and a `sorry`'d definition is not an open statement but a hole in the carrier; once a next-self law is chosen (a modelling decision, not a theorem), `condMart` on it is a ten-line check.
- **Open problem 7** (whole-line accounting): `executedWL` defined; nothing decided (Question 5).
- **Open problem 9** (viability kernel of a finite joint toy): T9(b) not attempted.
- **corr-wf13-2-030 C14.3** (the basin as the set of value-learner priors converging under designated feedback): recorded; `lit-mdp-corrigible`'s `GoalMDP.myopic_indep_corrigible` is C14.1 (cited, not imported).
- **Known issue 10**: corr-wf14-046 (adapted optional stopping) is `corr-reflect-frames`'s; no finite optional-stopping lemma fell out of T7 beyond `ville_finite`'s first-hitting induction (which is the finite optional-stopping argument at a hitting time, not a general one).
