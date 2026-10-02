# corr-power-channel — findings about the sources

*Findings per [STANDARDS](../../STANDARDS.md) §5, with severity (blocking the note's conclusion / local error / imprecision / presentation) and a pointer. Sources: `research/corrigibility/workflow-2026-09-14/dynamics/power-wisdom-final.md` (cited as power-wisdom-final.md with statement labels and line numbers), `dynamics/power-wisdom-adversary.md`, `workflow-2026-09-14b/develop/channel-final.md`, `develop/d1-special-case-final.md` (d1-final.md), the scripts named in the mandate, and the Turner summaries. Lean pointers are to `Cleanroom/Corrigibility/CorrPowerChannel/`. The mandate's "recorded only" items are F-7 to F-12.*

## F-1 — S2's "general case" structural-gap inequality is false without separability (local error; blocking for S2's general-case sentence, not for the E3 instance)

**Pointer.** power-wisdom-final.md S2 (l. 103: "**General case:** with an unreportable component `ρ` (D16), `VOI_t(s | q) ≥ VOI_t(ρ) > 0` for every `δ`"), D16 (l. 73: "`VOI_t(a | q) ≥ VOI_t(a | q, π)` — the value of what `a` reveals about `ρ` — for every channel error `δ`, including `δ = 0`"), P2 (l. 159: "`q` is uninformative about `ρ` and `s` reveals it, so `VOI_t(s | q) ≥ EVPI^ρ_t` at every `δ`"); power-wisdom-adversary.md S2.2 (l. 45).

**What is wrong.** Read as stated — for any option set, a channel `q` uninformative about `ρ` and a scan `s` revealing `(π, ρ)`, the marginal `VOI(s | q)` is at least the value of learning `ρ` alone — the claim fails. `Gap.lean`, `gap_counterexample`: `Ω = Bool × Bool` (`π`, `ρ`) uniform, four options worth `𝟙[π = 0]`, `𝟙[π = 1]`, `𝟙[ρ = 0]`, `𝟙[ρ = 1]`, `q = ofMap Prod.fst` (reveals `π` exactly, `δ = 0`), `s` perfect: `EVPI = 1/2`, `VOI(q) = 1/2`, `VOI(s, q) = 1/2`, so `VOI(s | q) = 0`, while `VOI(ofMap Prod.snd) = 1/2`. Once `π` is known a `π`-option is worth `1` and `ρ` is decision-irrelevant: the "value of what `s` reveals about `ρ`" is conditional on what `q` already gave, and need not be the unconditional value of `ρ`. **Register (repair round 1; scoped in repair round 2):** D16's displayed inequality `VOI_t(a | q) ≥ VOI_t(a | q, π)` stands *for the perfect scan* `a = s`, for every pair of channels — `VOI(s | q) − VOI(s | q, π) = VOI(q, π) − VOI(q) ≥ 0` by Blackwell, proved as `marginal_perfect_antitone` (`Separable.lean`), and it reads `0 ≥ 0` in the counterexample; for an `a` that reveals `ρ` alone, the reading D16's own words invite, the display is false (F-19). What is refuted is S2's general-case sentence and P2's identification of `VOI_t(s | q, π)` with the *unconditional* `ρ`-residual `EVPI^ρ_t` ("`VOI_t(s | q) ≥ EVPI^ρ_t` at every `δ`"): the value of `ρ` given `(q, π)` is not the value of `ρ` alone unless the two sides of the decision separate.

**Nearest well-posed version — proved (repair round 1, `Separable.lean`).** Under **additive separability over a product option set** — `Ω = Ω₁ × Ω₂`, `P = P₁ ⊗ P₂` (`prodDistr`), `A = A₁ × A₂` with option set `B₁ ×ˢ B₂`, `V((ω₁, ω₂), (a₁, a₂)) = V₁ ω₁ a₁ + V₂ ω₂ a₂` (`sepV`), `q = expComap Prod.fst q₁` depending on `ω₁` only — `VOI(s | q) = (EVPI₁ − VOI₁(q₁)) + EVPI₂` exactly (`voiExp_marginal_sep_eq`), hence `VOI(s | q) ≥ VOI(ρ-component) = EVPI₂` for every `q₁` including the perfect one (`voiExp_marginal_ge_rho_sep`, with `VOI(ρ)` the same object `voiExp … (ofMap Prod.snd) …` the counterexample uses; `voiExp_rho_sep`). The mechanism is `voiExp_sep_fst`: a `π`-only channel is worth on the product decision exactly what it is worth on the `π`-problem, because the `ρ`-coordinate is chosen on the prior whatever the signal; and `evpi_sep`: `EVPI` is additive. The mandate's instance is `e3rho_marginal`: E3 at `n+1` plans times a uniform `ρ ∈ Fin (m+1)` with a bet at stake `σ ≥ 0` gives `VOI(s | q) = δ(1 − 1/(n+1)) + σ(1 − 1/(m+1))` and `VOI(ρ) = σ(1 − 1/(m+1))` — equality at `δ = 0`, and positive at every `δ` iff `σ > 0`. S2's "`> 0`" is therefore the hypothesis `0 < EVPI₂` (the `ρ`-side is decision-relevant), not a theorem. The source should add the separability hypothesis to S2's general case and to P2's sentence, and name the brain-reader case as the separable one.

## F-2 — "J3 against asking first at every `n` iff `δ ≤ μh`" needs `0 < μh` (imprecision)

**Pointer.** power-wisdom-final.md S2 (l. 103: "J3 holds at **every** `n` iff `δ ≤ μh`"), P2 (l. 159).

**What is imprecise.** At `μh = 0` the harm side is `0` and J3 (strict) fails at every `n` and every `δ`, including `δ = 0` (`J3.lean`, `e3_j3Given_fails_of_zero`), so the "iff" is false there (`0 ≤ 0` holds, J3 does not). The exact statement is `e3_j3Given_all_iff`: under `0 < μh`, `(∀ n, J3 against asking first at `n+1` plans) ⟺ δ ≤ μh`, both directions, with `δ = 0` and one plan in range. The source's `μ = h = 1/2` has `μh = 1/4 > 0`, so its table is unaffected.

## F-3 — corr-wf14b-031's "instance of Prop. 6.9" is a gloss; only the `p = 1`, `γ = 1` count is exact (imprecision; the mandate's known issue 1)

**Pointer.** channel-final.md S10 (l. 83: "an inclusion-of-option-sets instance of Prop. 6.9 (l. 1942)"; "POWER after eroding `0.668` against `0.510–0.515`"; "erode optimal for `61%, 67%, 67%` of reward functions at `γ = 0.5, 0.9, 0.99` (40 000 draws each)"); `check_turner.py` (`p = 0.9`).

**What is wrong.** Prop. 6.9's hypothesis is a state-permutation involution `φ` copying `F(s | keep)` into `F(s | erode)`. At `p = 9/10` the keep branch's visit distributions mix `z` with `c1` (`f = e_s + γ e_k + γ²(p/(1−γ)) e_z + γ²(1−p) f^{c1}`), and no permutation of the five states maps such a mixture onto a visit distribution of the erode branch (which never puts mass on `z` or `k`). So the similarity hypothesis fails and Prop. 6.9 does not apply; the Monte Carlo numbers are estimates at `γ < 1`, not instances of a theorem. **Scope (repair round 1, fidelity N4):** this is the situation at `p = 9/10`. At `p = 1` the similarity hypothesis of Prop. 6.9 *does* hold — the involution `k ↔ c1`, `z ↔ c2`, `s` fixed maps `e_s + γe_k + γ²/(1−γ)·e_z` onto `e_s + γe_{c1} + γ²/(1−γ)·e_{c2} ∈ F(s | erode)`, `s ∉ REACH(s, keep)`, and `s` is left only through keep/erode — so at `p = 1` "erode `≥_most` optimal and POWER-seeking" is available at every `γ ∈ [0, 1]`, not only as the `γ = 1` count; that all-`γ` statement is a natural strengthening of T7(b) and is not formalized here. **What is proved** (`Mdp.lean`): at `p = 1` and `γ = 1` (average optimality), for every reward vector with distinct values, over its orbit `#{erode average-optimal} ≥ 2·#{keep average-optimal}` (`cor614_orbit_count`) — Cor. 6.14 for `s_x = z`, exact, and sharper than the `≥_most` form; in fact the counts are exact (`cor614_orbit_count_exact`, repair round 2): **when `R` is injective — the theorem's hypothesis, almost surely for IID continuous rewards — the keep cell is exactly `40` of the `120` permutations, one third of the orbit, and the erode set exactly `80`** (`card_keepOptPerms`, `card_erodeOptPerms`; the three cells of `{c1, c2, z}` are equal, disjoint and cover the group, `card_strictBestPerms_mul_of_injective`), matching the `0.67` at `γ = 0.99`; and, for *every* reward vector with no tie hypothesis, the `≥_most`-shaped count `#{erode-opt ∧ ¬keep-opt} ≥ 2·#{keep-opt ∧ ¬erode-opt}` (`cor614_orbit_count_strict`, repair round 1). The injectivity hypothesis is needed in full (on all five states), not only for the three terminal rewards: `R = (0, 0, 0, 1, 2)` has three distinct terminal values, its keep cell is `48` (two fifths, not one third), its erode set `84`, and the first count reads `2·48 ≤ 84`, false; the tie-robust count is tight there (`2·36 = 72`). (Repair round 2, fidelity B1: an earlier version of this paragraph stated the one-third count under "three distinct terminal rewards", which this very example refutes.) The source should cite Cor. 6.14 at `γ = 1` and call the `p = 9/10` numbers what they are.

## F-4 — d1 S3's "the sign changes … iff `a_θ > 31603/894103`" is one-sided; the exact condition has an upper threshold too (imprecision)

**Pointer.** d1-final.md S3 (l. 50: "under whole-line stakes and the worked parameters the sign changes at `λ* = 71737/80190` iff `a_θ > a_θ* = 31603/894103 ≈ 0.0354`"), P3 (l. 82).

**What is imprecise.** "Changes sign on `[0, 1]`" needs `margin 0 > 0` as well as `margin 1 < 0`. Both `F(a_θ)` and `H_0(a_θ)` are affine in `a_θ`, and `margin 0 = 62359/500000 − (894103/1250000) a_θ` is positive iff `a_θ < 311795/1788206 ≈ 0.1744` (`Hazard.lean`, `wholeLine_margin_zero_pos_iff`); the exact two-sided statement is `wholeLine_sign_change_iff`: a sign change on `[0, 1]` iff `31603/894103 < a_θ < 311795/1788206`. At the worked `a_θ = 1/20` both hold and `λ* = 71737/80190` is the exact root (`wholeLine_lambdaStar`); at `a_θ = 3/100` there is no crossing and at `4/100` there is (`wholeLine_cells`), as the source says. The lower threshold `31603/894103` is confirmed exactly (`wholeLine_margin_one_neg_iff`).

## F-5 — The develop file's per-option self-cap is inert: `EVPI{a, ∅} = 0` for every option dominated by `∅` (confirmed as a theorem; local error in the develop S11, already killed by the final file)

**Pointer.** power-wisdom-final.md S11′ (l. 135); power-wisdom-adversary.md S11.1–S11.3 (l. 155–159).

**What was wrong and is now a theorem.** `SelfCap.lean`, `evpi_pair_null_eq_zero`: `(∀ ω, V_ω(a) ≤ V_ω(∅)) → EVPI{a, ∅} = 0` for every posterior; `evpi_insert_dominated`: the D17 unlock increment of such an option is `0`. The final file's replacement — set-level coverage (`J3Coverage`) plus the support veto (`SupportVeto`) — is formalized with its witnesses (`e3_selfcap_inert`, `e3_support_veto`, `takeover_veto`, `e1n_veto_passes_coverage_blocks`). No further issue.

## F-6 — The time-averaged `Π^obj` of the develop file admits the catastrophe it exists to prevent (confirmed; local error in the develop D17, repaired in the final)

**Pointer.** `power-wisdom.md` D17 (l. 79, quoted in `Evpi.lean`); power-wisdom-adversary.md D.3 (l. 19); power-wisdom-final.md D17 (l. 79).

**Status.** `capObjAvg_admits_catastrophe`: A5's trajectory passes the average at `θ = 1/50` and fails the sup form. The sup form `CapObjTraj` is the definition of record. O1 (composition along the trajectory) has no theorem in the thread and none is manufactured here (mandate known issue 5).

## F-7 — Recorded only: corr-wf14-112 and 113 (presentation)

112 (composition) is `corr-caution-power`'s (`prod2_quantilize_compound`, `prod_cost_bound_compound`, `nGame_sharp`); nothing to add. 113 (O1–O8): O1 has no theorem anywhere (see F-6); O8's two-sided form `Reach · κ ≤ θ` is one D row (`CapTwoSided`, `Power.lean`) with no theorem about it, as the source marks it `[conjectured]`.

## F-8 — Recorded only: 2-061, S3 is ill-posed (presentation)

power-wisdom-final.md S3′ (l. 105) and adversary A4: there is no stakes knob in the linear rule; harm magnitude enters only through `harmOf`. The residue is a docstring remark on `J3` (`Power.lean`). Not formalized.

## F-9 — Recorded only: 2-058, the develop script's retracted "EVPI → 1/2" (presentation)

The retraction is honest (adversary S1.1); the trusted closed form `½(¾)ⁿ + ½(¼)ⁿ − (½)ⁿ` is T12 (`stretch`, not done). Nothing in the package depends on it.

## F-10 — Recorded only: 027/O8 and 032 — the inaction baseline and the site of legitimacy for erosion (imprecision; the mandate's known issue 2)

channel-final.md D10 (l. 43) and O8 (l. 160): failing to maintain a channel lowers `Γ` without being erosion; `Γ^e = 1`, `M^H = Δ(Ω)` for hardware is a modelling choice, not the author's identity. `ErodesReach` (`Channel.lean`) takes the null option as its baseline by hypothesis (an argument `nul`), so the choice is visible. 032/S11 (l. 85): the "legitimate erosion" label on the `(other, other)` cells is the source's under the accuracy-only anchor, which S11 itself withdraws as a definition; `s11_grid` (`Grip.lean`) proves the nine values and the four comparisons and attaches no legitimacy predicate.

## F-11 — Recorded only: 037's (H1)–(H4) by fiat; 041's `m p_θ ≤ p_r` is a definition (presentation; the mandate's known issue 6)

d1-final.md D6 (l. 38): the model fixes persistence by hypothesis; every number is model-specific, and the witnesses in `Hazard.lean` are N+ *for the model* (ledger says so). 041's identity is a definition of `r` (T11, not done).

## F-12 — Recorded only: 106(a) register, 106(b), 108 (presentation)

106(a): the develop file doubted a correct run-1 citation of Turner l. 248 ("these results apply … to individual reward functions"); the final withdraws the hedge, and `scaling_law_mixValue` makes the gloss exact. 106(b) is HM Theorem 1, `corr-osg-chai`'s (`osgDelta_rational_nonneg`, `osgDelta_rational_pos_iff`); nothing to prove here. 108 is 004 with roles renamed: `unlock_iff_deltaMinus` (`Splice.lean`) exhibits it as `0 ≤ Δ₋` of `twoState (1 − ε) α β h′ c′`.

## F-13 — "`≲`" in S6's unlock inequality is "`≤`" (presentation)

power-wisdom-final.md S6 (l. 113: "`α^E_t/β^E_t ≲ ((1−ε^E_t)/ε^E_t)(c′_t/h′_t)`"). The Bayes computation gives an exact `≤` (`unlock_iff`); the same finding as `corr-three-step`'s on position statement §2.13(b).

## F-14 — S5's "every behavioural wisdom meter is gameable" holds only with (H1)–(H3) named (presentation; the final already scopes it)

power-wisdom-final.md S5 (l. 109). `splice_bound` needs only `p_E(πw) ≥ 1 − η`; the "`α ≥`" clause needs reliability, (H2) and (H3) (`splice_alpha_bound`). The bound is a worst case over the class; the mandate's reading (S5.3) is kept in the docstring. The premise that a capable class contains a discriminator and the splice is Carlsmith's and enters as the hypotheses (H1)–(H2), not as a derived fact.

## F-15 — The coarsened ceiling holds for *any* agreeing class, not only the maximal-mass one (presentation; stronger than the source)

power-wisdom-final.md S1(iii′) (l. 99: "the maximum over decision-equivalence classes"). `evpi_le_one_sub_prob_class` takes the class as a hypothesis (any `C` on which `V_ω` agrees on `B`), so the maximal-mass class is the user's best choice, not part of the theorem. The singleton corollary `evpi_le_one_sub_mass` is the develop bound, vacuous under non-dogmatism (S1.3), as the source says.

## F-16 — Prose-open items (no Lean statement; listed so they are not mistaken for done)

1. ~~The separable structural-gap theorem (F-1's nearest well-posed version) — stated in prose, not in Lean.~~ **Done in repair round 1**: `Separable.lean` (`voiExp_marginal_sep_eq`, `voiExp_marginal_ge_rho_sep`, instance `e3rho_marginal`).
2. T11(b)–T17 of the mandate (`stretch`/`extension`): not attempted (T11(a) is done); see [corr-power-channel-report](corr-power-channel-report.md) §Not done. T16's MDP half is now largely covered by `cor614_orbit_count_exact` (keep is average-optimal on exactly one third of the orbit under injectivity) — the "channels on which erosion and POWER-seeking come apart" statement is still not formulated.
3. The `Tendsto` form of `rsd = lim (1 − γ)·visit`: replaced by the exact identity `rsd_identity` with an explicit `O(1 − γ)` correction; the limit is read off it, not stated as a filter limit (no topology import).
4. The all-states form of `AvgOptimal` (Def. 6.11); the `p = 1`, all-`γ` orbit statement (F-3's natural strengthening). Argued in docstrings, not formalized.

## F-17 — channel-final S1's "[derived]" reach sentence is a definitional unpacking of function-form endorsement (presentation; repair round 1, adversarial N1)

**Pointer.** channel-final.md S1 (l. 65: "a datum 'believe `ρ`' lands on `ρ` iff `ρ` is anticipated", marked `[derived]`), P1 (l. 99: "`P(ω | E_k) = ρ_k(ω)`").

**What is imprecise.** Under `(Mart)` — `ReflectiveFor P K ρ`, whose clause at `i` is `∀ ω, P ω K ω i = P(E_i) ρ_i ω` — the statement "the conditional on `E_i` is `ρ_i`" is `corr-general-object`'s `endorsed_iff_postPush_eq` read once per inclusion; `dataReach_eq_anticipated` (`Channel.lean`) is Kind L for that reason. S1's substantive content is elsewhere: the barycentre converse (`exists_anticipation_of_barycentre`, imported from corr-wf14b-028 = 003(ii)) and the "one anticipation per target, not all of `Δ(Ω)`" clause (`dz_two_target`, Kind P). The source could say "by definition of endorsement" rather than "[derived]".

## F-18 — channel-final S9's "general form for the blind model" is the value-certain POWER form (imprecision; repair round 1, fidelity N8)

**Pointer.** channel-final.md S9 (l. 81: "General form for the blind model: `POWER^Γ_D(A_t) = (1−Γ)·E_D[max_a E[V | a]] + Γ·E_D[V_ω(hum)]`").

**What is imprecise.** The free arm of that display is `POWER = E_D[max_B V]` — the maximum *inside* the expectation, i.e. the value-certain attainable value — not the blind free arm `(E_P X)⁺` of the same section's slope computation (`vFreeBlind`, `Grip.lean`). The two agree only for a point-mass `D`, which is the source's own "for a value-certain agent" caveat two lines earlier. `powerGrip` (`Orbit.lean`) is faithful to the formula as displayed and the mandate prescribes it; the label should read "value-certain form" (or "POWER form"). The practical consequence is on the record: on R1's kernel the value-certain slope is `−9/10` (`powerGrip_r1`), the blind slope `+3/20` (`r1_slopes`) — different objects, which is why the ledger's `powerGrip` witness was re-pointed.

## F-19 — D16's displayed inequality `VOI_t(a | q) ≥ VOI_t(a | q, π)` is false for an `a` that reveals `ρ` alone; it needs `a` decision-sufficient (local error in D16's display; repair round 2, fidelity N1)

**Pointer.** power-wisdom-final.md D16 (l. 73: "`VOI_t(a | q) ≥ VOI_t(a | q, π)` — the value of what `a` reveals about `ρ` — for every channel error `δ`, including `δ = 0`").

**What is wrong.** Read as its words say — `a` an observation that reveals `ρ`, `π` the legitimate channel, every `δ` — the inequality fails: information is complementary, not submodular. `Gap.lean`, `d16_display_fails_for_rho_only_a`: `Ω = Bool × Bool` (`π`, `ρ`) uniform, two options betting on `π = ρ` and on `π ≠ ρ` (XOR), `q = ∅` (`δ = 1`), `π = ofMap Prod.fst`, `a = ofMap Prod.snd` (reveals `ρ` alone): `VOI(a) = 0` (knowing `ρ` alone is worthless for an XOR bet), `VOI(π) = 0`, but `VOI(a, π) = EVPI = 1/2` (the pair reveals the world), so `VOI_t(a | q) = 0 < 1/2 = VOI_t(a | q, π)`. The display's "for every `δ`" therefore fails at `δ = 1` already. **What stands:** the display with `a = s` the *perfect* scan, for every `q` and `π` (`marginal_perfect_antitone`, `Separable.lean`: `VOI(s | q) − VOI(s | q, π) = VOI(q, π) − VOI(q) ≥ 0` by Blackwell) — the case the package proves and the case P2's E3 instance uses. More generally the perfect-scan value is attained by any deterministic scan that reveals everything decision-relevant (`voiExp_ofMap_eq_evpi_of_factors`), which is the hypothesis the display needs: `a` decision-sufficient. The source should state D16's display for the scan `s` (or for a decision-sufficient `a`), not for a general `ρ`-revealing `a`.
