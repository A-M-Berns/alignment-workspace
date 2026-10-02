# corr-landscape — report

*Formalizer: Claude Fable 5.1 ([scrubbed]), 2026-10-01. Mandate: `corr-landscape-mandate`. Ledger: [corr-landscape-ledger](corr-landscape-ledger.md). Findings: [corr-landscape-findings](corr-landscape-findings.md). Open list: `corr-landscape-open.txt` (one entry since repair round 1: `Horizon.phiW_supermartStep`). Lean: `Cleanroom/Corrigibility/CorrLandscape.lean` (root) + 21 modules under `Cleanroom/Corrigibility/CorrLandscape/` (`Map`, `Trichotomy`, `Regret`, `Margin`, `Kappa`, `Crossing`, `ActBased`, `BasinToy`, `Kalman`, `Amplify`, `Control`, `Invariant`, `Erosion`, `Switch`, `Timestep`, `Selection`, `Entrench`, `Legitimizing`, `TwoRound`, and since repair round 1 `Drift`, `Horizon`), namespace `Cleanroom.Corrigibility.CorrLandscape`, about 4 900 lines and 330 top-level declarations. Repair round 1: see the section at the end.*

## State of the package

**Gate: PASS** (after repair round 1) — `scripts/wp-audit Cleanroom.Corrigibility.CorrLandscape` plus all 21 modules named, after the last edit (2026-10-01): `22 module(s)`, `1905 declaration(s)`, axioms `['propext', 'sorryAx', 'Classical.choice', 'Quot.sound']` with `sorryAx` reaching exactly one declaration, the listed OPEN `Horizon.phiW_supermartStep` (reported `OPEN`, not failed); no native/unsafe/opaque, lint clean (every top-level declaration carries `Source:`/`Kind:`). The audited closure is the package's own ~330 declarations plus the imported `corr-trajectory`, `corr-joint-process`, `corr-three-step`, `lit-shutdown-prefs` modules. Nothing else in the package rests on a `sorry`, here or in a dependency (`lit-shutdown-prefs`'s OPEN is not on `Timestep`'s path).

**Every `core` target is closed; the five load-bearing headlines are `P`/`C` at grade (a) with N+ witnesses; both extension targets are done at the stated scope** (E1 fully — Proposition R′ is *attained* exactly on one side and *approached* on the other; E2(i) as the one-step statements plus the full `IsSupermart` on the two-round product process, `TwoRound.phi_isSupermart`, with the general-horizon lift diagnosed, F-21). T9 (stretch) is done at the definitions-plus-null-update level with one instance per class. Not attempted: E1's File Deletion Game cell (stretch), the Kalman convergence `P_t → P_ss` (stretch), the two remaining replacement kernels (stretch), T9's cumulative two-round instance, E2(ii), O9/OP7 (optional).

1. **T6, S7** — D9′'s invariant `step_dist_lt`/`traj_dist_lt` (P, with the `η = 1` boundary found and the strict form shipped), the contraction over a finite disturbance law with `ρ†` (P), `d` a one-step supermartingale above `ρ†`, the separation pair **against a drifting target** (D9′ frozen with `d_t = r + tσ`, unbounded; D9 from the same data entering and converging to the lag `σ/η < r`; N+ for "a basin exists iff acceptance depends on distance" — the zero-disturbance pair is kept as the N− skeleton), the D9 label refutation (every `r` above the noise scale is invariant; kind L, carried with the pair), and the bridge to `corr-trajectory`'s `forwardInvariantWithHazard` at hazard `0` over the product law with prefix atoms (L: pointwise invariance relabelled).
2. **T15, Proposition R′** — `regret_le` (P) from the per-signal excess bound, exactly the source's proof; tightness **attained** (`regret_attained`: regret `= (c+h)δ + |k̂ − k|` for `k̂ ≥ k`), **approached** on the other side (`regret_approached`: regret `= bound − η` for every `η > 0`, for `k̂ ≤ k`), and **never attained** for `k̂ < k` (`regret_lt_of_lt`, P, through the strict per-signal bound `excess_lt`), so the two-sided form is `sup = (c+h)δ + |k̂ − k|`, attained iff `k̂ ≥ k`; worked `1/2`.
3. **T14, the trichotomy** — the three identities (P), (a) as signed masses (P), (b) with the three-case refinement (P), Toy T's cells including the anti-informative one inhabiting the full package of (b) (N+).
4. **T3, the value coordinate** — affine, `m(0)`'s sign, the crossing `κ*` (P), strictly antitone in `ε` (P), **`κ*(ε*) = 1` exactly** (L: the regime holds at `ε*`, then the definition of `κ*`; replacing the inventory's and S4(iii)'s limit), the P3′ table as exact rationals, `t_conf = 7` as a least index.
5. **T4/T5, the crossings** — `t* = 17` as the least `t` with `ε_t < 1/361` (P), failure from `17` on, the general eventual bound; the AD floor `5/7`, never-fails-iff-floor (P), the `t = 10` refutation row with its surviving neighbour, drills raising `ε*` in general (P) and the `14, 13, 11` crossings as least indices.

**Deviations and decisions.** (i) `Timestep.lean` imports `Cleanroom.Lit.LitShutdownPrefs.CostModel`, outside the plan's dependency edge for `corr-landscape`; the mandate directed it ("in this one file only") so the TD definition is cited, never redefined; the import is Mathlib-light and `lit-shutdown-prefs`'s one OPEN is not on the path (the gate's only `sorryAx` is this package's own listed `Horizon.phiW_supermartStep`). (ii) The mandate's suggested file split was followed except that T1–T2 are `Margin`, T3 `Kappa`, T4 `Crossing` (three files, not one), and the witnesses live beside their theorems rather than in a `Witnesses` module. (iii) Three mandate numbers were wrong and are corrected in the findings (F-18 T11's witness, F-19 T17's rule, F-20 T2's box); the mandate asked for exactly this. (iv) `ρ†` is defined for the finite law (`(η E|ξ| + E|Δ*|)/η`) and the uniform value is reproduced by the three-point law — no (c) was needed (F-6).

## Design

**Finite shadow, product form.** Every probability is FAF's `Distr` on a finite type. The landscape's objects are on `Distr (S × Bool)` (signal, `L^push`): `legMass μ s = μ(s, L)`, `nonlegMass`, `sigMass = P*(s)`, `lam = ∑ legMass`, and the loss `ℓ*(r) = ∑_s cost(r s, s)` with `cost true s = μ(s,L) h + P*(s) k`, `cost false s = μ(s,¬L) c` — S5's bracket times `P*(s)`, no ratio. The Bayes rule is `decide (μ(s,L) < q_k P*(s))`; the posterior `piStar = legMass/sigMass` is a named real that appears only inside `covered` (quantified over `0 < sigMass`) and in the Toy T cells, where the masses are positive. `q_k = (c−k)/(c+h)` carries `0 < c + h` in every theorem. The approval lineage's margin is `corr-trajectory`'s `oddsIneq` (reused, never redefined); `effMargin` is its ratio form with `ε < 1`, `0 < c` on every theorem. The basin is a deterministic recursion with bounded disturbance *sequences*; its probabilistic statements are over a finite law on an alphabet with `ξv, Δv : A → ℝ`.

**Numerics.** No decimal is a theorem: `t* = 17`, `t_conf = 7`, the drilled `14, 13, 11` and the AD `10` are least indices by `interval_cases` + `norm_num`; `K_ss` and `P_ss` are brackets by sign change and monotonicity; the P3′ table ships exact rationals (`κ*_8 = 1452102/7902305`); the robustness box is one corner by monotonicity; the switch cells are exact rationals with the grid values shown to be the grid points below them.

**What is a headline and what is not.** Every target's claim has a row; supporting lemmas (`sum_sigMass`, `cost_true_sub_false`, masses of the toy laws, `abs_recursion_le`, …) carry the generic infrastructure docstring and no row.

## Per target

### T1 — the margin layer (`Margin`) · core · D + L + C

`effRates`, `effMargin`; `effMargin_one_nonneg_iff : 0 ≤ m(1) ↔ oddsIneq α β h c ε` under `ε < 1`, `0 < c` (L, the ratio's junk points as hypotheses); `effMargin_one_nonneg_iff_deltaMinus` composes it with `corr-trajectory`'s `Margin.oddsIneq_iff_deltaMinus` to FAF's `twoState` `Δ₋` (C); `effMargin_one_eq_zero_iff : m(1) = 0 ↔ ε = epsStar` under `0 < αc + βh` (L); `oddsIneq_iff_epsStar_le` (L). All (a). Status: proved.

### T2 — openness and the box (`Margin`) · core · T + L + N+

`strictMargin_isOpen` (T): the set `{(ε,α,β) ∈ (0,1)³ : m(1) > 0}` is the open box intersected with the strict polynomial inequality `(1−ε)cα < εhβ` (`isOpen_lt` on continuous maps; `strictMargin_iff_poly` is the equivalence on the box). The docstring says what the source says: every strict inequality is open, not a robustness theorem (A4.4). `effMargin_one_mono` (increasing in `ε`, `β`; decreasing in `α`) and `box_worst_corner`: on `ε ∈ [1/4, 7/20]`, `α ∈ [1/100, 9/100]`, `β ∈ [3/5, 6/5]` the margin is `≥ 391/100`, the corner value, and `m_0 = 1073/140` (N+, one cell). Status: proved. F-20 notes the box exits `[0,1]` in `β`.

### T3 — the value coordinate (`Kappa`) · core · load-bearing 4

(a) `effMargin_affine`, `effMargin_zero`, `effMargin_zero_neg_iff` (`π > 0`, `0 < c`, `0 ≤ h`, `0 ≤ ε < 1`), `effMargin_zero_nonneg_of_threshold_le` (2-051(c)). (b) `kappaStar := −m(0)/(m(1) − m(0))`; `comply_iff_kappaStar_le` on the regime (P); `comply_all_of_nonneg`, `fail_all_of_neg` with both endpoint signs explicit, and `effMargin_zero_le_one` (`α ≤ π ≤ β`, `u ≥ 0 ⟹ m(0) ≤ m(1)`) — the source's trichotomy presupposes this (F-15). (c) `kappaStar_closed`; `kappaStar_strictAnti` (`π > 0`, `β > α`, `0 < c`, `0 < h`, denominators positive; at `h = 0` the crossing is constant, so `h > 0` is needed) (P); `kappaStar_epsStar : κ*(ε*) = 1` under `0 < π`, `0 ≤ α < β`, `0 < c`, `0 < h` (P; F-3). (d) `kappaStar_table` (five exact rationals by `norm_num` after unfolding; the `t = 16` row has denominators of order `4^16`), `table_regime` (each row in the regime; `m(1)_8 = 6450203/12713540`, `m(0)_8 = −726051/6356770`), `tconf_least`. All (a). Status: proved. Register: the `κ` model is D14's CLAUDE stand-in for Carey 2018; ATTRIBUTION-UNVETTED on Christiano's sentence, stated in the file header.

### T4 — trajectory fragility (`Crossing`) · core · load-bearing 5 (half)

(a) `epsStar_worked : epsStar (1/20) (9/10) 1 20 = 1/361`; `tstar_least` (P): `∀ t ≤ 16, ¬ ε_t < 1/361` and `ε_17 < 1/361`; `complies_through_16`, `fails_from_17` (through `epsT_antitone`). (b) `margin_eventually_neg` (P; Fidelity weaker — an eventual bound `≤ −α̲/2` for the source's limit, F-16); `fails_of_antitone` (L, the parent's `oddsIneq_mono`). (c) the four cells as predicates on `(α̂, β̂, α, β, ε)` with `J2feedback`, `J2model`, `comply_iff_warranted_of_J2model` (the parent's `subj_iff_obj_of_agreements`), `cells_witness` (N+: over-trust at `(1/20, 9/10 ∣ 1/2, 1/100)`, FUD proper at the swap, `ε_0 = 3/10`). Provenance finding F-2. All (a). Status: proved.

### T5 — the act-based dual (`ActBased`) · core · load-bearing 5 (half)

(a) `authIneq pA γ c'' := c''(pA + γ) ≤ pA(1 + c'')`, `authIneq_iff_ratio`, `authIneq_iff` (`↔ c''γ ≤ pA`, P4's line). (b) `pA ε α β`, `pA_ge`, `pA_tendsto`, `pA_antitone`, `authPost`, `authPost_tendsto` (floor `α/(α+γ)`), `authPost_worked` (`61/65`, `5/7`), `never_fails_iff_floor` (P, both directions: `ge_of_tendsto'` for ⟹), `fails_in_limit_iff` (`¬ authIneq α γ c'' ↔ α/c'' < γ`, with `α(1−thr)/thr = α/c''` and `γ = 1/50` passing). (c) refutation row `decay_fails_least` (N−) with surviving neighbour `consistent_never_fails` (N+). (d) `drill`, `drill_worked`, `epsStar_drill_le` (P: drills raise `ε*` for `δ ∈ [0,1]`, `0 < α ≤ β ≤ 1`), `leastCrossing_antitone` (L; no monotonicity of `ε` needed), `drilled_crossings` (N+). (e) `opposite_scaling` (C). All (a). Status: proved.

### T6 — the basin (`BasinToy`) · core · load-bearing 1

See "State of the package" 1 and the ledger. `TwoRound.phi_isSupermart` lifts `phi_step` to `corr-trajectory`'s `IsSupermart` on the two-round product process `prod2 ν ν` with the filtration `atoms2` (the factorization `condSum_atoms2_one` is the two-round case of the missing general one). Statements and hypotheses: `step_dist_lt` needs `0 < η < 1`, `|ξ| ≤ ξ̄`, `|Δ*| ≤ σ̄*`, `η ξ̄ + σ̄* ≤ η r`; `step_dist_lt_of_strict` needs `0 < η ≤ 1` and the strict condition; `eta_one_boundary` is the boundary counterexample (F-14). `contraction` needs `0 < η ≤ 1` and `d < r`; `rhoDagger` needs `0 < η`; `supermart_above_rho` adds `ρ† ≤ d`; `phi_step` needs `η < 1`. `traj_frozen_at_r` needs `0 ≤ r`; `trajD9_enters` needs `0 < η ≤ 1`, `0 < r` (both N−, the skeleton); `traj_outside_drift` needs `0 ≤ r`, `0 ≤ σ`; `traj_outside_unbounded` needs `0 < σ`; `trajD9_enters_drift` needs `0 < η ≤ 1`, `0 < r`, `0 ≤ σ < η r`. `basin_forwardInvariant` needs the alphabet bounds and the condition; its atoms are `prefixAtoms T`, its law `prodLaw T ν` (every `Distr` works for the pointwise lemma; the product law is the natural one). **What resisted:** the `SupermartStep` lift of `phi_step` to the product space (F-21). The simulation statistics are not reproduced (F-13); Gaussian noise is text (F-8). Status: proved (core and (e)'s invariance half); E2(i)'s supermartingale lift proved on two rounds (`TwoRound`) and stated OPEN over the general horizon (`Horizon.phiW_supermartStep`, repair round 1).

### T7 — the Kalman freeze (`Kalman`) · core · P (small) / L

`Pss_root`, `Pss_pos`, `Pss_unique` (the second root `−(q + P_ss)` is negative), `Kss_zero`, `Kss_pos`, `Pss_bracket ∈ (819/10⁶, 82/10⁵)`, `Kss_bracket ∈ (327/1000, 329/1000)`, `Kss_inventory_bracket ∈ (246/1000, 248/1000)` (F-1), `Pseq`, `Kt`, `Kt_ge` (`K_t ≥ q/(q+R) > 0` for every `t`, `P_0 ≥ 0`), `gainVL_zero` (C over T4). All (a). Status: proved; `P_t → P_ss` (stretch) not attempted.

### T8 — the linear cap (`Amplify`) · core · L

`linear_cap` by induction; (A-amp) classified (c) in the docstring (F-9). Status: proved.

### T9 — the three-valued legitimizing relation (`Legitimizing`) · stretch · D + L + N+ + finding

`inert φ := ∃ g, ∀ e s, φ e s = g s`; `inert_null_update` (L): for an inert verdict, the mass-weighted sum over `{S = s, V = g s}` equals the one over `{S = s}` and the sum over `{S = s, V = v}` is `0` for `v ≠ g s` — conditioning on `V` jointly with `S` is a null update, in product form. `legitimizing` (conditioning on `V` strictly lowers the expected quadratic score about `X` against the prior mean; Fidelity: variant — the quadratic score for the source's unspecified proper score; `condMean` is a named real used only under positive verdict mass), `delegitimizing` (the reflection equation `E[X 𝟙[V = v]] = v P(V = v)` fails on some positive-mass `v`, product form). N+ on `Bool × Bool` uniform with target `𝟙[E]`: `inert_instance` (`φ e s = s`), `legitimizing_instance` (`φ e s = e`: score `1/4 → 0`), `delegitimizing_instance` (`φ e s = 1/2 + 𝟙[s]/4` breaks reflection at `v = 3/4`). The cumulative caveat (A11.3, O4) is text: a per-round defect measures the marginal `S`-dependence only; the two-round instance was not built. **Finding F-22** (repair round 1): the classes overlap as formalized — `legitimizing` compares against the unconditional mean, so an inert verdict is legitimizing whenever `S` is informative (`inert_and_legitimizing`); the `S`-relative baseline is not built. Status: proved at this scope, with the overlap disclosed.

### T10 — control by surprise presses (`Control`) · core · D + N+

`CtrlDefined` (the guard: both branches non-null at every positive-mass information state), `ctrlVal`, `Ctrl μ δ x` (a guarded Prop, never a junk number), `SurpriseCtrl f δ Sh := ∀ i, f i = false → δ i true ∈ Sh` and `NoSurpriseCtrl` (interventional; Fidelity variant of the conditional probability, P10's reading). `scenario_table` (N+): discounting — `Ctrl discLaw discPol 0` and no surprise control; pre-emption — `¬ CtrlDefined preLaw` with the null press branch at `I = false` exhibited, `SurpriseCtrl id prePol {true}`; forcing — `¬ CtrlDefined forceLaw`, no surprise control. `vlPolicy_eq_disc` (S12(a), C over T4). `tower` (A12.4, L: product-form reflection on every attained report value gives `E X = E R`, by `sum_fiberwise_of_maps_to`). All (a). Status: proved.

### T11 — "invariant of the agent" (`Invariant`) · core · D + N+

`InvariantOfAgent`, `vlCompliance_not_invariant` (N+; the mandate's witness corrected, F-18), `lexicalStop_invariant` (T: true by construction, since `lexicalStop` has no oversight argument — which is the source's notion; no non-syntactic witness is possible), `InvariantGiven`, `ConsequenceOf`, `invariantGiven_iff_consequence` (`Iff.rfl`). Status: proved. `Coined.*` cited, not re-sorted.

### T12 — the map's objects (`Map`) · core · D

Sixteen definitions of record (ledger row 1 of the map). D1a is the construal; `q_k` guarded; `piStar` named. Status: proved.

### T13 — Statements 1–2 (`Map`) · core · L / T

`loss_absolute`, `loss_none`, `absolute_lt_none_iff` (both directions, `0 < c+h`), `cost_bayes_le`, `loss_bayes_le`, `loss_bayes_lt_absolute`, `loss_bayes_lt_none`, `loss_bayes_lt_both` (strictness hypotheses exact, F-12), `conditionedRule_eq_bayes_of_exact`, `loss_conditioned_eq_bayes_of_covered_zero`, `landsMass_absolute`. The key algebra `cost_true_sub_false : cost true − cost false = (c+h)(μ(s,L) − q_k P*(s))` is the one identity everything in T13–T17 uses. Status: proved.

### T14 — the trichotomy (`Trichotomy`) · core · load-bearing 3

See "State of the package" 3. `anti_informative_worse`'s proof is shorter than P3's three cases (the conclusion `> min` needs only `D_R > 0 ∨ D_A < 0`); `anti_informative_cases` is the three-case statement itself (which constant is the better one). E1 (the File Deletion Game cell) not attempted. Status: proved.

### T15 — Proposition R′ (`Regret`) · core · load-bearing 2 · extension E1 done

See "State of the package" 2. Hypotheses: `0 < c+h`, `0 ≤ δ`, `covered`. Both tightness instances are on `oneSignal p` (`Distr (Unit × Bool)`), with the needed range conditions (`0 ≤ q_k̂ − δ ≤ 1`, etc.) as hypotheses; `regret_attained_worked` instantiates `c = 1, h = 4, k = k̂ = 0, δ = 1/10`. Status: proved, extension done.

### T16 — erosion, the stock, (H-decay), the switch, `β_t` (`Erosion`) · core (a–c) / stretch (d–e)

(a) `Map.erodes_antitone`, `erodes_one_iff`, `checkC` (F-17). (b) `toyLow_losses`, `e2_stocks`. (c) `none_eq_bayes_iff` (P), `stock_nonneg`, `stock_zero_iff` (P), `hdecay_iff` (C). (d) `switch_sufficient` (C), `switch_iff_refuted` (refutation row, F-4; since repair round 1 in the stronger form "no rule at all beats absolute", with no coverage hypothesis). (e) `fresh_stationary` (P small), `compliance_survives_drift`, `lineage_const` (T), `cohortBeta_antitone` (P small: a quadratic-form inequality in `(0.97^t, 0.94^t, 0.91^t)`), `cohortBeta_tendsto` (P: limit `3/10`). The most-visible and copy-a-survivor kernels were not attempted. Status: proved (a–d, and the fresh-draw/cohort/lineage parts of e).

### T17 — the switch rule (`Switch`) · core (lemma, exact rule) / extension (closed form) · P + N+ + finding

`canAccept`, `canResist`, `worstAt`, `worst` exactly as `switch_rule.py`. (a) `bayes_eq_absolute_of_all_ge`, `worst_ge_absolute` (P small), `worst_le_bayes_add` (P). (b) `two_signal_rule` (P): the mandate's rule **with a missing clause supplied** — `δ < q − π*(0) ∧ (δ ≤ π*(1) − q ∨ λ < q)`; `mandate_rule_refuted` (N+, F-19); `maxSafeDelta`, `two_signal_closed_form` (exact under the side condition; the supremum is not attained). All **eighteen** cells of `switch_rule.out` (six `λ` per block, `λ = 19/20` included): each of the eleven value cells carries the full package of `two_signal_closed_form` (`cellPkg`: positive masses, `π*(0) < q ≤ π*(1)`, side condition) and states the exact rule `worst < ℓ*(absolute) ↔ δ < x` (`cellExact`), each of the seven "none" cells proves `ℓ*(absolute) ≤ worst` for every `δ ≥ 0` (`cellNone`, via `worst_ge_absolute`) — `pause_cells`, `unit_cells`, `wholeLine_cells`; `grid_values` (F-5). The mean-zero expected-loss scoring (stretch) not attempted; shah-respondent 12 recorded only. Status: proved; extension done with the correction.

### T18 — Timestep Dominance (`Timestep`) · core (a) · D + C + N+ with the identification as a definition

Repaired in round 1 (fidelity B1). `tdRule` (D, the (c)): the landscape decision at signal `s` is the resist-bit of the option a TD agent chooses in the cost-model situation `situation (B s) (cost s) (w s)`. `tdRule_eq_absolute` (C): if the chosen option is `Maximal` for a preference satisfying `TDPrinciple` and the situation has a free option, `never_resist_costModel` makes the chosen option non-resisting at every signal, so `tdRule = absoluteRule`. `td_priced_absolute` (C): hence the class loss is `(1−λ)c` on every law. N+: `free_maximal` — in `lit-shutdown-prefs`'s byproduct situation (`base`, costs `(0, 1)`, weights `(wLong, wOne)`) the free option is `Maximal` for `TimestepDominates` itself (via `byproduct_witness`, `TD_irrefl` and the local `TD_asymm`), `costly_resists` — the costly option genuinely resists, `td_witness` — the full package inhabited at every signal with the derived rule and its price. `absolute_pair` (L). (b), (c) cited. Import deviation stated above. Status: proved; the TD theorem now does the work (the first version's hypothesis `hid` had a theorem as antecedent and was a squeeze).

### T19 — selection as reweighting (`Selection`) · stretch · T/L

`reweight_worked` (`102/113`, then `> 99/100`), `contract_closed`, `contract_tendsto` (`0 < ηm ≤ 1`), `contract_cells`. Direction and order only, as S12. Status: proved.

### T20 — the entrenching agent (`Entrench`) · stretch · D + findings

`Model` (a cost-of-pressing coordinate), `presses`, `entrenches`, `pushMass`, `unmarked` (L: the pushed class has mass `0` after the act — `λ` conditions on a null event, every row's class loss is `0`, D6′ sees no resistance), `instance_entrenches` (N+). Text: which of `Δ₋(Q)`, `R_t(Q)`, Carey–Everitt non-obstruction (Theorem 14 passes, per the judge), Turner's attainable utility (marks it, value-laden), `caution` D9's `λ`-reversibility move on it needs those packages' objects — not formalized here; K8's extension of `L` to world-acts that shape no transition is OPEN as text. Status: definitions and the unmarked lemma proved.

## Extensions

- **E1** (T15): done, two-sided, with the attained instance for `k̂ ≥ k` and the approached instance for `k̂ < k`.
- **E2(i)** (T6): one-step statements proved (`contraction_rho`, `supermart_above_rho`, `phi_step`, `phi_neg_below_rho`, `max_repair_fails`), and on the two-round product process `Φ` is a full Layer-F `IsSupermart` (`TwoRound.phi_isSupermart`: adapted to `atoms2`, the step at every `t`, kind C) that is not a potential (`TwoRound.phi_not_nonneg`). The diagnosis is exact: `d_t` is a potential in `corr-trajectory`'s sense only on `{ρ† ≤ d_t}`, `Φ` has the step everywhere inside but is not nonnegative, and the clamp fails. The `SupermartStep` form over the general horizon-`T` product space is **stated OPEN** since repair round 1 (`Horizon.phiW_supermartStep`, listed in `corr-landscape-open.txt`; adaptedness `Horizon.phiW_adapted` proved) — the obstacle is infrastructure (the prefix-atom factorization of `prodLaw`, of which `condSum_atoms2_one` is the two-round case), not a conjecture (F-21).
- **E2(ii)** (`Drift`, repair round 1): **settled**. `|β_t − β_stat|` is *not* a potential for the fresh-draw kernel — `beta_not_potential` is the cell `m = (15/22, 0, 7/22)` with `β = β_stat` exactly and `β' ≠ β_stat` (F-23); the certificate is the ℓ¹ deviation of the mass vector, non-increasing for every `0 ≤ ε` with `ε · max v ≤ 1` (`l1_nonexpansive`), with `m_stat` stationary for every `ε` (`freshStep_mstat`) and `|β − β_stat| ≤ (9/10) ‖m − m_stat‖₁` (`beta_le_l1`).
- O9, OP7: not attempted.

## Findings summary

Twenty-three entries in [corr-landscape-findings](corr-landscape-findings.md): the mandate's thirteen (F-1–F-13), ten new (F-14 the `η = 1` boundary of P5(a); F-15 the trichotomy's presupposition `m(0) ≤ m(1)`; F-16 S5's limit presumes convergence of `α_t`; F-17 check C's strict bound; F-18, F-19, F-20 corrections to the mandate's own numbers and rule; F-21 the E2(i) diagnosis, now with the OPEN statement; F-22 the legitimizing classes overlap under the unconditional baseline; F-23 E2(ii)'s `|β − β_stat|` is not a potential, the ℓ¹ mass deviation is). Two refutation rows against the sources (`ActBased.decay_fails_least`, `Erosion.switch_iff_refuted`) and one against the develop's basin (`BasinToy.stepD9_dist_lt`), each with its surviving neighbour; one refutation of the mandate's derivation (`Switch.mandate_rule_refuted`) and one of the mandate's conjectured certificate (`Drift.beta_not_potential`).

## Contamination

None. Nothing under `research/faf-lab/`, `~/.claude/projects/`, or `.claude-backup/` was read, listed or grepped; `git log` was run only with a path filter on this package's own directory.

## Repair round 1

*Repairer: Claude Fable 5.1 ([scrubbed]), 2026-10-01, fresh context. Read: both round-1 audits (`corr-landscape-audit-r1-fidelity`, `corr-landscape-audit-r1-adversarial`) and their five probes, the mandate, this report, the ledger, the findings, and the Lean they discuss. The probes were not machine-checked by the auditors (slot contention); their content is now in the library (`BasinOutside` → `BasinToy.traj_outside_drift`/`traj_outside_unbounded`/`trajD9_enters_drift`; `SwitchCells` → `Switch.cellPkg`/`cellExact`/`cellNone` and the three cell theorems; `LegitimizingOverlap` → `Legitimizing.inert_and_legitimizing`; `KappaEndpoint` and `TdSqueeze` are answered by the regrade and the redesign below) and elaborated there. Gate: **PASS** on the root + 21 modules after the last edit (`22 module(s)`, `1905 declaration(s)`, `sorryAx` only through the listed `Horizon.phiW_supermartStep`).*

### Blocking issues

| Audit · issue | Verdict | What changed (declaration names) |
|---|---|---|
| **fidelity B1** — `Timestep.td_priced_absolute` is a squeeze (`hid`'s antecedent is the theorem `never_resist_costModel`; the TD data idle; ledger Kind `C` wrong) | **fixed** (the auditor's option (ii), the real claim) | The bridge is now a **definition**: `Timestep.tdRule B cost w hw choose : S → Bool` reads the landscape decision at `s` off the resist-bit of the option `choose s` the agent takes in the cost-model situation `situation (B s) (cost s) (w s)`. `tdRule_eq_absolute` (C): with `TDPrinciple lt`, a free option `j s` and `choose s` `Maximal` at every signal, `never_resist_costModel` makes every chosen option non-resisting, so `tdRule = absoluteRule`. `td_priced_absolute` (C) is its price `(1 − λ)c` on every law. The TD theorem does the work; the (c) is `tdRule` itself, disclosed on the headline. N+: `free_maximal` (in `lit-shutdown-prefs`'s byproduct situation — `base`, costs `(0, 1)`, weights `(wLong, wOne)` — the free option is `Maximal` for `TimestepDominates` itself, via `byproduct_witness`, `TD_irrefl` and the local `TD_asymm`), `costly_resists`, and `td_witness` (the full package inhabited at every signal, the derived rule and its price). Ledger row rewritten (`D / C / C`, Hyps (c) = the definition); F-11 rewritten. |
| **fidelity B2** — F-3 misquotes `approval-final.md` S4(iii) ("as `ε_t → ε*`") and mis-scopes the imprecision to the inventory | **fixed** | F-3 now quotes S4(iii) verbatim ("`κ*_t → 1` as `ε_t → 0`", l. 57), scopes the imprecision to inventory 116 **and** S4(iii), and locates the right form in P3′ (l. 99). `Kappa.kappaStar_epsStar`'s docstring cites S4(iii) and P3′ accordingly. |
| **adversarial B1** — `Switch.unit_cells`/`wholeLine_cells` only evaluate `maxSafeDelta`; the ledger, F-19 and T17 claimed the side condition (and two-signal hypotheses) were checked per cell; "thirteen cells"; the `λ = 19/20` row omitted | **fixed** (the auditor's option (i), with the exact rule per cell) | `Switch.cellPkg l c h hl` is the full package of `two_signal_closed_form` (positive masses, `π*(0) < q ≤ π*(1)`, side condition); `cellExact l c h x hl := ∀ δ ≥ 0, worst < ℓ*(absolute) ↔ δ < x`; `cellNone l c h hl := ∀ δ ≥ 0, ℓ*(absolute) ≤ worst`; `cellExact_of_pkg` (via `two_signal_closed_form`) and `cellNone_of_all_ge` (via `worst_ge_absolute`). `pause_cells`, `unit_cells`, `wholeLine_cells` now state, for all **eighteen** rows of `switch_rule.out` (six `λ` per block, `19/20` included), the exact rule in the eleven value cells and `cellNone` in the seven "none" cells. Ledger row, report T17, F-5 and F-19 rewritten to say exactly this. |
| **adversarial B2** — the separation pair `traj_frozen_at_r`/`trajD9_enters` is graded N+ on zero disturbance sequences (constant sequences: N− by STANDARDS §3) | **fixed** (the auditor's stronger pair added; the zero pair regraded) | `BasinToy.traj_outside_drift`: against a target drifting away at rate `σ ≥ 0` (`Δ* ≡ −σ`), D9′ from `d_0 = r` stays frozen with `d_t = r + tσ`; `traj_outside_unbounded`: for `σ > 0` the error exceeds every bound; `trajD9_enters_drift`: D9 from the same data has `d_t = (1−η)^t (r − σ/η) + σ/η`, strictly inside for every `t ≥ 1` and converging to the lag `σ/η < r` whenever `σ < η r` (stronger than the probe's step-1 entry). This pair is the load-bearing row 3 (N+); `traj_frozen_at_r`/`trajD9_enters` are regraded N− ("the deterministic skeleton") in docstrings and ledger. |

### Non-blocking issues (fixed)

- fidelity N1 / adversarial N8 — `Invariant.lexicalStop_invariant` regraded **T** ("true by construction": no oversight argument; the empty-`Ov` vacuity noted); docstring and ledger.
- fidelity N2 — `BasinToy.stepD9_dist_lt` regraded **L** (the D9 instance of `step_dist_lt`'s bound; the refutation is A7.1's reading carried with the separation pair); docstring and ledger.
- fidelity N3 / adversarial N3 — `BasinToy.basin_forwardInvariant` regraded **L** (the D4 instance at hazard `0` carries no conditional content); docstring and ledger. The two mandated OPEN statements written: `Horizon.phiW_supermartStep` (E2(i), general horizon, `sorry`, listed in `corr-landscape-open.txt`; adaptedness `Horizon.phiW_adapted` proved) and E2(ii) **settled** rather than stated open (`Drift`, below).
- fidelity N4 — covered by adversarial B2 (the drift pair, with the trajectory of `d_t` under D9 in closed form).
- fidelity N5 / adversarial N10 — `ActBased.authIneq`'s docstring and ledger row record the source's own inconsistency (S6 `≥`, D7/P4 strict) and the choice; no worked cell is on the boundary.
- fidelity N7 / adversarial N9 — `Erosion.switch_iff_refuted` strengthened: the universal clause is now over **every rule** `r : Bool → Bool` (no coverage hypothesis), with the conditioned-rule form as a corollary; F-4 and the ledger updated.
- fidelity N8 — `Control.SurpriseCtrl`'s Fidelity line says it quantifies over every `i` including zero-mass states.
- fidelity N9 / adversarial N7 — `Entrench.unmarked` regraded **T/L** with the loss clause named as `0 · loss = 0`; docstring and ledger.
- fidelity N10 / adversarial N11 — ledger header: root + 21 modules (22 in the gate).
- fidelity N11 — `Kalman.Kss_inventory_bracket` relabelled **P** (a bracket computation); docstring and ledger.
- fidelity N12 — `BasinToy.contraction`'s ledger row carries F-6's sentence (the Gaussian value is not reproduced).
- adversarial N1 — `Regret.regret_approached` now takes `k̂ ≤ k` (covers the source's `k̂ = k` instance), and the "only if" is proved: `Regret.excess_lt` (strict per-signal bound for `k̂ < k`) and `Regret.regret_lt_of_lt` (every covered instance has regret strictly below the bound for `k̂ < k`), so "attained iff `k̂ ≥ k`" is now Lean, not prose.
- adversarial N2 — `Kappa.kappaStar_epsStar` regraded **L** (the regime at `ε*`, then the definition of `κ*`); docstring and ledger.
- adversarial N4 — subsumed by fidelity B1 (the redesign).
- adversarial N5 — `Legitimizing.inert_and_legitimizing` (the probe's overlap witness) added; `legitimizing`'s docstring and the ledger say the classes overlap under the unconditional baseline; finding F-22.
- adversarial N6 — `ActBased.decay_fails_least`'s Status now reads "confirmed under the source's asserted decay; the decay itself refuted by `consistent_never_fails`".
- adversarial N12 — F-1 locates the inventory's convention in 2-053's Claim line (a), not "the margin".
- adversarial N13 — `Switch.worstAt`'s docstring says the final `else` branch is reachable only for `δ < 0`.
- adversarial N14 — `Crossing.margin_tendsto`: with `α_t → α̲` and `0 ≤ β_t ≤ 1`, `m_t → −α̲` exactly (the source's limit under the convergence it assumes); ledger row added.

### Pushed further

- **E2(ii) settled** (`Drift`): `beta_not_potential` refutes the mandate's conjectured certificate — at `m = (15/22, 0, 7/22)`, `β = β_stat = 27/55` exactly and one fresh-draw step gives `β' = 5373/11000`, so `|β − β_stat|` grows from `0` (F-23). The certificate is on the mass vector: `l1_nonexpansive` (the ℓ¹ deviation from `m_stat` is non-increasing under `freshStep ε` for every `0 ≤ ε` with `ε · (9/10) ≤ 1`), `freshStep_mstat` (stationary for every `ε`), `beta_le_l1` (`|β − β_stat| ≤ (9/10) ‖m − m_stat‖₁`).
- **E2(i)**: the general-horizon statement is now precise and gate-visible (`Horizon.phiW_supermartStep`, OPEN) with adaptedness proved; the obstacle (prefix-atom factorization of `prodLaw`) is unchanged and is infrastructure.
- **Proposition R′ closed two-sidedly** (`regret_lt_of_lt`, above).

### Not done

- The strict ℓ¹ contraction rate of the fresh-draw kernel (the map is strictly contracting on zero-sum deviations) is not computed.
- The `S`-relative baseline for `legitimizing` (the repair F-22 suggests) is not built.
- `Horizon.phiW_supermartStep` remains OPEN.
