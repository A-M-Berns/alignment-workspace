# corr-landscape — findings about the sources

*[STANDARDS](../../STANDARDS.md) §5. Severity: **blocking** (the note's conclusion does not follow) / **local error** / **imprecision** / **presentation**. Every claim about what a person meant is ATTRIBUTION-UNVETTED; the sources are CLAUDE-authored and unvetted by the author. Pointers are to `research/corrigibility/workflow-2026-09-14/dynamics/` (approval lineage) and `research/corrigibility/workflow-2026-09-14b/` (landscape map, dialogue) unless stated. Lean names are in `Cleanroom.Corrigibility.CorrLandscape.` and the module is named. The mandate's thirteen known issues are F-1 to F-13 in its order; F-14 onward are new. F-18 to F-20 are findings about the **mandate** (not the sources), recorded here because the mandate asked that every witness number be recomputed.*

## F-1 — 2-053's Kalman gain convention `K_ss = P_ss/(P_ss + R)` is the updated-covariance form; P6 and the script use the predicted-covariance form · presentation (inventory, not the source)

**Where.** `corr-wf14-2-inventory` 2-053 ("`K_ss` solves … `P_ss = (P+q)R/(P+q+R)`" with `K_ss = P_ss/(P_ss + R)` in its Claim line (a), l. 609–611); `approval-final.md` P6 and `approval-repair-scratch/s8_kalman_gain.py` ("`K_ss = (Pss+q_true)/(Pss+q_true+R)`").

**What.** At `q = 1/2500`, `R = 1/400` the predicted-covariance gain is bracketed in `(327/1000, 329/1000)` (`Kalman.Kss_bracket`, the source's `0.328`), the inventory's form in `(246/1000, 248/1000)` (`Kalman.Kss_inventory_bracket`). Only the former reproduces P6's number. Both are honest conventions of the same filter; the inventory mislabelled which one the script reports.

## F-2 — 2-050's provenance: the `t = 16, 17` rows come from the repair script, not the develop's committed script · reproducibility

**Where.** `approval-final.md` S5 ("Provenance fix (A5.1)"), P3's "`ε_16 = 0.00301 > ε* > ε_17 = 0.00226`"; `approval-scratch/s3_s5_trajectory.py` (`for t in range(0,16)`, prints `first non-compliant step t* = None`); `approval-repair-scratch/s4_misspec_two_coordinates.py` (`for t in [0,3,5,6,8,10,12,15,16,17]`, `κ = 1` column).

**What.** The develop's committed script never reaches `t = 17`; the final's own text says so and points at the repair script. The crossing is now a theorem independent of either script: `Crossing.tstar_least` proves `17` is the least `t` with `ε_t < 1/361` (`ε_16 = 129140163/42949672960 ≥ 1/361 > ε_17 = 387420489/171798691840`). No numerical claim of the source is wrong; the pointer was.

## F-3 — "`1 − κ*_t → 0` as `ε_t → 0`" is loose: `κ*` reaches `1` exactly at `ε = ε*` and is undefined after · imprecision (inventory 116's title **and** the final's S4(iii); the final's P3′ has the right form)

**Where.** `corr-wf14-inventory` 116 (title: "`1 − κ*_t → 0` as `ε_t → 0`"); `approval-final.md` S4(iii), verbatim: "(iii) *Interaction*: `κ*_t → 1` as `ε_t → 0`: the tolerable misspecification `1 − κ*_t` runs 1,1,1,0.82,…,0 at `t = 0,3,6,8,10,12,15,16,17`" (l. 57) — the same loose limit, in the statement itself; the correct form "`κ*_t ↑ 1` on `[t_conf, t*]`" is in P3′ (l. 99; table row `t = 17`: "none"), not in S4(iii). (Repair round 1: the first version of this finding misquoted S4(iii) as "as `ε_t → ε*`" and scoped the imprecision to the inventory only — fidelity audit B2.)

**What.** `Kappa.kappaStar_epsStar`: `kappaStar (epsStar α β c h) β α π c h = 1` exactly, under `0 < π`, `0 ≤ α < β`, `0 < c`, `0 < h` (the channel margin vanishes at `ε*` while `m(0) < 0` there because `ε* < c/(c+h) ⟺ α < β`). For `ε < ε*` the regime `m(0) < 0 ≤ m(1)` fails and `kappaStar` is a junk quotient — "none" in the table. `Kappa.kappaStar_strictAnti` gives the monotonicity on the regime. The limit statement "as `ε_t → 0`" is the wrong limit: the relevant endpoint is `ε*`, reached at `t*`, not `∞`.

## F-4 — 065's switch "iff `δ < (1−λ)c/(c+h)`" is false as an iff · local error (dialogue)

**Where.** `dialogue/wentworth-judge.md` l. 101 ("D1's crossover `δ < (1−λ)c/(c+h)` belongs in Statement 6's neighbourhood as the row comparison at each stakes class"); `dialogue/wentworth-judge-scratch/judge_checks.py` (3) ("C-row wins iff delta < (1-lambda)*c/(c+h)"); `corr-wf14b-inventory` 065 ("the C row beats the no-lever/absolute row iff `δ < (1−λ)c/(c+h)`").

**What.** The formula drops `ℓ*(Bayes)` from Proposition R′'s bound and reads the sufficient condition as necessary. `Erosion.switch_iff_refuted`: at Toy T pause stakes with `λ = 7/10`, `π*(0) = 7/34 > q = 1/5`, so the Bayes rule *is* absolute acceptance (`bayesRule toySeven 1 4 0 = absoluteRule`) and **every rule whatsoever** — hence every conditioned rule at every `δ`, covered or not — has `ℓ*(r) ≥ ℓ*(absolute)`: no `δ` makes the conditioned row strictly better, while `(1−λ)c/(c+h) = 3/50 > 0`. (The refutation needs no coverage hypothesis; the first version carried one idly — audit r1 N7/N9.) Reading formalized (ATTRIBUTION-UNVETTED): "wins" as strict improvement. **Surviving neighbour:** the sufficient direction `ℓ*(Bayes) + (c+h)δ + |k̂ − k| < (1−λ)c ⟹ ℓ*(cond) < ℓ*(absolute)` (`Erosion.switch_sufficient`, over T15 and T13) and the exact two-signal rule under worst-case scoring (`Switch.two_signal_rule`).

## F-5 — 2-005's tabulated max-safe `δ` are `1/400`-grid values; the exact supremum is `q − π*(0)` (under a side condition), not attained · presentation

**Where.** `dialogue/hudson-voice.md` item 2 (l. 81), `hudson-voice-scratch/switch_rule.py` (`max_safe_delta(..., grid=400)` scans `F(i, 400)` and keeps the last `i` with `w < abs_loss`), `.out` (`0.1875, 0.1525, 0.0975`); `dialogue/hudson-respondent.md` C2 ("The table re-runs exactly").

**What.** `Switch.grid_values`: `75/400 < 77/410 ≤ 76/400`, `61/400 < 17/110 ≤ 62/400`, `39/400 < 1/10 ≤ 40/400` — each tabulated value is the largest grid point strictly below the exact bound. The respondent's "re-runs exactly" reproduces the grid, not the closed form. The exact bounds, `Switch.pause_cells`/`unit_cells`/`wholeLine_cells` (each value cell now states the exact rule `worst < ℓ*(absolute) ↔ δ < x` for every `δ ≥ 0`, with the full package of `two_signal_closed_form` checked in the cell): pause `77/410, 17/110, 1/10`; `c = h = 1`: `20/41, 5/11, 2/5, 5/17`; whole-line `359/820, 89/220, 7/20, 83/340`; "none" (proved as `ℓ*(absolute) ≤ worst` for every `δ ≥ 0`) where `π*(0) ≥ q` — eighteen cells, the script's six `λ` values per block including `λ = 19/20`. At `δ = q − π*(0)` the worst case *is* the absolute row (`Switch.two_signal_closed_form`): the supremum is not attained, which is why the grid stops one step below (`1/10 = 40/400` exactly is unsafe). See F-19 for the side condition.

## F-6 — S7's `ρ† = ξ̄/2 + σ̄*/(2η)` is the continuous-uniform value; a finite law gives its own `E|ξ|`, `E|Δ*|` · disclosure (no (c) in the shipped witness)

**Where.** `approval-final.md` S7(b), P5(b) ("Uniform noise: `E|ξ_t| = ξ̄/2`"); A7.4 (`√(2/π)` for the Gaussian case).

**What.** `BasinToy.contraction` is stated for an arbitrary finite law with `ρ† := (η E|ξ| + E|Δ*|)/η` (`rhoDagger`). The symmetric three-point law `{−b, 0, b}` with masses `(1/4, 1/2, 1/4)` has `E|ξ| = b/2` exactly (`expect_abs_threeVal`), so the joint three-point law reproduces the source's `ρ† = 9/200` (`rho_worked`) with no modelling substitution: the uniform law has no finite shadow, but its first absolute moments do. The Gaussian value is not reproduced (F-8).

## F-7 — 2-049: "the act-based agent without drills fails at `t = 10`" holds only under the develop's asserted decay and contradicts its own model · refutation row with surviving neighbour

**Where.** `approval.md` S6 l. 69 ("In the worked trajectory the act-based agent without drills fails at `t = 10`; with drills never"); `approval-scratch/s3_s5_trajectory.py` (`pA = pA0*decay**t`, prints "AD without drills first fails at t = 10"); killed by `approval-adversary.md` A6.2 and `approval-adversary-scratch/s6_consistent_pA.py`; `approval-final.md` S6.

**What.** Under the asserted decay `p^A_t = (3/10)(3/4)^t` the least failing index *is* `10` (`ActBased.decay_fails_least`, kind N−: `ε_9 = 2187/… ≥ 1/50 > ε_10`), so the arithmetic was right and the model was wrong: nothing in the develop makes the authentic-press rate decay to `0`. Under the parameterization consistent with the develop's own P3 (`p^A_t = ε_t β + (1−ε_t) α → α`), act-based compliance never fails (`consistent_never_fails`), and in general never fails iff the floor `α/(α+γ)` passes (`never_fails_iff_floor`), i.e. fails in the limit iff `γ > α/c''` (`fails_in_limit_iff`; `= 1/20` at the worked values, `γ = 1/50` passes). **Surviving neighbour:** T5(b).

## F-8 — 2-052(b): Gaussian noise has no finite shadow; "no a.s. invariant ball under unbounded noise" is recorded as text · scope

**Where.** `approval-adversary.md` A7.3 ("With Gaussian `ξ_t, Δ*_t` there are no bounds … the per-step exit probability is positive for every `r`"); `approval-final.md` S7 (bounded noise adopted in D9′).

**What.** Not formalizable in Layer F (a `Distr` on a finite type has bounded support; every finite law *has* an invariant ball above its noise scale, which is `BasinToy.step_dist_lt` with `ξ̄ = max|ξv|`). The statement "under unbounded noise no ball is almost-surely invariant" is true and elementary in Layer M (positive mass outside any bound on one step) but was not attempted: the package is Layer F by mandate. Recorded as text; the final's own move to bounded noise (D9′) is what the Lean follows.

## F-9 — S10's (A-amp) is CLAUDE's assumption; the capped quantity is decision quality · scope

**Where.** `approval-final.md` D10, S10, P8; A10.2–A10.4.

**What.** `Amplify.linear_cap` carries both hypotheses as clauses, the docstring classifies `q_{t+1} ≤ q_0 + k_t` as (c) (the source's own modelling assumption, denied by Christiano's line 19 in the limit) and `k_{t+1} ≤ q_{t+1}` as the min-cap. Kind L; nothing more is claimed.

## F-10 — 061: D1a/D1b are unvetted construals; "legitimizing ⟹ accuracy-increasing" for literal adoption is conjectured (OP5), not a target · register

**Where.** `landscape-final.md` S2 (D1a "[CLAUDE construal of v1 §2.10 …]", "Relation [derived, for the push-conditional; conjectured, for literal adoption]"), Open problem 5.

**What.** The map's objects (`Map`) are drawn under D1a, as the source says; `legMass`/`lam` are the law of (signal, `L^push`) and nothing is called `Legitimate`. No theorem relates D1a to accuracy. OP5 is not formalized.

## F-11 — 2-006(a) is a placement; the TD → absolute-row bridge is a modelling identification (c) · disclosure

**Where.** `dialogue/thornley-respondent.md` P1 ("Timestep Dominance is the absolute row of the same map, priced by `landscape` Statement 1 at `(1−λ)c`").

**What.** The two finite developments (lotteries over trajectories; a law over signals) share no object, and plan §0.4 rule 10 plans no bridge. The smallest bridge that lets the TD theorem do work is a **definition**: `Timestep.tdRule` reads the landscape decision at signal `s` off the resist-bit of the option a TD agent chooses (`Maximal` for its preference) in a cost-model situation with a free option. Then `tdRule_eq_absolute` is `lit-shutdown-prefs`'s `never_resist_costModel` at every signal, and `td_priced_absolute` prices it at `(1−λ)c` by Statement 1; the (c) is the identification embodied in `tdRule`, disclosed on the headline. The N+ (`td_witness`) uses `lit-shutdown-prefs`'s own byproduct situation: a two-option menu whose costly option genuinely resists and whose free option is `Maximal` for `TimestepDominates` itself. (Repair round 1: the first version took the bridge as a hypothesis `hid` whose antecedent was the theorem `never_resist_costModel`, so the TD data were idle and the row was a squeeze — fidelity audit B1.) (b), (c) of 2-006 are `lit-shutdown-prefs`'s `TD_dodge_comply` and `maximal_congr_menu`, cited.

## F-12 — 063(b) needs nonempty `R` and `A` with positive mass; 062's strictness needs a signal strictly on each side of `q_k` · imprecision (made exact)

**Where.** `landscape-final.md` Statement 3(b) ("If `π̄_R > π̄_A`"), P3; Statement 2 ("strictly whenever two positive-probability signals straddle `q_k`").

**What.** `Trichotomy.anti_informative_worse` carries `0 < p_R`, `0 < p_A` (the averages `π̄_R, π̄_A` are undefined otherwise, and with `R` or `A` empty `r` is a constant). `Map.loss_bayes_lt_absolute` / `loss_bayes_lt_none` / `loss_bayes_lt_both` carry the strict hypotheses `∃ s, μ(s, L) < q_k P*(s)` and `∃ s, q_k P*(s) < μ(s, L)` (each forces positive mass); a tie `π*(s) = q_k` gives equality (`none_eq_bayes_iff` says exactly when the none row ties the Bayes row).

## F-13 — Everything Monte Carlo is not a theorem and is not reproduced · scope

**Where.** `approval-final.md` S7 (zero exits in `200 × 5000`, mean final `d`), S8 (`0.108/0.400/1.281`, `0.024` vs `0.69`), P6; `landscape-final.md` R1 (20 000 instances), R2 (24 232 instances), C2 (3000).

**What.** Replaced by the theorems they illustrate: `BasinToy.traj_dist_lt` (every bounded disturbance sequence, not a sample), `Kalman.Kt_ge` (the gain floor), `Regret.regret_le` (every instance), `Trichotomy` (every finite signal space). The numbers are not restated as claims.

## F-14 — P5(a)'s invariant "`d_{t+1} < r` whenever `η ξ̄ + σ̄* ≤ η r`" silently uses `η < 1` · local imprecision (new)

**Where.** `approval-final.md` D9′ ("gain `η ∈ (0,1]`"), S7(a), P5(a) ("`d_{t+1} < (1−η)r + η ξ̄ + σ̄* ≤ r` iff `η ξ̄ + σ̄* ≤ η r`").

**What.** The first strict inequality multiplies `d_t < r` by `1 − η`, which is strict only for `η < 1`. At `η = 1` with equality in the condition the step can land exactly on `d = r`: `BasinToy.eta_one_boundary` (`η = r = 1`, `ξ̄ = σ̄* = 1/2`, `d_0 = 0`, `ξ = 1/2`, `Δ* = −1/2` gives `d_1 = 1`). `step_dist_lt` is stated for `0 < η < 1`; `step_dist_lt_of_strict` recovers `η ≤ 1` under the strict condition `η ξ̄ + σ̄* < η r`. The worked toy (`η = 1/2`) is unaffected.

## F-15 — P3′'s trichotomy in `κ` presupposes `m(0) ≤ m(1)` · imprecision (new)

**Where.** `approval-final.md` P3′ ("If `m(0) ≥ 0`, compliance holds for every `κ` …; if `m(0) < 0 ≤ m(1)`, the crossing …; if `m(1) < 0` compliance fails for every `κ`").

**What.** `m(κ) = (1−κ) m(0) + κ m(1)` is a convex combination, so "`m(0) ≥ 0 ⟹ all κ`" needs `m(1) ≥ 0` too and "`m(1) < 0 ⟹ no κ`" needs `m(0) < 0` too; the three cases are exhaustive only when `m(0) ≤ m(1)`, which holds under `α ≤ π ≤ β` (and `u ≥ 0`): `Kappa.effMargin_zero_le_one`. The worked parameters satisfy it (`1/20 < 3/10 < 9/10`). `comply_all_of_nonneg` and `fail_all_of_neg` carry both endpoint signs explicitly.

## F-16 — S5's general limit "`m_t → −α̲ < 0`" presumes `α_t` converges · imprecision (new)

**Where.** `approval-final.md` S5 ("Along any trajectory with `ε_t → 0`, `α_t ≥ α̲ > 0` and `β_t ≤ 1`: `m_t → −α̲ < 0`").

**What.** With only `α_t ≥ α̲` the margin need not converge (`α_t` may oscillate above `α̲`); what the crossing uses is the eventual bound. `Crossing.margin_eventually_neg`: eventually `m_t ≤ −α̲/2 < 0` (Fidelity: weaker, stated). With `α_t → α` the limit is `−α ≤ −α̲`, which the source may have meant; ATTRIBUTION-UNVETTED.

## F-17 — Check C's "resists for all `k̂ ≤ 0.5`" is the strict bound `k̂ < 1/2` · presentation (new)

**Where.** `landscape-final.md` D6′ (check C: "at `p_push = 0.1, π̂ = 0.1, c = 1, h = 4` the push-time rule resists for all `k̂ ≤ 0.5`, the anticipatory rule stops at `k̂ = 0.05`").

**What.** D6′'s inequality is strict (`> k̂`): `Erosion.checkC` gives `erodes 1 (1/10) 1 4 k̂ ↔ k̂ < 1/2` and `erodes (1/10) (1/10) 1 4 k̂ ↔ k̂ < 1/20`. At `k̂ = 1/2` exactly the push-time rule does not resist. A grid reading.

## F-18 — The mandate's T11 witness "holds at `α = 1/20` and fails at `α = 1/2` (worked `ε_0`)" is wrong at `β = 9/10` · mandate correction

**Where.** Mandate T11(i).

**What.** At `ε_0 = 3/10`, `h/c = 20`, `β = 9/10` the compliance inequality `(1−ε) c α ≤ ε h β` reads `0.7 α ≤ 5.4`, true for every `α ≤ 1`: no change of `α` alone breaks it at `t = 0`. `Invariant.vlCompliance_not_invariant` uses the oversight pair `(α, β) = (1/2, 1/100)` for the failing state (and `(1/20, 9/10)` for the holding one); the conclusion — D1 is not an invariant of the agent in the VL frame — is unchanged. The same pair is T4(c)'s over-trust/FUD cells (`Crossing.cells_witness`).

## F-19 — The mandate's T17 "exact rule: … iff `δ < q − π*(0)`" lacks a clause; the closed form needs a side condition · mandate correction (the mandate said "verify, do not take")

**Where.** Mandate T17(b).

**What.** With `π*(0) < q ≤ π*(1)` the band can straddle `s = 1` as well once `δ > π*(1) − q`; then the adversary resists at both signals and the worst case is the *none* row, which beats absolute iff `λ < q`. `Switch.two_signal_rule`: `worst < ℓ*(absolute) ⟺ δ < q − π*(0) ∧ (δ ≤ π*(1) − q ∨ λ < q)`. `Switch.mandate_rule_refuted`: `p_0 = 1/5`, `p_1 = 4/5`, `π*(0) = 3/10`, `π*(1) = 1/2`, `c = 9`, `h = 11` (`q = 9/20`), `δ = 1/10 < 3/20 = q − π*(0)`, yet worst `253/50 > 243/50 = ℓ*(absolute)` (`λ = 23/50 ≥ q`, `δ > 1/20 = π*(1) − q`). Under the side condition `q − π*(0) ≤ π*(1) − q ∨ λ < q` the closed form is exact (`two_signal_closed_form`), and in every value cell of `switch_rule.out` the full package — positive masses, `π*(0) < q ≤ π*(1)`, and the side condition — holds: `pause_cells`, `unit_cells`, `wholeLine_cells` check it per cell (`Switch.cellPkg` through `cellExact_of_pkg`) and state the exact rule, so the voice's numbers stand. (Repair round 1: the first version's `unit_cells`/`wholeLine_cells` only evaluated `maxSafeDelta` and the finding over-claimed what they checked — adversarial audit B1.)

## F-20 — The mandate's T2 box exits `[0,1]` in `β`; harmless · presentation (source S4(i) and mandate)

**Where.** `approval-final.md` S4(i) ("`|Δβ| ≤ 0.3`" around `β = 9/10`); `s4_misspec_two_coordinates.py` (perturbs `beta+db` with `db ∈ {−0.3, 0, 0.3}`); mandate T2.

**What.** `β = 6/5` is not a rate. `Margin.box_worst_corner` proves the bound over the box as stated (`β ∈ [3/5, 6/5]`); the worst corner is at `β = 3/5`, inside `[0,1]`, so the result and the number `391/100` stand for the clipped box too.

## F-21 — E2(i): the `SupermartStep` form of the contraction over the general horizon is stated OPEN; diagnosis · scope (mandate extension)

**Where.** Mandate T6(e), E2(i).

**What proved.** One-step: `BasinToy.contraction_rho` (`E[d'] ≤ (1−η)d + ηρ†` on the inside), `supermart_above_rho` (`d` is a one-step supermartingale on `{ρ† ≤ d < r}`), `phi_step` (`Φ_t = (1−η)^{−t}(d_t − ρ†)` satisfies the step everywhere inside), `phi_neg_below_rho` (not nonnegative below `ρ†`, so not an `IsPotential`), `max_repair_fails` (the clamp `max(Φ, 0)` is not a one-step supermartingale: at `d = ρ†` the expectation of the clamped next value is positive on the worked law). **Proved on two rounds:** `TwoRound.phi_isSupermart` — on `prod2 ν ν` with the filtration `atoms2` (everything / the first letter / singletons), `Φ` is a full `IsSupermart` (adapted, step at every `t`), through the two-round factorization `condSum_atoms2_one`; `phi_not_nonneg` says it is not a potential. **Stated OPEN (repair round 1):** `Horizon.phiW_supermartStep` — `SupermartStep (prodLaw T ν) (prefixAtoms T) (PhiW …) t` for `t < T`, the general horizon, with a `sorry`, listed in `corr-landscape-open.txt`; adaptedness of `Φ` to the prefix filtration is proved (`Horizon.phiW_adapted`). **Why it stalled:** the conditional sum over a prefix atom of the product law factors as (mass of the prefix) × (one-letter expectation) × (sum over the suffixes = 1), which needs a bijection between the atom and `A × (words on the remaining indices)` over `Fin T → A`; the Finset bookkeeping is the whole difficulty (infrastructure, not a conjecture). The honest statement of the certificate: `d_t` is a potential in `corr-trajectory`'s sense only on the region `{ρ† ≤ d_t}`, and `max(d_t − ρ†, 0)` is not one. E2(ii) is F-23.

## F-22 — S11(a)'s three classes are not a trichotomy under the unconditional baseline: an inert verdict can be legitimizing · imprecision (new; audit r1 adversarial N5)

**Where.** `approval-final.md` S11(a) (inert / legitimizing / delegitimizing), P9; `Legitimizing.legitimizing` (this package).

**What.** The source's "inert" is "carries no information *for `P_t`*", i.e. relative to the agent's own state `S`; "legitimizing (raises expected accuracy)" leaves the baseline unspecified. Formalized against the *unconditional* prior mean, a verdict that is a function of `S` alone is both inert and legitimizing whenever `S` is informative about the target: `Legitimizing.inert_and_legitimizing` (uniform law on `Bool × Bool`, target `𝟙[S = true]`, verdict `φ e s = s`: quadratic score `1/4 → 0`). The classes overlap as formalized; the `S`-relative baseline (condition on `V` jointly with `S`, as `inert_null_update` already does) is the natural repair and is not built here. Disclosed in the docstring and the ledger; the source's prose needs the baseline stated.

## F-23 — E2(ii): `|β_t − β_stat|` is **not** a potential for the fresh-draw kernel; the certificate is the ℓ¹ deviation of the mass vector · refutation of the mandate's conjecture (new)

**Where.** Mandate E2(ii) ("the fresh-draw kernel's `|β_t − β_stat|` as a potential (linear contraction to the stationary mass)"); wentworth-respondent item 2, `selection_drift.py`.

**What.** `β_{t+1} = (1 + (ε/3)∑v) β_t − ε ∑_v v² m_v` depends on the second moment of the mass, not on `β_t` alone, so no scalar function of `β_t` is a one-step certificate: `Drift.beta_not_potential` — at `m = (15/22, 0, 7/22)` (a probability vector) `β = β_stat = 27/55` exactly, and one step at `ε = 1/10` moves `β` to `5373/11000 ≠ 27/55`, so `|β − β_stat|` grows from `0`. The certificate lives on the mass vector: `Drift.l1_nonexpansive` — `∑_v |m_v − m_stat,v|` is non-increasing under `freshStep ε` for every `0 ≤ ε` with `ε · max v ≤ 1` (triangle inequality, exact), `m_stat ∝ 1/v` is stationary for every `ε` (`freshStep_mstat`), and `|β − β_stat| ≤ (max v) ‖m − m_stat‖₁` (`beta_le_l1`). The mandate's "linear contraction" is right for the vector dynamics (non-expansive in ℓ¹; strictly contracting on zero-sum deviations, not proved) and wrong for the scalar.
