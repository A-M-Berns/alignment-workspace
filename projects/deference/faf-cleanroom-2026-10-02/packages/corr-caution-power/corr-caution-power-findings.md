# corr-caution-power — findings about the sources

*Findings per [STANDARDS](../../STANDARDS.md) §5, with severity (blocking the note's conclusion / local error / imprecision / presentation) and a pointer. Sources: `research/corrigibility/workflow-2026-09-14/dynamics/caution-final.md` (cited as `caution-final.md` with line numbers), `dynamics/caution-adversary.md`, `references/11-adjacent/taylor-2016-quantilizers-a-safer-alternative-to-maximizers.md` (Taylor), `workflow-2026-09-13/critique/turner.md`, and the mandate `corr-caution-power-mandate`. Lean pointers are declarations in `Cleanroom/Corrigibility/CorrCautionPower/` (namespace `Cleanroom.Corrigibility.CorrCautionPower` omitted). Every `[checked]` mark in the sources is a Python script on random instances; here the same statements are exact.*

## F-1 — D10's printed pointwise predicate is vacuous at `∅`, so S5(b)'s repaired "ratio" theorem is false as printed (local error; blocking for the repaired S5(b) as stated)

**Pointer.** `caution-final.md` D10 (l. 55: "for every `t ≤ T` and every `a ∈ supp γ_t` — all base actions, old and new, and the null action `∅` — either `a ∈ C_t(δ)` (covered) or `ĉ_t(a) ≥ c_t(a)` (known-uncovered)"), S5(b) (l. 69: "Under D10's pointwise form (all of `supp γ_t` including `∅`, at `t`): `R̂_t ≥ R_t − 2δ`"), proof §5 (l. 129: "on covered `a`, Jensen gives … `≥ c_t(a) − 2δ` (§2, using `∅ ∈ C_t`)").

**What is wrong.** By D4, `c_ω(∅) = (V_ω(∅) − V_ω(∅))⁺ = 0` for every `ω`, so at `a = ∅` the "known-uncovered" disjunct `ĉ_t(∅) ≥ c_t(∅)` is `0 ≥ 0` and holds always. The clause "and the null action `∅`" — added after adversary A2.2 precisely to make S2's hypothesis `∅ ∈ C_t(δ)` available — therefore constrains nothing (`CautionState.coveredOrKnownUncovered_iff`, Setting.lean). The proof of S5(b) then uses `∅ ∈ C_t`, which the predicate does not supply. The conclusion `R̂_t ≥ R_t − 2δ` is **false** under the printed predicate: `Witnesses.printed_predicate_no_CORδ` — `A = {a, ∅}`, `Ω = {ω*, ω′}`, `P = (1/2, 1/2)`, `V_{ω*} = (0, 1)`, `V_{ω′} = (0, 2/5)`, `δ = 1/20`, uniform base: `a` is covered (`e(a) = 0`), `∅` is not (`e(∅) = −3/10`), the printed predicate holds, and `R − 2δ = 2/5 > 7/20 = R̂`. (`Witnesses.not_printed_predicate_implies_CORδ` states the negation.)

**Nearest well-posed version (proved).** Replace the predicate by `NullCoveredKnownUncovered δ := ∅ ∈ C(δ) ∧ ∀ a ∈ supp γ, a ∈ C(δ) ∨ c(a) ≤ ĉ(a)` (Setting.lean). Under it both halves of the repaired S5(b) hold: `CautionState.baseHarm_sub_le_estBaseHarm` (`R − 2δ ≤ R̂`) and `CautionState.realizedHarm_le_known_cost` (`H ≤ k + 2δ + max{η, R̂}`), CautionRule.lean. The source needs to state `∅ ∈ C_t(δ)` as *coverage of the null action*, not fold it into the disjunction.

## F-2 — The S5(b) counterexample lies outside D1's standing realizability assumption (imprecision)

**Pointer.** `caution-final.md` S5(b) (l. 69: "point-mass posterior with `V(∅) = V(a) = 0.5`, truth `0.5 ± δ`"), proof §5 (l. 129), adversary A5.2 (l. 49: "`Ω = {ω₁}` … truth `V*(∅) = 0.5 + δ`"); D1 (l. 25: "Standing assumption … `ω*_t ∈ Ω`").

**What is imprecise.** The adversary's witness as written (A5.2: `Ω = {ω₁}`, truth `V* ∉ {V_{ω₁}}`) puts the target outside the algebra, violating D1's standing assumption `ω* ∈ Ω`; the identity `E_P[R_ω] = R̂` (`expect_baseHarmOf`) still holds, but its *interpretation* as a posterior estimate of `R` needs the target to be a possible hypothesis. The final's own phrasing (l. 69: "point-mass posterior … truth `0.5 ± δ`") is realizable *inside* D1 — `Ω = {ω₁, ω*}`, `P = δ_{ω₁}`, target `ω*` with `P(ω*) = 0`, the shape of `estZeroState` — so the final is not wrong, only silent about the posterior; Witness B additionally gives the target positive mass (severity adjusted at audit r1 N4).

**Repair (proved).** `Witnesses.witnessB_refutes_COR`: `Ω = {ω₁, ω*}`, `P(ω*) = 1/2`, `V_{ω₁} = (1/2, 1/2)`, `V_{ω*} = (1/2 − δ, 1/2 + δ)` at `δ = 1/4` — inside `[0, 1]`, target in `Ω`, both actions `δ`-covered (errors `±1/8`), so even the corrected predicate F-1 holds, and `R̂ = 1/8 < 1/4 = R`. The refutation of "pointwise ⟹ COR" survives realizability (`Witnesses.not_pointwise_implies_COR`).

## F-3 — Taylor 2016, Lemma 2: the printed proof covers only the support of `γ` (presentation; paper)

**Pointer.** Taylor l. 105–113 (Lemma 2 and its proof: `c(a) = 1/γ(a*)` if `a = a*`).

**What is incomplete.** The proof divides by `γ(a*)`, so it establishes `p(a) ≤ t γ(a)` only where `γ(a) > 0`. The statement is right: off the support, `c = K · 1_a` for every `K > 0` has `E_γ[c] = 0 ≤ 1` and `E_p[c] = K p(a) ≤ t`, which forces `p(a) = 0`. Formalized in full in `fits_under_base` (Quantilizer.lean).

## F-4 — The gloss counterexample cannot be realized with a point-mass posterior (local error in the mandate; the source's numbers are consistent inside `[0, 1]` once "all else harmless" is read as harmless *in truth*)

**Pointer.** `caution-final.md` S3 (l. 65: "with `ρ_t = 1`, `η = 0.1`, a thousand uniform base actions and the one harmful action proxy-top"), proof §3 (l. 121); adversary A3.2 (l. 35); mandate T3 ("`P = δ_{ω*}` so `R̂ = R = 1/n`, proxy ranking `a°` top").

**What is wrong.** Under D2/D4, at a point-mass posterior `P = δ_{ω*}` the proxy *is* the truth, `U = V_{ω*}`; an action ranked top by the proxy then has `V_{ω*}(a°) ≥ V_{ω*}(∅)`, i.e. `c(a°) = (V_{ω*}(∅) − V_{ω*}(a°))⁺ = 0`. So "`P = δ_{ω*}`, `a°` proxy-top, `c(a°) = 1`" is contradictory. The source's text only asks for `ρ_t = 1` (not a point mass), which is consistent; whether its script (`checks.py` §5) used Taylor's independent ranking `U` and cost `c` rather than D2's proxy was not verified here (the script was not read). **Sharpened at audit r1:** inside `[0, 1]`, `c(a°) = 1` forces `V*(a°) = 0`, `V*(∅) = 1`; for `a°` to be proxy-top the other hypothesis must rate `a°` above `∅` by enough to beat `P(ω*)`, and `R̂ = R = 1/N` then forces estimated harm somewhere else — so the source's "all else harmless" (proof §3, l. 121) is consistent only read as *harmless in truth*, with decoys the posterior fears. One decoy cannot do it in range (it would need harm `1` under `ω′`, forcing `V_{ω′}(∅) = 1 > U(a°)`); two can.

**Repair (proved; rebuilt at audit r1).** `Witnesses.gloss_refuted` on `Fin (n+4)`: two hypotheses, `P = (3/10, 7/10)`, target `ω*`; `V_{ω*} = 1` except `V_{ω*}(a°) = 0`; `V_{ω′} = 0` on two decoys, `1/2` on `∅` and the rest, `1` on `a°` — every value in `[0, 1]` (`glossState_inRange`). Then the proxy is `3/10` on the decoys, `13/20` on `∅` and the rest, `7/10` on `a°` — top; the natural order is compatible (`glossState_proxy_compatible`) — `c(a°) = 1` and `c = 0` elsewhere, `ĉ(a°) = 3/10`, `ĉ(bᵢ) = 7/20`, so `R = R̂ = 1/(n+4)` (`ρ = 1` exactly). With `η ≤ 1 < (n+4)η`: `q = 1/((n+4)η)`, `Q(a°) = η`, `H = η = (n+4)η · R > R`. `InRange` and `Compatible` are conjuncts of the theorem. The source's numbers `n = 1000`, `η = 1/10`, `H = 1/10 = 100 R` are `Witnesses.gloss_refuted_1000` (`Fin 1000 = Fin (996 + 4)`). (Round 0's witness had `V_{ω′}(a°) = 3`, outside D1's range, and the refutation was therefore established only on a state the source's model excludes — audit r1 B1; the in-range construction is the adversarial auditor's `Fin 4` probe, parametrized.) The gloss "never worse than sampling the base" is refuted; the surviving statement is the disjunction `CautionState.realizedHarm_qRule_cases` and `H ≤ max{R, η}` (`realizedHarm_qRule_le_max`) — which is the formal clause of the very sentence quoted (`caution.md` l. 71), so the source's *formula* was right and its *gloss* wrong.

## F-5 — S4(b): D8's distinctive content does not survive algebra misspecification (imprecision; recorded, the source already says so)

**Pointer.** `caution-final.md` S4(b) (l. 67), adversary A4.2 (l. 41); mandate T3 S4(b).

**Record.** Under misspecification `q_t = min{1, R̂_t/η}` reads a corrupted `R̂_t`; at `R̂_t = 0` it gives `q_t = 0`, where the quantilizer is undefined (division by zero in `qmass`; `Quantilizer.lean` requires `0 < q`) and the bound `R/q` is vacuous. The Lean pointer is `Witnesses.s1_estZero_trueHarm_pos`: `R̂ = 0 < R = 1/2`, `qRule η 0 = 0`, `qRuleFloored q_min η 0 = q_min`. What survives is Lemma 1 for *any* nonnegative cost (`quantilize_cost_bound`, no `Ω` in the statement) and the floored rule's `H ≤ R/q_min` (`CautionState.floored_cost_bound_misspec`, stated for an arbitrary true value function outside `Ω`; tight by `Witnesses.floored_tight_misspec`).

## F-6 — S4(c)'s joint bound needs `0 < R̂` as a load-bearing hypothesis (imprecision; junk value)

**Pointer.** `caution-final.md` S4(c) (l. 67: "`H_t ≤ min{R_t/q_min, max{R_t, ηρ_t}}`"); mandate "Known issues" 4.

**Record.** The source's `ηρ_t` is `ηR_t/R̂_t`; at `R̂_t = 0` its convention is `ρ = +∞` (so the max is `+∞` and the min is `R/q_min`), but Lean's `x/0 = 0` would make the clause `H ≤ min{R/q_min, R}`, which the state of F-5 violates when `q_min < 1`. `CautionState.realizedHarm_floored_le_min` carries `0 < R̂` explicitly; the robust clause `realizedHarm_floored_le_robust` carries nothing.

## F-7 — S6(b)'s "within budget iff `R̂_t ≥ g`" is the special case `c_t(a°) = 1` (imprecision)

**Pointer.** `caution-final.md` S6(b) (l. 71), proof §6 (l. 133: "`≤ η` iff `R̂_t ≥ g c_t(a°)`, in particular iff `R̂_t ≥ g`"); adversary A6.2 (l. 57).

**Record.** The exact condition is `g · c_t(a°) ≤ R̂_t` (`CautionState.isolated_error_within_budget_iff`); "in particular iff `R̂_t ≥ g`" holds only when `c_t(a°) = 1` (or as a sufficient condition when `c_t(a°) ≤ 1`, i.e. under D1's range). The statement S6(b) drops the factor.

## F-8 — Taylor's two-game cost has no additive decomposition; "per-step bounds sum to `0`" (imprecision, made exact)

**Pointer.** `caution-final.md` S5(a) (l. 69), proof §5 (l. 129: "Per-game marginal cost of every single action is `0`, so each per-step S3 bound is `0`"); adversary A5.1 (l. 47).

**Record.** "Per-game marginal cost" is not defined in the source. What is true and exact: the cost `c(a₁, a₂) = 1[(a₁, a₂) = (2, 2)]` admits **no** additive decomposition `c₁(a₁) + c₂(a₂)` at all (`twoGame_cost_not_additive`, four cells and `linarith`), so no per-step cost exists to be bounded; independent `1/3`-quantilizers pay `1` against the base's `1/9` (`twoGame_independent`), the joint quantilizer pays `1/3` under every compatible tie-break (`twoGame_joint`), and `9 = (1/3)⁻²` shows the compounding bound tight at `n = 2`; `nGame_sharp` shows `3ⁿ` attained for every `n`.

## F-9 — 2-088's "exact composition law": (d3)'s "if" direction is false; the product of quantilizers is not a quantilizer in general (finding on the plan's extension item)

**Pointer.** `plan/formal.md` l. 209 (the extension of record: "The exact composition law for two quantilizers in sequence, or the witness that no additive law exists"); mandate T4(d2)–(d3).

**Record.** (d2) `prod2_quantilize_not_quantilizer`: `Q_{3/4}[uniform Fin 2] ⊗ Q_{3/4}[…] = (1/9, 2/9, 2/9, 4/9)` is not `Q_{q′}` of the uniform-on-four base under any tie-break at any level (a quantilizer has at most one partial atom, `partial_unique`, and equal masses on full atoms). (d3), the conjectured law `Q_q[γ₁] ⊗ Q_q[γ₂] = Q_{q²}[γ₁ ⊗ γ₂]` "iff no boundary splits an atom": the **"if" direction is false** — `d3_no_split_not_joint`: `U = (0, 1, 10)`, uniform, `q = 2/3` (no split: the boundary is an atom edge, `quantilize_fin3_two_thirds`), `Q ⊗ Q` puts `1/4` on `(1, 1)` but every order compatible with `U(a₁) + U(a₂)` puts `5/9 > 4/9` of base mass above `(1, 1)`, so the joint `q²`-quantilizer puts `0` there. The "only if" direction (equality forces no split) was not attempted; it is the open remainder of 2-088. **The refutation is reading-specific** (audit r1 §3.4): "product-compatible ranking" was read as "compatible with `U(a₁) + U(a₂)`" — Taylor's own additive `U(o₁, …, oₙ) = ∑ Uᵢ(oᵢ)` (l. 178) — and under that reading there is no exact law of this shape. Under a linear order whose top-`q²` initial segment is `T₁ × T₂` (the product of the two full top sets), the "if" direction *holds* in the no-split case: `Q ⊗ Q = γ₁γ₂/q²` on `T₁ × T₂` and `0` elsewhere, which is what `qmass_of_aboveEq_le` / `qmass_of_le_above` give for the `q²`-quantilizer of `γ₁ ⊗ γ₂` under such an order (not machine-checked; a concrete `LinearOrder (Fin 3 × Fin 3)` was not built). So the law's truth is a property of the product ranking, not of the product base; the honest statement under the sum ranking is the compounding bound `q⁻ⁿ` with its sharpness.

## F-10 — Model M: "Bayes factor exactly 1" is trivial once `p_th = p_reck`; the content is well-formedness and threshold monotonicity (imprecision in emphasis; proved)

**Pointer.** `caution-final.md` S8(b) (l. 77), proof §8 (l. 147); adversary A8.3 (l. 69); mandate "Known issues" 6.

**Record.** `ModelM.pressProb_alphaTH` (exact algebra under `ε ≠ 1`) makes `likelihood_th_eq_reck`, `bayesFactor_th_reck_eq_one` and `postOdds_eq_priorOdds` immediate. The two things that could have been false were proved with exact positivity hypotheses: `alphaTH_mem_Icc` (`α′ ∈ [0, 1]` under `0 ≤ α ≤ β ≤ 1`, `1 ≤ ρ`, `0 < ε < 1`, `ρε ≤ 1`) and `epsStar_le_epsStar_alphaTH` (the trigger-happy hypothesis raises `ε†`). The source's decimals are the rationals `p_reck = 9/50`, `α′ = 31/190`, `ε†(α) = 1/11`, `ε†(α′) = 31/221` (`numbers_rho4`). The source's "recovery in `≈ log(odds gain)/D_KL` steps", "`1766` steps", "`19 %`" are simulations and are recorded only.

## F-11 — S8(b′): the a.s. limit `μ_t → 1` under labelled feedback is the strong law; only the per-step statement is formalized (gap, recorded)

**Pointer.** `caution-final.md` S8(b′) (l. 78), proof §8 (l. 149: "`0.1398` nats each").

**Record.** Formalized: the labelled-step log-LR, its expectation under `Bern(ρε)` equals the two-point KL (`expect_logLR_eq_klBern`), and `0 < klBern (ρε) ε` for `ρ > 1` (`klBern_pos`, Gibbs strict), instantiated at `ρ = 4`, `ε = 1/20` (`klBern_rho4_pos`). Not formalized: the trajectory limit (needs the SLLN over Mathlib's `ProbabilityTheory`; not attempted) and the decimal `0.1398` (a bracket `(0.13, 0.15)` needs tighter `log` bounds than `log x ≤ x − 1` gives; not done). The source's "restored under labelled feedback" is, in Lean, "positive expected evidence per labelled step".

## F-12 — S8's heed condition: the regime `ε < ε† < ρε` is not needed for `heed ↔ μ† ≤ μ` (presentation)

**Pointer.** `caution-final.md` proof §8 (l. 141: "in the regime `ε < ε† < ρε`").

**Record.** `ModelM.heed_iff_muDagger_le` needs only `ρ > 1`, `ε > 0` (and the parent's junk guard `0 < αc + βh`); the regime only places `μ†` in `(0, 1)`. Fidelity `stronger`.

## F-13 — S9: the rate cap is a telescoping sum; Kosoy's two corrections recorded (presentation; as the plan anticipated)

**Pointer.** `caution-final.md` S9(a) (l. 84), proof §9 (l. 155); adversary A9.1, A9.3 (l. 83, 87); mandate "Known issues" 7.

**Record.** `AUModel.rate_cap` is `AU(s₀) − AU(s_T) ≤ λT` by induction on `T`; Kind L. The load-bearing content is the finding it carries: linear in `T`, a rate cap, not a guard; `λ = 0` (Kosoy's traps) makes `AU` nondecreasing (`rate_cap_zero`, `au_mono_of_traps`). Adversary A9.4's "`hnull` is free" is `AUfin_null_le` in the finite-horizon Bellman form (horizons shift by one; the source's stationary `AU` is not available finitely). A9.2's "D9 never penalizes power gain" is `reversible_of_gain` / `gainModel_reversible`. Kosoy 2019 (not a target, no RL layer in FAF): (i) the number of delegations is `O(ln N/(η_K ε))` with `η_K ∼ (1 − γ)^{1/4}`, growing with the horizon, not uniformly bounded; (ii) her regret is against a *known* reward shared by all hypotheses, so nothing in her theorem concerns value uncertainty. Both as the adversary states them (`[reported]`, not re-derived here).

## F-14 — S12's salvage (T8(b), 2-089): with a deterministic value-sane advisor equal to the argmax, the single-state toy has no non-identifiable case (finding on the mandate's stretch item; conjecture recorded)

**Pointer.** `caution-final.md` S12 (l. 103, "restated conjecture"); adversary A12.2 (l. 101); mandate T8(b) ("if the fiber contains an `ω` whose optimal action differs from `ω*`'s, the trigger fires forever").

**Record.** If `adv ω` is *the* `ω`-optimal action (value-sane, deterministic, each hypothesis with a *unique* optimum) then the fiber `{ω | adv ω = adv ω*}` consists of hypotheses that share the optimal action, so after one delegation the exploration trigger (disagreement about the optimal action among positive-posterior hypotheses) can never fire again and the regret is `0` thereafter — the "fires forever" branch is empty. With ties (audit r1 N9) two hypotheses can share `adv` yet differ in their argmax *sets*, and a trigger defined by argmax-set disagreement then fires forever with zero action regret but linear delegation cost; the uniqueness clause is load-bearing. The linear-regret-from-delegation case the mandate describes needs an advisor whose action is *not* the value-argmax (Milli et al.'s irrational human, Carey's conflated actions), i.e. the identifiability obstacle is in the advisor model, not in the value model. No Lean for (b); the refutation (a) is exact (`s12_refuted`, `s12_not_sublinear`, Delegation.lean). 2-089's DRL-shaped regret theorem stays a conjecture conditional on identifiability of `ω*` from advisor actions.

## F-15 — 2-080 ("option value grows with the environment and with capability"): true in the refinement reading, false in the menu reading (imprecision)

**Pointer.** `critique/turner.md` C4 (l. 81), Objection 1 (l. 159); inventory flag "suspicious: Cor. 6.14 is by analogy".

**Record.** (c1) *Refinement-monotone*: a finer second channel has weakly more option value — `optionValue_coarsen_le` (OptionValue.lean), proved. (c2) *Menu-monotone* ("adding actions to `Shᶜ` raises option value") is **false**: it is the same phenomenon as `corr-power-channel`'s "EVPI not monotone in the option set" (corr-wf14-104, 2-059); not duplicated here. Turner's Corollary 6.14 (average-optimal policies avoid the terminal state) is an MDP statement with no counterpart in Setting S; the Lean here shows only that the middle term of C4's decomposition is nonnegative (`optionValue_nonneg`, Good's theorem, also re-derived from `corr-three-step-facts`' `priorBest_le_partValue` via `optionValue_eq_partValue_sub`) — its *size* is not addressed anywhere in this package.

## F-16 — Duplicates and non-targets (recorded)

- **S7** (corr-wf14-102, the outside-view detector): `duplicate-of: 095` — the detector's identity is S1's `E_P[U − V_ω] = 0` applied (`CautionState.expect_proxy_sub_V`); the Milli–Carey attribution is the adversary's A7.2 and is not a formal target. No separate declaration.
- **S13** (corr-wf14-103, the FUD page's clauses): `duplicate-of: corr-wf14-013`, whose tower-property lemma is `corr-three-step-facts`'s. The conditional clauses are the below-threshold inequality on a press (`corr-three-step`'s `belowThresholdIneq`); the unconditional clause is what the tower property forbids; D8 has no channel in it. Not re-proved here.
- **corr-wf14-009** (run 1 `miri` Prop. 15.1, compliance-record non-identification): `corr-three-step-facts`'s sibling result; cited in `ModelM.lean`'s docstring, not duplicated.
- **2-042** (Monte Carlo), **2-082**, **2-084** (scripts): `recorded, not a target`. E5 (the two-game example) is T4(c); E1–E4 are `corr-power-channel`'s.
- **A5.3** ("carried over on old actions"): not a predicate on the state at `t`; the source deleted it; nothing to formalize.
- **Kosoy's regret theorem** (S9(c), S12 shape): not a target (no RL layer in FAF); corrections in F-13.
- **The entropy/Pinsker bound** (corr-wf14b-038): `info-voi-latents`'s.

## F-18 — S5(b)'s "every term but `2δ` is computable by the agent" is false for `k_t` as defined (imprecision; found by audit r1, adversarial B2)

**Pointer.** `caution-final.md` S5(b) (l. 69: "`k_t := E_{π_t}[(U_t(∅) − U_t(a))⁺ 1_{C_t}]` is the cost the agent knowingly accepts. Every term but `2δ` is computable by the agent; the *hypothesis* is not"); S1 (l. 61).

**What is wrong.** `k_t` sums over `C_t(δ)`, and coverage is a relation between `P_t` and the target (`|U_t(a) − V_{ω*}(a)| ≤ δ`, D3) — S1's own point is that no functional of `P_t` sees it. So the restriction `1_{C_t}` is no more computable than the hypothesis; the sentence contradicts S1 for the `k_t` it defines. The round-0 docstring of `CautionState.realizedHarm_le_known_cost` repeated the sentence and has been corrected.

**Nearest true statement (proved).** Drop the indicator: since `(U(∅) − U(a))⁺ ≥ 0`, `H ≤ E_{Q}[(U(∅) − U(a))⁺] + 2δ + max{η, R̂}` — `CautionState.realizedHarm_le_known_cost_computable` (CautionRule.lean), every term but `2δ` a function of `P`, `γ`, `η`. The price is the uncovered actions' proxy harm, which the `1_{C_t}` form omits; the source should either state the computable form or stop calling `k_t` computable.

## F-19 — The develop's S12 does not specify its acting policy well enough for D8 to apply; the source's refutation (and `s12_refuted`) refutes the adversary's substitution (imprecision; found by audit r1, fidelity B2)

**Pointer.** `caution.md` S12 (l. 108: "the agent acts by the delegation variant of D8 (delegate iff the intended action is not `λ`-reversible and `P_t(c_ω(a) > λ) ≥ η′`)"); `caution.md` D8 (l. 49: `π_t := Q_{q_t}[U_t, γ_t]`, the delegation variant "when a candidate action has `ĉ_t(a) > η` and is not reversible … takes the delegation action"); `caution-adversary.md` A12.1 (l. 101: "posterior sampling plays `b` with probability `p`"); `caution-final.md` S12 (l. 103) and proof §12 (l. 159: "posterior-sampling plays `b` w.p. `p`").

**What is imprecise.** D8 acts by the proxy-ranked quantilizer over a base `γ_t` with a null action `∅`; S12 supplies neither a base nor a null action (its data are `Ω`, the dynamics, the trigger and the advisor), so "the delegation variant of D8" has no non-delegating policy to run. The adversary instantiated the policy as *posterior sampling* (A12.1), the final's proof §12 accepted it, and the develop's own trigger clause (`P_t(c_ω(a) > λ) ≥ η′`) differs from D8's (`ĉ_t(a) > η`). The refutation is therefore of a substituted policy. Under D8's own policy the answer depends on data S12 does not fix: with a small base the quantilizer plays the proxy-top action, which is `a` (regret `0`) or `b` (regret `g` per step) according to the prior, so the conjecture is false either way — but that argument was not in the source.

**Repair (proved).** `Delegation.s12_refuted` now states its reading as the adversary's instantiation (Hyps `(c)`), and `Delegation.s12_refuted_d8` refutes S12 under D8's own quantilizer on a state that supplies what S12 omits (`A = {∅, a, b}`, uniform base, `P(ω′) = 3/4`, `η = 1/4`, values in `[0, 1]`, `R = R̂ = 1/12`): `q = 1/3`, policy `δ_b`, realized harm `1/4 = η` (within budget, tight), regret `1` per step and `T` over `T` steps, trigger never firing. So the develop's S12 is false with its own acting rule as well; what the source needs is to say which non-delegating policy the conjecture is about.

## F-17 — Attribution register (recorded)

D5 ("reckless") and D10 are CLAUDE's formalizations of the author's v2 §1.3 sentence (`caution-final.md` §0, l. 19: "the definition D5 below is CLAUDE's"). No docstring in this package says what the author meant; every "the source's reading" is that file's, and any bridge from these definitions to his sentence is ATTRIBUTION-UNVETTED.
