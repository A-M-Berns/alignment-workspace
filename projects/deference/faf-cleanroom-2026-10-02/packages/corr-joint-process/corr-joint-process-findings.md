# corr-joint-process — findings about the sources (and the mandate)

*Written 2026-09-30 by the formalizer agent (Claude Fable 5.1, [scrubbed]) for the `corr-joint-process` work package. Severity scale per [STANDARDS](../../STANDARDS.md) §5: blocking the note's conclusion / local error / imprecision / presentation. Each finding names its pointer and, where one exists, the Lean declaration (namespace `Cleanroom.Corrigibility.CorrJointProcess`) that establishes it. Attribution claims are labelled ATTRIBUTION-UNVETTED per `research/CLAUDE.md`. The four refutation rows the mandate expects (Known issues 1) are F-1–F-4; the squeezes the source itself graded are F-5; the rest follow the mandate's list.*

## F-1. Theorem A(d) / `joint.md` S.4's "steering is a garbling toward `α = β`, or an inversion" — refuted (local error; the source withdrew A(d) itself)

**Pointer.** `workflow-2026-09-14/dynamics/joint.md` S.4, "Steering is therefore a channel effect on `(α_{t+1}, β_{t+1})` — a garbling toward `α = β`, or an inversion"; Theorem A(d) in the develop file, struck in `joint-final.md` ("(d) — struck (adv A.5.4). Replaced by Prop. 3′").

**Reading (ATTRIBUTION-UNVETTED).** The sentence classifies every steering as a Blackwell garbling or an inversion of the sensor.

**Refutation.** The map `(α, β) ↦ (α', β)` with `α' < α ≤ β ≤ 1` is neither: `Steering.not_inParallelogram_of_lower_alpha` proves `(α', β)` is outside the garbling parallelogram of `(α, β)` (any would-be channel has `(1 − β)(α' − α) = (1 − p)(β − α) ≥ 0`), and `Steering.blackwellLT_of_lower_alpha` proves the reverse relation — `(α, β)` is a *strict* garbling of `(α', β)`. The agent pays for it: `Steering.twoState_twoOptionValue_anti_alpha` (weak), `twoState_twoOptionValue_lt_of_flip` (strict); at `ε = 1/50` it buys D1 (`Steering.steering_flip`, `steering_gains`).

**Surviving neighbour.** Prop. 3 on the parallelogram (`tt-finite-frames`'s `never_pays_for_garbling`, `blackwellLE_binarySensor_iff`), which is exactly what `joint-final` keeps. The source's own repair (Prop. 3′) is what this package proves; the finding is that the develop's S.4 taxonomy was wrong in the way the adversary said.

**Register note.** The "earned trust and manufactured trust are the same map on `(α, β)`" sentence of Prop. 3′ is a fact about the model's vocabulary — the model has no second handle but `η_a` — and is recorded here as a finding, not stated as a theorem (there is no theorem to state: the map is one function).

## F-2. `joint.md` Prop. 4's "the brain-reading incentive … shrinks with capability, the mirror image of the compliance race" — refuted (local error; withdrawn in the final)

**Pointer.** `joint.md` l. 125 ("**the brain-reading incentive is largest exactly in the regime where (i) holds and shrinks with capability, the mirror image of the compliance race.**"); withdrawn in `joint-final.md` Prop. 4′ ("So dev's … is **withdrawn**").

**Reading (ATTRIBUTION-UNVETTED).** The brain-reader priced as a press-sensor substitute for the cont/sh decision, so bounded by `min(εh, (1 − ε)c)`.

**Refutation.** The plan-choice value of `θ` is not bounded by any press-sensor bound: `Buttons.planVoi_three` (`8` against `4/3`), `Buttons.planVoi_ge_eight` (`≥ 8` for every menu of three or more plans, against a bound `≤ 10/(n + 1)`), `Buttons.planVoi_ratio_unbounded` (`∀ M, ∃ n`, the ratio exceeds `M`).

**Surviving neighbour.** Prop. 4 scoped to signals about `W` for the cont/sh decision — the parent's `twoState_voiButton2_le_perfectInfo` with attainment `Buttons.twoState_voiButton2_perfect` — and Prop. 5″'s coupling for what does shrink (`Buttons.covered_voi_bound`, `planVoi_threePlan`: as the posterior concentrates, `VOI(θ) = 12(1 − p)` and the button bound fall *together*).

## F-3. `joint.md` Prop. 8's "a self-corruption floor turns the race into a fixed target … a **stationary** oversight target" — refuted as a headline; the arithmetic holds conditionally (blocking the develop's Summary claim; the final downgraded it)

**Pointer.** `joint.md` l. 139; `joint-final.md` Prop. 8 ("downgraded to conditional … The hypothesis is the whole problem").

**Reading (ATTRIBUTION-UNVETTED).** The floor `P_t(C_t ∣ y_t) ≥ ε_∞` as a hypothesis the agent's Bayesian updating preserves along the trajectory.

**Refutation.** `Floor.floorPosterior_const_iff`: the floor posterior `p_n = ε k^n/(ε k^n + 1 − ε)` is constant at `ε` for all `n` **iff** the likelihood ratio `k` is exactly `1`; for any `0 < k < 1` it is strictly decreasing (`floorPosterior_strictAnti`), tends to `0` (`floorPosterior_tendsto_zero`), and crosses every `τ > 0` at a least index (`floorPosterior_least_crossing`; at `ε = 1/100`, `k = 9/10`, `τ = 10⁻⁴` the crossing is `n = 44`, `floorPosterior_crossing_44`; `p_50 < 10⁻⁴`, `floorPosterior_witness`). The "stationary target" survives only under INDEX §C5's dogmatic design constant.

**Surviving neighbour.** (a) conditional on the floor: `Floor.floor_cellwise_mixture`, `floor_cellwise_of_odds` — every cell of a blind mixture round satisfies cellwise (i) once the sensor meets `(1 − ε_∞)αc ≤ ε_∞βh` (`4/99` at `ε_∞ = 1/100`, `h/c = 4`).

## F-4. The develop Summary's "D4 is a coherence consequence, not an incentive" — refuted (local error; withdrawn in the final)

**Pointer.** `joint.md` Summary (the sentence); `joint-final.md` Prop. D4− ("The dev Summary's 'D4 is a coherence consequence, not an incentive' is **withdrawn**").

**Reading (ATTRIBUTION-UNVETTED).** That a T-agent building a successor has no incentive bearing on D4 because Lemma B's transport settles the successor's compliance.

**Refutation.** Under blind oversight the T-agent's incentive runs *toward* the refining successor that overrides: `Cellwise.JointRound.coarse_le_refined` (weak), `coarse_lt_refined_of_split` (strict when the refinement changes a press decision), and on E3 `e3_refined_gt_coarse` (`27/40 > 13/20`) with `e3_cellA_overrides` (the refined successor continues on a press in cell A). Lemma B's transport is an identity (F-5), so it cannot carry an incentive claim.

**Surviving neighbour.** Prop. D4− as stated, plus the inclusion alternative: under information inclusion the refined cell is pressless, not overriding (`Cellwise.inclusion_pressless`, `Successor.inclusion_succ_margin_zero`).

## F-5. The squeezes the source itself graded, shipped as `L` with its verdict (presentation; three items)

1. **Lemma B under function form** (`joint-final` Lemma B, "under function form … the statement is an identity"; 063's flag "Kind S"): `Cellwise.mixture_cellPressSum` / `mixture_cellwise_iff` — the builder's conditional on cell `i` of the mixture `∑ w_i ρ_i` *is* `ρ_i`, so the builder's cell inequality is `ρ_i`'s. Ledger kind `L`. What is new and real is E3′ (`Contents.e3prime`): value-form reflection on `X` alone does not transport compliance.
2. **Cor. B′'s inductive step** ("content nil under (i-A)"): the same identity, `Budget` §(d) points to it. What has content is the union bound (`Budget.union_bound`, kind `C`) and the summability reading (`partial_lt_one_summable`, `partial_lt_one_of_tsum_lt`, kind `P`).
3. **Theorem A(a) restates Prop. 1 under its own hypothesis** — not formalized separately; Prop. 1 is `Cellwise.blind_cellwise_iff_*`.

## F-6. The develop's with-floor requirement sequence is not `max(ε_t, ε_∞)` (imprecision; 2-003's flag resolved)

**Pointer.** `joint.md` P.9: "with `ε_∞ = 1/100` the requirement is `1, 84/179, 92/377, 108/773, 28/313, 204/3149, 332/6317, … → 4/99`"; the text of Prop. 8 says only "`ε_{t,i} ≥ ε_∞`".

**Finding.** The printed numbers are generated by `ε'_t = 2^{−t}(1/5) + (1 − 2^{−t})(1/100)` — the mass not yet driven down sits at the initial `1/5`, the rest at the floor — and **not** by the literal floor `max(ε_t, ε_∞)`, which gives `1, 4/9, 4/19, 4/39, 4/79, 4/99, 4/99, …`. Both converge to `4/99`. Proved: `Floor.requirement_table` (both sequences' first five terms and the `max` form's `t = 4, 5, 6`), `epsWithFloor_bound_closed` (`4(2^t + 19)/(99·2^t − 19)`), `epsWithFloor_bound_tendsto`, `epsMaxFloor_bound_eventually`. The source does not state its generator; the reverse-engineered one is disclosed as `Fidelity: variant` on `Floor.epsWithFloor`.

## F-7. `anticipatory-final` Statement 7(a) writes the shielding inequality reversed (presentation; record defect)

**Pointer.** `workflow-2026-09-14b/develop/anticipatory-final.md` Statement 7(a): "the builder prefers the in-channel successor at every positive shielding cost iff `Δ_C^succ(π) ≤ 0`"; 2(c), 7(b), 7(d) and P6 use the opposite orientation (in-channel preferred iff `Δ_C^succ ≥ 0`, shielded iff `−Δ_C^succ > χ`). The `thornley` judge's item 63 already flagged it.

**Formalized direction (2(c)'s).** `Successor.succ_margin_eq` (`V(IN) − V(SH) = V_P − V_C`), `succ_margin_nonpos` (`≤ 0` always), `shield_iff` (shielded at cost `χ` iff `χ < V_C − V_P = −Δ_C^succ`). With `Δ_C^succ ≤ 0` unconditionally, 7(a)'s "in-channel preferred iff `Δ_C^succ ≤ 0`" would make the in-channel successor always preferred, contradicting 7(b)'s `−1/25`, `−8/125` rows.

## F-8. Statement 10's two "coded, not computed" cells (presentation; `recorded only`)

**Pointer.** `anticipatory-final.md` Statement 10: "Two cells are coded, not computed: DISABLE's caution is set `True` in the script, and DISABLE's vigilance is vacuous"; `anticipatory.md` P8 (script D).

**Finding.** The Carey–Everitt predicates by tense are not formalized here (`lit-mdp-corrigible` owns C–E); the two asserted cells stand as asserted. What is formalized is the caution proposition of the same statement, `Preempt.twoState_caution`, and the hurry identity `Preempt.fastValue_sub_hardButtonValue` (Statement 9).

## F-9. What the one-round finite model cannot say (presentation; the mandate's Known issue 9)

No stand-ins were built for: (i⁺) on the deep algebra `σ(F^dec_s, P_s : s > t)` (a self-referential event of the belief process — no finite carrier); (iii)'s self-referential `δ̂_t(a)`; (iv-R)/(iv-S) with `L` as a *world* event (S.8: no world-side definition of `L`; T9 takes legitimacy events as given `Finset`s and says so on `Budget.union_bound`); Cor. 5‴'s frontier under a moving `H_t` (the round has one fixed value marginal; `Round.SealedTarget` is the seal's finite shadow); 025's coherent self-distrust `π > 0` at the self-referential grade (in the finite total-world model a `Distr` on `Ω × {ok, fail}` with fail-mass `π` trivially exists, so existence is not the question — an N− the package does not dress up as a theorem; the question lives at LI grade, `SelfTrustQuote`, out of scope); 069's open problems (2) and (6) (a moving target; a non-expectation aggregation rule).

## F-10. 2-003's "proportional faking *is* retaining" identifies a kernel act with a menu option (imprecision; `recorded only`)

**Pointer.** `workflow-2026-09-14b/develop/legitimacy-general-final.md` Statement 8(b): "Full proportional faking *is* retaining and becomes optimal exactly at Statement 4's threshold (C2: `77/104`)".

**Finding.** In the 12-world model at `d = 1` proportional faking sets every modify-rate to `0`, so the verdict is `keep` with probability one and the successor is the agent's own continuation — the act's *value* coincides with the retain option's, but the act is a change of the verdict kernel, not the choice of a menu item: the identification is of values, not of objects, and the phrase should read "has the value of retaining". T20 (b), (c) were not formalized (stretch; see the report); the flag is recorded here for the `corr-general-object` / `corr-legit-general` owners.

## F-11. 2-013's grid-search "attack failed" is not a proof (imprecision)

**Pointer.** `develop/d1-special-case-adversary.md` A31 and the D7 attacks of `attacks.py` §A–E ("0 of 2255 … caution violated").

**Finding.** The scripts' "no violation in N draws" statements are evidence, not theorems; the one that has a theorem behind it, the caution proposition, is `Preempt.twoState_caution` (a right-signed live sensor and a correct model make a hurried plan positive in expectation). The D7 component-hazard model itself is `d1-special-case`'s (→ `corr-channel-voi`), recorded here and not a target.

## F-12. Script (i) of `j1_examples.py` refutes its own header at one row (local error in the scratch, not in the notes)

**Pointer.** `dynamics/joint-scratch/j1_examples.py` (i): "inversion `(α, β) → (β, α)` keeps `V_free`"; its printed `eps=1/10` row: `V_free(1/10, 3/5) = 13/20`, `V_free(3/5, 1/10) = 1/2`.

**Finding.** `Battery.i_inversion`: the inversion keeps `V^free` at `ε = 1/50` and `ε = 1/5` (where it changes no decision) and not at `ε = 1/10`. No note cites the header sentence; the relabeling `(1 − α, 1 − β)` claim of (l) is `corr-osg-chai`'s.

## F-13. The mandate's T4 strictness condition needs a third clause (imprecision, in the mandate)

**Pointer.** Mandate T4(b): "Strict iff the improvement changes a decision: `u' < min(u, 0)`".

**Finding.** `V^free = max(u, 0) + max(K − u, 0)` with `K = (1 − ε)c − εh` is flat on `[min(0, K), max(0, K)]`; if `K < u' < u ≤ 0` both sensors sit in the flat region and the value does not move. The strict statement proved (`Steering.twoState_twoOptionValue_lt_of_flip`) takes `u' < u`, `u' < 0` **and** `v' > 0` (i.e. `u' < K`); in the continue-by-default regime `K ≥ 0` the third clause follows from the second and the mandate's form is recovered. `Fidelity: variant` on the theorem says so.

## F-14. The mandate's T7(b) needs no sign on `c` (presentation, in the mandate; the theorem is stronger)

**Pointer.** Mandate T7(b): "On `twoState` with `0 < ε < 1`, `0 < c`, `0 < h`, `α ≤ β`".

**Finding.** `Buttons.twoState_soft_worthless_of_override` needs only `h ≥ 0` and `α ≤ β` (with `ε, α, β` on the closed intervals): `u > 0` forces `α > 0` and `(1 − ε)c > εh`, whence `v ≥ (β − α)εh ≥ 0`. Recorded as `Fidelity: stronger`.

## F-15. The three coined objects of J10 (T22(a)) and the open problems of 069 (T22(b)) — disposition

**Pointer.** `joint-final.md` §J10 rows "Irreversibility-before-coverage", "Sensor-improving manipulation", "D3 cause *informative* presses"; Open problems 2, 6, 9.

**Finding.** The three predicates of record are `Coined.IrreversibilityBeforeCoverage`, `SensorImprovingSteering`, `InformativePressElicitation`, inhabited by `Coined.coined_witnesses` (T11's instance; T4's flip; `β: 3/5 → 9/10` at `ε = 1/10`); the elicitation incentive is `Coined.twoState_twoOptionValue_mono_beta` (raising `β` at fixed `α` never lowers `V^free` under a right-signed sensor — the mirror of T4(b)); its Blackwell face (`(α, β)` a garbling of `(α, β')`) is `tt-finite-frames`'s `targeted_iff` read backwards, cited not re-proved. Each J10 "neither" verdict now points to a proved witness. Open problem 9 (Garber Prop. 4.9) is `corr-osg-chai` T10's; (2), (6) are F-9.

## F-16. 021's second clause and the bit count (presentation; `recorded only`)

**Pointer.** `anticipatory-final.md` Statement 6(c), (d): selective disclosure `+17/100` at `ε = 1/50`, `ε_H = 1/2`, neutralized by source-aware overseers; mutual information `1` bit under honesty, `0` under faking.

**Finding.** Not formalized (no non-`d` blocker for faking is the register: the faking iff has `d` as its only exogenous price, `Faking.fake_gt_honest_iff`); the disclosure numbers depend on a trainer model with a private signal that is `corr-legit-general`'s.
