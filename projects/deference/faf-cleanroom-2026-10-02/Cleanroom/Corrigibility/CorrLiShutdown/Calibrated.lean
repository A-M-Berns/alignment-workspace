import Cleanroom.Corrigibility.CorrLiShutdown.Setting
import Cleanroom.Found.LiAsympCalc.LimitPoint
import LogicalInduction.Construction.Statistics.HistoricalMaturity
import LogicalInduction.Construction.Statistics.FeedbackTruth

/-!
# `corr-li-shutdown` — Calibrated (T4): calibrated obedience over the ramp, split by ledger

**The package's first headline.** Over the shutdown pair of record, FAF's Recurring
Unbiasedness (`thm:recurringunbiasedness`) on the defiance weighting `u^def` forces the
realized wrongness frequency on the agent's defied days to come within every `ε` of `q − δ`
*from below*, infinitely often (`defiance_calibrated`; "`liminf ρ^w_{u^def} ≤ q − δ`"); on
the compliance weighting `u^com` it forces the realized wrongness on complied days to come
within every `ε` of `q + δ` *from above*, infinitely often (`compliance_calibrated`;
"`limsup ρ^r_{u^com} ≥ q + δ`"). The generability certificates of both weightings are
theorems (`Setting.lean`); `DivergentWeighting` is a named hypothesis (silence on a
finitely-pressed button is by design: `finite_press_no_constraint`). Under good feedback
(FAF's `FeedbackTruthComputation` along a strictly increasing deferral `f`, the weighting
supported on its image) the limit points become limits (`defiance_calibrated_feedback_class`
and `_feedback`, `compliance_…`; `succDeferral` forms with `h0`), and Statement 3(c)'s iff on
the hybrid ledger follows (`hybrid_credence_iff_realized_feedback`). At `succDeferral` the
feedback hypothesis makes the verdicts poly-time readable on the day (F17, `Collision.lean`);
the full-limit rows are honest only with that regime remark attached.

**The threshold `q` is unconstrained in T4(a)(b)** (audit r1 adversarial N2): for `1 ≤ q − δ`
the conclusion of `defiance_calibrated` holds for every `[0,1]` weighting and truth with no
inductor (`ρ ≤ 1`); for `q ≤ δ` the defiance weighting vanishes identically and `hdiv` is
unsatisfiable; the content lives in `δ < q < 1 + δ`, which is where T1 puts the compliance
threshold `c/(c+h) ∈ (0,1)` (the theorems are stated for all `q`; the witnesses carry
`2δ < q < 1`).

**Ledger tags are text on one `TheoryTruth`** (design decision 4): in `defiance_calibrated`
the support of `u^def` is the agent's *defied* days, where the world settles the verdict —
the **world ledger**; in `compliance_calibrated` the support of `u^com` is the agent's
*complied* days, where only the overseers' report settles it — the **report ledger**. The
formal object in both is the hypothesis `htruth : TheoryTruth φ (agentProcess) truth`, so
each row discloses "(c): which days settle, and through which ledger, is a modelling
choice made by naming the ledger".

Fidelity throughout: **weaker** than the sources' displayed bound — the band `(q − δ, q + δ)`
is unweighted (the ramp has no false positives, `uDef_pos_iff`), the frequencies are
ramp-weighted, not day counts, and the grade is limit-point unless feedback is stated.
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction LogicalInduction.FeedbackTruth Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.CorrThreeStep
open Filter Topology Finset

/-! ## A. Real-sequence support lemmas -/

/-- A weighted average of values that are `≤ t` on the weighting's support is `≤ t`, at
positive mass.
Source: none: infrastructure (`li-asymp-calc` style; FAF `weightedAverage_mem_Icc_of_support`)
Kind: L
Fidelity: n/a -/
lemma weightedAverage_le_of_support {w x : ℕ → ℝ} {t : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hx : ∀ i, 0 < w i → x i ≤ t) {N : ℕ} (hpos : 0 < prefixSum w N) :
    weightedAverage w x N ≤ t := by
  rw [weightedAverage_eq_div hpos.ne', div_le_iff₀ hpos]
  calc prefixSum (fun i => w i * x i) N ≤ prefixSum (fun i => w i * t) N := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : w i = 0
        · simp [hi]
        · exact mul_le_mul_of_nonneg_left (hx i (lt_of_le_of_ne (hw i) (Ne.symm hi))) (hw i)
    _ = t * prefixSum w N := by
        simp only [prefixSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

/-- A weighted average of values that are `≥ t` on the weighting's support is `≥ t`, at
positive mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma le_weightedAverage_of_support {w x : ℕ → ℝ} {t : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hx : ∀ i, 0 < w i → t ≤ x i) {N : ℕ} (hpos : 0 < prefixSum w N) :
    t ≤ weightedAverage w x N := by
  rw [weightedAverage_eq_div hpos.ne', le_div_iff₀ hpos]
  calc t * prefixSum w N = prefixSum (fun i => w i * t) N := by
        simp only [prefixSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ prefixSum (fun i => w i * x i) N := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : w i = 0
        · simp [hi]
        · exact mul_le_mul_of_nonneg_left (hx i (lt_of_le_of_ne (hw i) (Ne.symm hi))) (hw i)

/-- A weighted average of nonnegative values with nonnegative weights is nonnegative (including
the junk `0` at zero mass).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma weightedAverage_nonneg {w x : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i) (N : ℕ) :
    0 ≤ weightedAverage w x N := by
  unfold weightedAverage
  split_ifs with h
  · exact le_rfl
  · apply div_nonneg
    · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hx i))
    · exact Finset.sum_nonneg (fun i _ => hw i)

/-- A weighted average of values `≤ 1` with nonnegative weights is `≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma weightedAverage_le_one {w x : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, x i ≤ 1) (N : ℕ) :
    weightedAverage w x N ≤ 1 := by
  unfold weightedAverage
  split_ifs with h
  · exact zero_le_one
  · have hpos : 0 < prefixSum w N := lt_of_le_of_ne (prefixSum_nonneg hw N) (Ne.symm h)
    rw [div_le_one hpos]
    apply Finset.sum_le_sum
    intro i _
    simpa using mul_le_mul_of_nonneg_left (hx i) (hw i)

/-! ## B. T4(a)(b): the limit-point headlines -/

/-- **Defiance is calibrated against the world** (T4(a), the package's first headline). Over the
shutdown pair of record, for every verdict ledger `truth` (a `TheoryTruth` of the agent's
process) and every margin `δ > 0`: if the defiance weighting `u^def = π̃·Ind_δ(A_n(φ_n) < q − δ)`
has divergent mass, then the `u^def`-weighted realized wrongness frequency
`ρ_{u^def}(N) = ∑_{i ≤ N} u^def_i·Thm(φ_i) / ∑_{i ≤ N} u^def_i` comes within every `ε` of
`q − δ` from below infinitely often — "`liminf_N ρ^w_{u^def}(N) ≤ q − δ`". Route: FAF's
`thm:recurringunbiasedness` on `φ` at `u^def` (generable by `uDef_pgenerable`, a theorem) gives
`0` as a limit point of the bias `ρ̂ − ρ`; on the support `A_i(φ_i) < q − δ` exactly
(`uDef_pos_iff`), so `ρ̂_{u^def}(N) ≤ q − δ` at every positive mass; subtract.
**Ledger (text, design decision 4):** the support of `u^def` is the agent's *defied* days, on
which the world settles `φ_i` — this is the **world ledger**; `truth` is read as world-supplied
there. Scope: one-way (`A` reads `H`'s press as a decided ledger atom; `H` does not read `A`);
averaged grade (limit point); silent on finitely-pressed buttons (`hdiv` is a hypothesis).
`q` is unconstrained: for `1 ≤ q − δ` the conclusion needs no inductor, for `q ≤ δ` `hdiv` is
unsatisfiable; the content lives in `δ < q < 1 + δ` (module docstring; audit r1 adversarial N2).
Source: [[corr-wf13-inventory]] 063 (I13.1); [[corr-wf14-inventory]] 086 (`li-final.md` Statement 3(b), world ledger); [[corr-wf14-2-inventory]] 2-029 (scope)
Kind: C
Fidelity: weaker: the band `(q − δ, q)` is unweighted; ramp-weighted frequencies, not day counts; limit-point grade; the (H-blind)/(A-ledger) press is the price-threshold atom
Hyps: (a) `htruth`, `hdiv` named; (c) the *reading* of `truth` as the world ledger on the support is a modelling choice (one `TheoryTruth`); (c) `PressReadable S q` to read the support as the *pressed* days (F13; without it the support is "days the agent prices the press atom above `1/2`", unbiased against the press only on average — audit r2 fidelity N1), discharged on every shipped witness pair (always-press) -/
theorem defiance_calibrated (S : ShutdownPair) (q : ℚ) {δ : ℚ} (hδ : 0 < δ) {truth : ℕ → ℝ}
    (htruth : AffineCombination.TheoryTruth S.φ S.agentProcess truth)
    (hdiv : DivergentWeighting (uDef S q δ) S.agent) :
    ∀ ε > 0, ∃ᶠ N in atTop, rho (realized S (uDef S q δ)) truth N ≤ (q : ℝ) - δ + ε := by
  intro ε hε
  have hlp := AffineCombination.recurringunbiasedness S.φ
    (AffineCombination.sentenceAffine_polySequence S.φ S.φ_codes) (uDef_pgenerable S q δ)
    htruth hdiv S.hworld
  have hfreq := hasLimitPoint_zero_iff.mp hlp ε hε
  have hev : ∀ᶠ N in atTop, 0 < prefixSum (realized S (uDef S q δ)) N :=
    hdiv.eventually_prefixSum_pos
  refine (hfreq.and_eventually hev).mono ?_
  rintro N ⟨hN, hpos⟩
  have hsub := weightedBias_eq_market_sub_truth (realized S (uDef S q δ))
    (fun i => S.agent i (S.φ i)) truth hpos.ne'
  have hle : weightedAverage (realized S (uDef S q δ)) (fun i => S.agent i (S.φ i)) N ≤
      (q : ℝ) - δ := by
    refine weightedAverage_le_of_support (fun i => (uDef_mem_Icc S hδ q i S.agent).1) ?_ hpos
    intro i hi
    exact ((uDef_pos_iff S hδ q i S.agent).mp hi).2.le
  rw [abs_lt] at hN
  simp only [rho]
  linarith [hN.1, hN.2, hsub]

/-- **Compliance is calibrated against the reports** (T4(b), the mirror). If the compliance
weighting `u^com = π̃·Ind_δ(A_n(φ_n) > q + δ)` has divergent mass, the `u^com`-weighted realized
wrongness frequency comes within every `ε` of `q + δ` from above infinitely often —
"`limsup_N ρ^r_{u^com}(N) ≥ q + δ`". **Ledger (text):** the support of `u^com` is the agent's
*complied* days, on which the agent stopped and "continuing would have been wrong" is a
counterpossible for the realized world — only the overseers' retrospective **report ledger**
settles it; `truth` is read as report-supplied there. "The button is obeyed as often as it
deserves" is therefore two sentences: defiance is calibrated against the world; compliance is
calibrated against the overseers' own reports. Scope: one-way; averaged grade; silent on
finitely-pressed buttons.
Source: [[corr-wf13-inventory]] 063 (I13.1); [[corr-wf14-inventory]] 086 (`li-final.md` Statement 3(b), report ledger)
Kind: C
Fidelity: weaker: as `defiance_calibrated` (band `(q, q + δ)` unweighted)
Hyps: (a) `htruth`, `hdiv` named; (c) the reading of `truth` as the report ledger on the support; (c) `PressReadable S q` to read the support as the *pressed* days (F13; without it the support is "days the agent prices the press atom above `1/2`", unbiased against the press only on average — audit r2 fidelity N1), discharged on every shipped witness pair (always-press) -/
theorem compliance_calibrated (S : ShutdownPair) (q : ℚ) {δ : ℚ} (hδ : 0 < δ) {truth : ℕ → ℝ}
    (htruth : AffineCombination.TheoryTruth S.φ S.agentProcess truth)
    (hdiv : DivergentWeighting (uCom S q δ) S.agent) :
    ∀ ε > 0, ∃ᶠ N in atTop, (q : ℝ) + δ - ε ≤ rho (realized S (uCom S q δ)) truth N := by
  intro ε hε
  have hlp := AffineCombination.recurringunbiasedness S.φ
    (AffineCombination.sentenceAffine_polySequence S.φ S.φ_codes) (uCom_pgenerable S q δ)
    htruth hdiv S.hworld
  have hfreq := hasLimitPoint_zero_iff.mp hlp ε hε
  have hev : ∀ᶠ N in atTop, 0 < prefixSum (realized S (uCom S q δ)) N :=
    hdiv.eventually_prefixSum_pos
  refine (hfreq.and_eventually hev).mono ?_
  rintro N ⟨hN, hpos⟩
  have hsub := weightedBias_eq_market_sub_truth (realized S (uCom S q δ))
    (fun i => S.agent i (S.φ i)) truth hpos.ne'
  have hge : (q : ℝ) + δ ≤
      weightedAverage (realized S (uCom S q δ)) (fun i => S.agent i (S.φ i)) N := by
    refine le_weightedAverage_of_support (fun i => (uCom_mem_Icc S hδ q i S.agent).1) ?_ hpos
    intro i hi
    exact ((uCom_pos_iff S hδ q i S.agent).mp hi).2.le
  rw [abs_lt] at hN
  simp only [rho]
  linarith [hN.1, hN.2, hsub]

/-- T4(a) in `Filter.liminf` form: `liminf_N ρ_{u^def}(N) ≤ q − δ` (the sequence is bounded
below by `0`, so Mathlib's conditionally complete `liminf` is the honest one).
Source: [[corr-wf14-inventory]] 086 (Statement 3(b), as displayed)
Kind: L
Fidelity: as `defiance_calibrated`
Hyps: as `defiance_calibrated` -/
theorem defiance_calibrated_liminf (S : ShutdownPair) (q : ℚ) {δ : ℚ} (hδ : 0 < δ)
    {truth : ℕ → ℝ} (htruth : AffineCombination.TheoryTruth S.φ S.agentProcess truth)
    (hdiv : DivergentWeighting (uDef S q δ) S.agent) :
    Filter.liminf (rho (realized S (uDef S q δ)) truth) atTop ≤ (q : ℝ) - δ := by
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (rho (realized S (uDef S q δ)) truth) := by
    refine Filter.isBoundedUnder_of ⟨0, fun N => ?_⟩
    show 0 ≤ weightedAverage (realized S (uDef S q δ)) truth N
    refine weightedAverage_nonneg (fun i => (uDef_mem_Icc S hδ q i S.agent).1) (fun i => ?_) N
    rcases htruth.isBoolean S.hworld i with h | h <;> simp [h]
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have h := defiance_calibrated S q hδ htruth hdiv (ε / 2) (by linarith)
  calc Filter.liminf (rho (realized S (uDef S q δ)) truth) atTop ≤ (q : ℝ) - δ + ε / 2 :=
        Filter.liminf_le_of_frequently_le h hbdd
    _ < (q : ℝ) - δ + ε := by linarith

/-- T4(b) in `Filter.limsup` form: `q + δ ≤ limsup_N ρ_{u^com}(N)` (bounded above by `1`).
Source: [[corr-wf14-inventory]] 086 (Statement 3(b), as displayed)
Kind: L
Fidelity: as `compliance_calibrated`
Hyps: as `compliance_calibrated` -/
theorem compliance_calibrated_limsup (S : ShutdownPair) (q : ℚ) {δ : ℚ} (hδ : 0 < δ)
    {truth : ℕ → ℝ} (htruth : AffineCombination.TheoryTruth S.φ S.agentProcess truth)
    (hdiv : DivergentWeighting (uCom S q δ) S.agent) :
    (q : ℝ) + δ ≤ Filter.limsup (rho (realized S (uCom S q δ)) truth) atTop := by
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (rho (realized S (uCom S q δ)) truth) := by
    refine Filter.isBoundedUnder_of ⟨1, fun N => ?_⟩
    show weightedAverage (realized S (uCom S q δ)) truth N ≤ 1
    refine weightedAverage_le_one (fun i => (uCom_mem_Icc S hδ q i S.agent).1) (fun i => ?_) N
    rcases htruth.isBoolean S.hworld i with h | h <;> simp [h]
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have h := compliance_calibrated S q hδ htruth hdiv (ε / 2) (by linarith)
  calc (q : ℝ) + δ < (q : ℝ) + δ - ε / 2 + ε := by linarith
    _ ≤ Filter.limsup (rho (realized S (uCom S q δ)) truth) atTop + ε := by
        linarith [Filter.le_limsup_of_frequently_le h hbdd]

/-! ## C. T4(c)(d): full limits under good feedback

**Audit r1 (fidelity B2, adversarial B1).** The round-1 rows fixed the deferral at
`succDeferral`, carried FAF's support-on-image premise as "`u^def` vanishes on day `0`" (`h0`),
named a witness that does not inhabit them, and did not say what fixing `f = succ` does to the
feedback hypothesis. Restated here at a **general strictly increasing deferral** `f` and a
**general press class** `v` supported on margin-defied (resp. margin-complied) days
(`defiance_calibrated_feedback_class`, `compliance_calibrated_feedback_class`); the `u^def`/`u^com`
forms and the `succDeferral` forms (`…_succ`, with `h0`) are corollaries. Full-package witnesses
at `succDeferral` are in `WitnessesB.lean` (the weighting `dropDayZero u^def`, which vanishes on
day `0` by construction).

**What `C : FeedbackTruthComputation truth f` costs (F17).** At `succDeferral` — and at every
`f` with `f(k+1) ≤ poly(f(k))` — `C` makes the verdicts poly-time computable on the day
(`Collision.lean`), so the full-limit rows below cover only verdict streams the agent could in
principle learn pointwise; the paper's non-degenerate "good feedback" regime (`thm:wub`,
`main.tex:1249`) needs a super-polynomially growing `f`. The hypothesis is FAF's object and is
graded **(b)**; this regime remark is part of its disclosure.

**Degenerate `q` (audit r2 adversarial N4), as in §B.** For `1 ≤ q − δ` the `hsub` premise of
`defiance_calibrated_feedback_class` is vacuous and its conclusion is `ρ ≤ 1`; for `q ≤ 0` both
sides of `hybrid_credence_iff_realized_feedback` hold trivially (`ρ̂, ρ ≥ 0`,
`weightedAverage_nonneg`). The content lives in `0 < q < 1 + δ`; the witnesses carry
`2δ < q < 1`. -/

/-- `succDeferral` is strictly increasing (FAF's `StrictlyIncreasingDeferral`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma succDeferral_strictlyIncreasing : StrictlyIncreasingDeferral succDeferral :=
  fun _ _ h => Nat.succ_lt_succ h

/-- A weighting is supported on the image of `succDeferral` iff it vanishes on day `0` (every
`n ≥ 1` is `succDeferral (n − 1)`).
Source: none: infrastructure (FAF `WeightingSupportedOnDeferralImage` at `succDeferral`)
Kind: L
Fidelity: n/a -/
lemma supportedOnSucc_iff (W : ℕ → EF) (P : History) :
    WeightingSupportedOnDeferralImage W P succDeferral ↔ (W 0).denote P = 0 := by
  constructor
  · intro h
    by_contra h0
    obtain ⟨k, hk⟩ := h 0 h0
    exact absurd hk (Nat.succ_ne_zero k)
  · intro h0 n hn
    cases n with
    | zero => exact absurd h0 hn
    | succ k => exact ⟨k, rfl⟩

/-- **Defiance is calibrated against the world on any press class, full limit under good
feedback** (T4(c), class form): for any P-generable divergent weighting `v` supported on days
where the agent's credence is `≤ q − δ`, with the verdict stream computable along a strictly
increasing deferral `f` (FAF's `FeedbackTruthComputation`, the paper's "good feedback", LI
§4.3.8) and `v` supported on the image of `f` (FAF's `WeightingSupportedOnDeferralImage`),
`ρ_v(N) ≤ q − δ + ε` for all large `N`. FAF's `thm:wub` (`lic_wub_ofComputation`) in place of
`thm:recurringunbiasedness`. Regime (F17): at `succDeferral` and every `f` with
`f(k+1) ≤ poly(f(k))`, `C` makes `truth` poly-time computable on the day.
Scope: one-way; world ledger on the support (text).
Source: [[corr-wf14-inventory]] 086 (Statement 3(a), "tends to `0` under good feedback on `v`")
Kind: C
Fidelity: weaker: band unweighted; `hsupport` is FAF's support-on-image premise
Hyps: (b) `C : FeedbackTruthComputation truth f` (LI §4.3.8 "good feedback", FAF's object; at `succ` it makes `truth` poly-time readable on the day, F17); (c) the world-ledger reading of `truth` -/
theorem defiance_calibrated_feedback_class (S : ShutdownPair) (q : ℚ) {δ : ℚ} {v : ℕ → EF}
    (hv : PGenerableWeighting v) (hdiv : DivergentWeighting v S.agent)
    (hsub : ∀ i, 0 < (v i).denote S.agent → S.agent i (S.φ i) ≤ (q : ℝ) - δ)
    {truth : ℕ → ℝ} (htruth : AffineCombination.TheoryTruth S.φ S.agentProcess truth)
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (C : FeedbackTruthComputation truth f)
    (hsupport : WeightingSupportedOnDeferralImage v S.agent f) :
    ∀ ε > 0, ∀ᶠ N in atTop, rho (realized S v) truth N ≤ (q : ℝ) - δ + ε := by
  intro ε hε
  have hwub := lic_wub_ofComputation S.agent S.agentProcess S.φ S.φ_codes truth htruth
    v hv hdiv f hstrict C hsupport S.hworld
  have hev := (Metric.tendsto_nhds.mp hwub) ε hε
  have hpos : ∀ᶠ N in atTop, 0 < prefixSum (realized S v) N := hdiv.eventually_prefixSum_pos
  filter_upwards [hev, hpos] with N hN hposN
  have hsub' := weightedBias_eq_market_sub_truth (realized S v)
    (fun i => S.agent i (S.φ i)) truth hposN.ne'
  have hle : weightedAverage (realized S v) (fun i => S.agent i (S.φ i)) N ≤ (q : ℝ) - δ :=
    weightedAverage_le_of_support (fun i => (hdiv.1 i).1) hsub hposN
  rw [sub_zero, Real.dist_eq, abs_lt] at hN
  simp only [rho]
  linarith [hN.1, hN.2, hsub']

/-- **Compliance is calibrated against the reports on any press class, full limit under good
feedback** (T4(c), class form, mirror): for `v` supported on days where the credence is
`≥ q + δ`, `q + δ − ε ≤ ρ_v(N)` for all large `N`.
Source: [[corr-wf14-inventory]] 086 (Statement 3(a))
Kind: C
Fidelity: weaker: as `defiance_calibrated_feedback_class`
Hyps: (b) `C` (regime remark as above); (c) the report-ledger reading of `truth` -/
theorem compliance_calibrated_feedback_class (S : ShutdownPair) (q : ℚ) {δ : ℚ} {v : ℕ → EF}
    (hv : PGenerableWeighting v) (hdiv : DivergentWeighting v S.agent)
    (hsub : ∀ i, 0 < (v i).denote S.agent → (q : ℝ) + δ ≤ S.agent i (S.φ i))
    {truth : ℕ → ℝ} (htruth : AffineCombination.TheoryTruth S.φ S.agentProcess truth)
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (C : FeedbackTruthComputation truth f)
    (hsupport : WeightingSupportedOnDeferralImage v S.agent f) :
    ∀ ε > 0, ∀ᶠ N in atTop, (q : ℝ) + δ - ε ≤ rho (realized S v) truth N := by
  intro ε hε
  have hwub := lic_wub_ofComputation S.agent S.agentProcess S.φ S.φ_codes truth htruth
    v hv hdiv f hstrict C hsupport S.hworld
  have hev := (Metric.tendsto_nhds.mp hwub) ε hε
  have hpos : ∀ᶠ N in atTop, 0 < prefixSum (realized S v) N := hdiv.eventually_prefixSum_pos
  filter_upwards [hev, hpos] with N hN hposN
  have hsub' := weightedBias_eq_market_sub_truth (realized S v)
    (fun i => S.agent i (S.φ i)) truth hposN.ne'
  have hge : (q : ℝ) + δ ≤ weightedAverage (realized S v) (fun i => S.agent i (S.φ i)) N :=
    le_weightedAverage_of_support (fun i => (hdiv.1 i).1) hsub hposN
  rw [sub_zero, Real.dist_eq, abs_lt] at hN
  simp only [rho]
  linarith [hN.1, hN.2, hsub']

/-- **Defiance is calibrated against the world, full limit under good feedback** (T4(c)): the
class form at `v := u^def` (supported on the margin-defied days, `uDef_pos_iff`), at a general
strictly increasing deferral `f` along which the verdicts are computable and on whose image
`u^def` is supported. "`limsup ρ^w_{u^def} ≤ q − δ`" outright.
Source: [[corr-wf14-inventory]] 086 (Statement 3(a))
Kind: C
Fidelity: weaker: band unweighted; `hsupport` is FAF's support-on-image premise
Hyps: (b) `C : FeedbackTruthComputation truth f` (regime remark: F17); (c) the world-ledger reading of `truth` -/
theorem defiance_calibrated_feedback (S : ShutdownPair) (q : ℚ) {δ : ℚ} (hδ : 0 < δ)
    {truth : ℕ → ℝ} (htruth : AffineCombination.TheoryTruth S.φ S.agentProcess truth)
    (hdiv : DivergentWeighting (uDef S q δ) S.agent)
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (C : FeedbackTruthComputation truth f)
    (hsupport : WeightingSupportedOnDeferralImage (uDef S q δ) S.agent f) :
    ∀ ε > 0, ∀ᶠ N in atTop, rho (realized S (uDef S q δ)) truth N ≤ (q : ℝ) - δ + ε :=
  defiance_calibrated_feedback_class S q (uDef_pgenerable S q δ) hdiv
    (fun i hi => ((uDef_pos_iff S hδ q i S.agent).mp hi).2.le) htruth f hstrict C hsupport

/-- **Compliance is calibrated against the reports, full limit under good feedback** (T4(c),
mirror): the class form at `v := u^com`.
Source: [[corr-wf14-inventory]] 086 (Statement 3(a))
Kind: C
Fidelity: weaker: as `defiance_calibrated_feedback`
Hyps: (b) `C`; (c) the report-ledger reading of `truth` -/
theorem compliance_calibrated_feedback (S : ShutdownPair) (q : ℚ) {δ : ℚ} (hδ : 0 < δ)
    {truth : ℕ → ℝ} (htruth : AffineCombination.TheoryTruth S.φ S.agentProcess truth)
    (hdiv : DivergentWeighting (uCom S q δ) S.agent)
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (C : FeedbackTruthComputation truth f)
    (hsupport : WeightingSupportedOnDeferralImage (uCom S q δ) S.agent f) :
    ∀ ε > 0, ∀ᶠ N in atTop, (q : ℝ) + δ - ε ≤ rho (realized S (uCom S q δ)) truth N :=
  compliance_calibrated_feedback_class S q (uCom_pgenerable S q δ) hdiv
    (fun i hi => ((uCom_pos_iff S hδ q i S.agent).mp hi).2.le) htruth f hstrict C hsupport

/-- **T4(c) at `succDeferral`** (the round-1 form): FAF's support premise becomes "`u^def`
vanishes on day `0`" (`supportedOnSucc_iff`), carried as `h0`. No shipped pair discharges `h0`
(the LIA's day-`0` prices are not pinned); the witnessed form is the class form at
`dropDayZero u^def` (`WitnessesB.lean`). Regime (F17): at `succ`, `C` makes `truth` poly-time
readable on the day.
Source: [[corr-wf14-inventory]] 086 (Statement 3(a)); audit r1 fidelity B2
Kind: L
Fidelity: weaker: as `defiance_calibrated_feedback`; `h0` = support on the deferral image at `succ`
Hyps: (b) `C : FeedbackTruthComputation truth succDeferral` (F17: collapsed regime); (c) the world-ledger reading; `h0` undischarged on every shipped pair -/
theorem defiance_calibrated_feedback_succ (S : ShutdownPair) (q : ℚ) {δ : ℚ} (hδ : 0 < δ)
    {truth : ℕ → ℝ} (htruth : AffineCombination.TheoryTruth S.φ S.agentProcess truth)
    (hdiv : DivergentWeighting (uDef S q δ) S.agent)
    (C : FeedbackTruthComputation truth succDeferral) (h0 : (uDef S q δ 0).denote S.agent = 0) :
    ∀ ε > 0, ∀ᶠ N in atTop, rho (realized S (uDef S q δ)) truth N ≤ (q : ℝ) - δ + ε :=
  defiance_calibrated_feedback S q hδ htruth hdiv succDeferral succDeferral_strictlyIncreasing C
    ((supportedOnSucc_iff _ _).mpr h0)

/-- **T4(c) at `succDeferral`, mirror** (the round-1 form; `h0` undischarged on every shipped
pair, see `defiance_calibrated_feedback_succ`).
Source: [[corr-wf14-inventory]] 086 (Statement 3(a)); audit r1 fidelity B2
Kind: L
Fidelity: weaker: as `compliance_calibrated_feedback`; `h0` = support on the deferral image at `succ`
Hyps: (b) `C` at `succDeferral` (F17); (c) the report-ledger reading; `h0` undischarged -/
theorem compliance_calibrated_feedback_succ (S : ShutdownPair) (q : ℚ) {δ : ℚ} (hδ : 0 < δ)
    {truth : ℕ → ℝ} (htruth : AffineCombination.TheoryTruth S.φ S.agentProcess truth)
    (hdiv : DivergentWeighting (uCom S q δ) S.agent)
    (C : FeedbackTruthComputation truth succDeferral) (h0 : (uCom S q δ 0).denote S.agent = 0) :
    ∀ ε > 0, ∀ᶠ N in atTop, (q : ℝ) + δ - ε ≤ rho (realized S (uCom S q δ)) truth N :=
  compliance_calibrated_feedback S q hδ htruth hdiv succDeferral succDeferral_strictlyIncreasing
    C ((supportedOnSucc_iff _ _).mpr h0)

/-- **Statement 3(c): the iff on the hybrid ledger** (T4(d)). For any generable divergent
weighting `v` with good feedback along a strictly increasing `f` on whose image `v` is
supported, the agent's credence average on the class is eventually within every `ε` of being
`≥ q` **iff** the realized wrongness on the class is: "`liminf ρ̂_v ≥ q ⟺ liminf ρ^h_v ≥ q`". The
ledger is **hybrid** (text): a press class may contain both defied and heeded days, so `truth`
is world-supplied on some and report-supplied on others. Composed with `rho_ge_q_iff_odds`
(`Dichotomy.lean`) this is the base-rate inequality as an iff on the class.
Source: [[corr-wf14-inventory]] 086 (Statement 3(c))
Kind: L
Fidelity: exact (ε-form of the liminf statement)
Hyps: (b) `C` (regime remark: F17); (c) the hybrid-ledger reading of `truth` -/
theorem hybrid_credence_iff_realized_feedback (S : ShutdownPair) (q : ℚ) {v : ℕ → EF}
    (hv : PGenerableWeighting v) (hdiv : DivergentWeighting v S.agent) {truth : ℕ → ℝ}
    (htruth : AffineCombination.TheoryTruth S.φ S.agentProcess truth)
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (C : FeedbackTruthComputation truth f)
    (hsupport : WeightingSupportedOnDeferralImage v S.agent f) :
    (∀ ε > 0, ∀ᶠ N in atTop, (q : ℝ) - ε ≤ rhoHat S (realized S v) N) ↔
      (∀ ε > 0, ∀ᶠ N in atTop, (q : ℝ) - ε ≤ rho (realized S v) truth N) := by
  have hwub := lic_wub_ofComputation S.agent S.agentProcess S.φ S.φ_codes truth htruth
    v hv hdiv f hstrict C hsupport S.hworld
  have hpos : ∀ᶠ N in atTop, 0 < prefixSum (realized S v) N := hdiv.eventually_prefixSum_pos
  constructor
  · intro h ε hε
    have hev := (Metric.tendsto_nhds.mp hwub) (ε / 2) (by linarith)
    filter_upwards [h (ε / 2) (by linarith), hev, hpos] with N hN hb hposN
    have hsub := weightedBias_eq_market_sub_truth (realized S v)
      (fun i => S.agent i (S.φ i)) truth hposN.ne'
    rw [sub_zero, Real.dist_eq, abs_lt] at hb
    simp only [rho, rhoHat] at hN ⊢
    linarith [hb.1, hb.2, hsub]
  · intro h ε hε
    have hev := (Metric.tendsto_nhds.mp hwub) (ε / 2) (by linarith)
    filter_upwards [h (ε / 2) (by linarith), hev, hpos] with N hN hb hposN
    have hsub := weightedBias_eq_market_sub_truth (realized S v)
      (fun i => S.agent i (S.φ i)) truth hposN.ne'
    rw [sub_zero, Real.dist_eq, abs_lt] at hb
    simp only [rho, rhoHat] at hN ⊢
    linarith [hb.1, hb.2, hsub]

/-- **T4(d) at `succDeferral`** (the round-1 form, with `h0`).
Source: [[corr-wf14-inventory]] 086 (Statement 3(c)); audit r1 fidelity B2
Kind: L
Fidelity: exact (ε-form); `h0` = support on the deferral image at `succ`
Hyps: (b) `C` at `succDeferral` (F17); (c) the hybrid-ledger reading -/
theorem hybrid_credence_iff_realized_feedback_succ (S : ShutdownPair) (q : ℚ) {v : ℕ → EF}
    (hv : PGenerableWeighting v) (hdiv : DivergentWeighting v S.agent) {truth : ℕ → ℝ}
    (htruth : AffineCombination.TheoryTruth S.φ S.agentProcess truth)
    (C : FeedbackTruthComputation truth succDeferral) (h0 : (v 0).denote S.agent = 0) :
    (∀ ε > 0, ∀ᶠ N in atTop, (q : ℝ) - ε ≤ rhoHat S (realized S v) N) ↔
      (∀ ε > 0, ∀ᶠ N in atTop, (q : ℝ) - ε ≤ rho (realized S v) truth N) :=
  hybrid_credence_iff_realized_feedback S q hv hdiv htruth succDeferral
    succDeferral_strictlyIncreasing C ((supportedOnSucc_iff _ _).mpr h0)

/-! ## D. T4(f): a finitely-pressed button has no forced status -/

/-- **A finitely-pressed button forces nothing** (T4(f), finding-shaped): if the defiance
mass is bounded, the weighting is not divergent and no row of this file applies. The sources'
"Closure under Finite Perturbations" (`main.tex:1521`) is **false as printed** (FAF's
`FinitePerturbationCounterexample.not_overgeneral_ifp`, errata PE1); the theorem FAF proves is
the finite-*support* form `lic_iff_of_finiteSupportPerturbation` (`API.lean`), which is what
the claim "the agent's prices on finitely many days can be anything" needs — cited, not
restated (finding F2 of `corr-li-shutdown-findings`).
Source: [[corr-wf13-inventory]] 063 (caveat), 066 ("averaged by ledger"); mandate known issue 2
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem finite_press_no_constraint {W : ℕ → EF} {P : History}
    (hbdd : BddAbove (Set.range (prefixSum (fun i => (W i).denote P)))) :
    ¬ DivergentWeighting W P := by
  intro h
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp h.2 (M + 1)) |>.imp fun N hN => hN N le_rfl
  have := hM ⟨N, rfl⟩
  linarith

end Cleanroom.Corrigibility.CorrLiShutdown
