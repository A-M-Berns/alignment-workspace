/-
  Kernel-checked core of the FAITHFUL-ACCELERATION argument
  (`faithful-acceleration.md`, §5): the credence round-trip trader that forces
  (soft) Total Trust of a human H in an AI A which forecasts H's own future credences.

  Discipline (identical to the other modules): the genuine arithmetic/asymptotic
  cores are PROVED outright; the Logical-Induction facts enter ONLY as named
  hypotheses — here, A's calibration (Expectation Unbiasedness From Feedback) as the
  vanishing weighted bias `C n / W n → 0`, and H's no-Dutch-book criterion as the
  bound on the trader's plausible value. No `sorry`; axiom audit at the end.

  The setup, per element n (all are H-market quantities except a, A's forecast):
    w n = the (continuous, one-sided) weight  Ind_δ(a n > t)        (≥ 0; >0 ⇒ a n > t)
    p n = E^H_n(X)              H's current price          (< t-ε where the trade fires)
    v n = E^H_{f(n)}(X)         H's future price           (the round-trip cash-out)
    a n = E^A_n(⌜E^H_{f(n)}(X)⌝)  A's forecast of H's future credence
  Partial sums over the days where the trade fires:
    P n = Σ w (v - p)   the trader's banked value      (what the criterion bounds)
    C n = Σ w (v - a)   the weighted forecast bias     (→ 0 relative to W: calibration)
    W n = Σ w           the accumulated weight         (→ ∞ iff the violation persists)

  Map to the note:
    round_profit_ge        per-day: each weighted round-trip nets ≥ bias-term + ε·weight
    profit_partial_sum_ge  summed:  P n ≥ C n + ε·W n
    profit_diverges        calibration (C/W→0) + persistent violation (W→∞) ⇒ P→∞
    violation_not_persistent  + the criterion (P bounded) ⇒ ¬(W→∞), i.e. soft Total Trust
-/
import Mathlib

open Filter Topology

namespace FaithfulAccel

/-- **Per-day profit bound (exact).**  On a day where the trade fires (`0 < w`), the AI
    forecasts high (`t < a`) and the human is currently low (`p < t - ε`); the round-trip
    holding `w` units of `X` from now to the lookahead nets `w·(v - p)`, which is at least
    the day's forecast-bias term `w·(v - a)` plus a clean `ε·w`.  (On `w = 0` both sides
    vanish.)  This is the per-element engine; calibration handles the bias term in the sum. -/
theorem round_profit_ge (w v p a t ε : ℝ) (hw : 0 ≤ w)
    (hone : 0 < w → t < a) (hmis : 0 < w → p < t - ε) :
    w * (v - a) + ε * w ≤ w * (v - p) := by
  rcases eq_or_lt_of_le hw with h | h
  · simp [← h]
  · have ha := hone h
    have hp := hmis h
    have key : 0 < w * (a - p - ε) := mul_pos h (by linarith)
    nlinarith [key]

/-- **Summed profit bound.**  Summing `round_profit_ge` over the first `n` days gives
    `P n ≥ C n + ε·W n`, where `P`, `C`, `W` are the partial sums of `w(v-p)`, `w(v-a)`, `w`. -/
theorem profit_partial_sum_ge (w v p a : ℕ → ℝ) (t ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hone : ∀ i, 0 < w i → t < a i) (hmis : ∀ i, 0 < w i → p i < t - ε) :
    ∀ n,
      (∑ i ∈ Finset.range n, w i * (v i - a i)) + ε * (∑ i ∈ Finset.range n, w i)
        ≤ ∑ i ∈ Finset.range n, w i * (v i - p i) := by
  intro n
  have h1 :
      (∑ i ∈ Finset.range n, w i * (v i - a i)) + ε * (∑ i ∈ Finset.range n, w i)
        = ∑ i ∈ Finset.range n, (w i * (v i - a i) + ε * w i) := by
    simp only [Finset.mul_sum, Finset.sum_add_distrib]
  rw [h1]
  exact Finset.sum_le_sum (fun i _ =>
    round_profit_ge (w i) (v i) (p i) (a i) t ε (hw i) (hone i) (hmis i))

/-- **The trader's value diverges.**  Given the summed bound `C n + ε·W n ≤ P n`, A's
    **calibration** (the weighted bias is `o(W)`, here `C n / W n → 0`), and a **persistent
    violation** (`W n → ∞`), the trader's banked value `P n → ∞`.  Proof: eventually
    `C n / W n > -ε/2`, so `P n ≥ C n + ε·W n > (ε/2)·W n → ∞`. -/
theorem profit_diverges (P C W : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hPC : ∀ n, C n + ε * W n ≤ P n)
    (hbias : Tendsto (fun n => C n / W n) atTop (𝓝 0))
    (hW : Tendsto W atTop atTop) :
    Tendsto P atTop atTop := by
  have hWinf : Tendsto (fun n => (ε / 2) * W n) atTop atTop :=
    Tendsto.const_mul_atTop (by linarith) hW
  have hWpos : ∀ᶠ n in atTop, 0 < W n := hW.eventually_gt_atTop 0
  have hev : ∀ᶠ n in atTop, (ε / 2) * W n ≤ P n := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hbias (ε / 2) (by linarith)
    filter_upwards [hWpos, eventually_atTop.2 ⟨N, hN⟩] with n hWn hclose
    simp only [Real.dist_eq, sub_zero] at hclose
    have hcw : -(ε / 2) < C n / W n := (abs_lt.1 hclose).1
    have hC : -(ε / 2) * W n < C n := by
      have hmul := mul_lt_mul_of_pos_right hcw hWn
      rwa [div_mul_cancel₀ _ (ne_of_gt hWn)] at hmul
    have hring : -(ε / 2) * W n + ε * W n = (ε / 2) * W n := by ring
    linarith [hPC n]
  exact tendsto_atTop_mono' atTop hev hWinf

/-- **Soft Total Trust (the contrapositive).**  The human's no-Dutch-book criterion bounds
    its own trader's plausible value (`P n ≤ M`).  With A's calibration (`C/W → 0`) and the
    summed bound, the violation cannot persist: `¬ (W n → ∞)`.  That is, the weight `W`
    accumulated where "A forecasts ≥ t yet H sits below t − ε" stays bounded — soft Total
    Trust of H in A.  (The exploit itself — unbounded value, bounded risk — is the trusted
    LI criterion, exactly as in the other trader modules.) -/
theorem violation_not_persistent (P C W : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hPC : ∀ n, C n + ε * W n ≤ P n)
    (hbias : Tendsto (fun n => C n / W n) atTop (𝓝 0))
    (hbdd : ∃ M, ∀ n, P n ≤ M) :
    ¬ Tendsto W atTop atTop := by
  intro hW
  obtain ⟨M, hM⟩ := hbdd
  have hP := profit_diverges P C W ε hε hPC hbias hW
  obtain ⟨n, hn⟩ := (tendsto_atTop.1 hP (M + 1)).exists
  linarith [hM n]

/-- **End-to-end (composition).**  From the per-day data — nonnegativity, one-sidedness
    (`0 < w ⇒ t < a`), the violation (`0 < w ⇒ p < t − ε`), A's calibration (the weighted
    bias `C/W → 0` with `C`, `W` the partial sums), and the criterion bound — the violation
    weight `W` is not divergent.  Bundles `profit_partial_sum_ge` + `violation_not_persistent`. -/
theorem soft_total_trust (w v p a : ℕ → ℝ) (t ε : ℝ) (hε : 0 < ε)
    (hw : ∀ i, 0 ≤ w i) (hone : ∀ i, 0 < w i → t < a i) (hmis : ∀ i, 0 < w i → p i < t - ε)
    (hbias : Tendsto
      (fun n => (∑ i ∈ Finset.range n, w i * (v i - a i)) / (∑ i ∈ Finset.range n, w i))
      atTop (𝓝 0))
    (hbdd : ∃ M, ∀ n, (∑ i ∈ Finset.range n, w i * (v i - p i)) ≤ M) :
    ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop :=
  violation_not_persistent
    (fun n => ∑ i ∈ Finset.range n, w i * (v i - p i))
    (fun n => ∑ i ∈ Finset.range n, w i * (v i - a i))
    (fun n => ∑ i ∈ Finset.range n, w i) ε hε
    (profit_partial_sum_ge w v p a t ε hw hone hmis) hbias hbdd

/-- Non-vacuity: a concrete instance (`w ≡ 1`, `v ≡ 1`, `a ≡ 1`, `p ≡ 0`) satisfying the
    `profit_diverges` hypotheses with `W n = n → ∞` and `P n = n → ∞`, so the divergence
    conclusion is real, not vacuous. -/
theorem profit_diverges_nonvacuous :
    ∃ (P C W : ℕ → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ n, C n + ε * W n ≤ P n) ∧
      Tendsto (fun n => C n / W n) atTop (𝓝 0) ∧
      Tendsto W atTop atTop ∧
      Tendsto P atTop atTop := by
  refine ⟨(fun n => (n : ℝ)), (fun _ => 0), (fun n => (n : ℝ)), 1/4, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro n; show (0 : ℝ) + 1 / 4 * (n : ℝ) ≤ (n : ℝ)
    have h : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  · simp
  · exact tendsto_natCast_atTop_atTop
  · exact tendsto_natCast_atTop_atTop

/- ====================================================================================
   The doubly-soft weight, CONSTRUCTED and verified (the trader-legality the abstract `w` hid).
   `soft_total_trust` above takes `w` abstractly, with only the support hypotheses `hone`/`hmis`
   — so it cannot tell a legal weight from the buggy hard-restriction-to-a-violation-set weight
   (both satisfy `hone`/`hmis`).  Here we build the actual §5 weight, the doubly-soft gate
   `Ind_δ(a−t)·Ind_δ(t−ε−p)`, and PROVE it is **continuous** in the price pair (the heart of
   trader-legality, which a hard indicator violates), nonnegative, and one-sided — so `hone`,
   `hmis` are now theorems about the construction, not assumptions.  Still named: that
   continuity upgrades to full 𝒞_H-expressible-feature legality, and the LI inputs `hbias`/`hbdd`.
   ==================================================================================== -/

/-- The soft (continuous) indicator: a clamp ramping `0 → 1` over `[0, δ]`. -/
noncomputable def softInd (δ x : ℝ) : ℝ := max 0 (min 1 (x / δ))

theorem softInd_nonneg (δ x : ℝ) : 0 ≤ softInd δ x := le_max_left _ _

/-- The legality-relevant property: the soft indicator is **continuous**. -/
theorem softInd_continuous (δ : ℝ) : Continuous (softInd δ) := by
  unfold softInd; fun_prop

/-- One-sidedness: a positive soft-indicator value certifies its argument is positive. -/
theorem softInd_pos_imp (δ x : ℝ) (hδ : 0 < δ) (h : 0 < softInd δ x) : 0 < x := by
  unfold softInd at h
  have h1 : 0 < min 1 (x / δ) := (lt_max_iff.1 h).resolve_left (lt_irrefl 0)
  have h2 : 0 < x / δ := lt_of_lt_of_le h1 (min_le_right 1 (x / δ))
  have h3 := mul_pos h2 hδ
  rwa [div_mul_cancel₀ _ (ne_of_gt hδ)] at h3

/-- The **doubly-soft weight** of §5: positive only where `a > t` *and* `p < t − ε`. -/
noncomputable def dsWeight (t ε δ a p : ℝ) : ℝ := softInd δ (a - t) * softInd δ (t - ε - p)

theorem dsWeight_nonneg (t ε δ a p : ℝ) : 0 ≤ dsWeight t ε δ a p :=
  mul_nonneg (softInd_nonneg _ _) (softInd_nonneg _ _)

/-- **Joint continuity** of the doubly-soft weight in the price pair `(a, p)` — the legal-trader
    property the §5 fix supplies and the hard-restriction violated. -/
theorem dsWeight_continuous (t ε δ : ℝ) :
    Continuous (fun ap : ℝ × ℝ => dsWeight t ε δ ap.1 ap.2) := by
  unfold dsWeight softInd; fun_prop

theorem dsWeight_pos_imp_fst (t ε δ a p : ℝ) (hδ : 0 < δ) (h : 0 < dsWeight t ε δ a p) :
    t < a := by
  unfold dsWeight at h
  have hf : 0 < softInd δ (a - t) := by
    rcases mul_pos_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 (not_lt.2 (softInd_nonneg _ _))
  linarith [softInd_pos_imp δ (a - t) hδ hf]

theorem dsWeight_pos_imp_snd (t ε δ a p : ℝ) (hδ : 0 < δ) (h : 0 < dsWeight t ε δ a p) :
    p < t - ε := by
  unfold dsWeight at h
  have hs : 0 < softInd δ (t - ε - p) := by
    rcases mul_pos_iff.1 h with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2
    · exact absurd h2 (not_lt.2 (softInd_nonneg _ _))
  linarith [softInd_pos_imp δ (t - ε - p) hδ hs]

/-- **`soft_total_trust` with the weight constructed and `hone`/`hmis` discharged.**  Instantiated
    at the doubly-soft weight, the only remaining hypotheses are the named LI inputs — A's
    calibration `hbias` and H's no-Dutch-book criterion `hbdd`.  The support properties are now
    *proved* (`dsWeight_pos_imp_fst`/`_snd`) and the weight is the genuine continuous gate
    (`dsWeight_continuous`), not an abstract `w` that an illegal trader could also satisfy. -/
theorem soft_total_trust_doublysoft (v p a : ℕ → ℝ) (t ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hbias : Tendsto
      (fun n => (∑ i ∈ Finset.range n, dsWeight t ε δ (a i) (p i) * (v i - a i))
              / (∑ i ∈ Finset.range n, dsWeight t ε δ (a i) (p i))) atTop (𝓝 0))
    (hbdd : ∃ M, ∀ n, (∑ i ∈ Finset.range n, dsWeight t ε δ (a i) (p i) * (v i - p i)) ≤ M) :
    ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, dsWeight t ε δ (a i) (p i)) atTop atTop :=
  soft_total_trust (fun i => dsWeight t ε δ (a i) (p i)) v p a t ε hε
    (fun i => dsWeight_nonneg t ε δ (a i) (p i))
    (fun i h => dsWeight_pos_imp_fst t ε δ (a i) (p i) hδ h)
    (fun i h => dsWeight_pos_imp_snd t ε δ (a i) (p i) hδ h)
    hbias hbdd

end FaithfulAccel

-- Axiom audit: each must rest on ONLY [propext, Classical.choice, Quot.sound] (no `sorryAx`).
#print axioms FaithfulAccel.round_profit_ge
#print axioms FaithfulAccel.profit_partial_sum_ge
#print axioms FaithfulAccel.profit_diverges
#print axioms FaithfulAccel.violation_not_persistent
#print axioms FaithfulAccel.soft_total_trust
#print axioms FaithfulAccel.profit_diverges_nonvacuous
#print axioms FaithfulAccel.softInd_continuous
#print axioms FaithfulAccel.softInd_pos_imp
#print axioms FaithfulAccel.dsWeight_continuous
#print axioms FaithfulAccel.dsWeight_pos_imp_fst
#print axioms FaithfulAccel.dsWeight_pos_imp_snd
#print axioms FaithfulAccel.soft_total_trust_doublysoft
