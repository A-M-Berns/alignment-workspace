/-
  run3 TODO 1 — `legit-gate-classes`
  Legitimacy gates vs. the calibration class: "predict only through non-corrupt
  futures" (li-deference.md §0.3) modeled as a gate `c : ℕ → ℝ`, `c n ∈ [0,1]`,
  multiplying the faithful-acceleration violation weight.

  STANDALONE file (GROUND-RULES §2): does NOT import LeanDeference.  The block
  marked COPIED below is copied verbatim from
  `lean-deference/FaithfulAcceleration.lean` (lines 28–213, module
  FaithfulAccel, sorry-free, audited in lean-deference/AUDIT.md §2.4) with the
  citation comments required by the standalone-file discipline.  Nothing in the
  copied block is claimed as new.  The AUDIT classification travels with the
  citation: in `soft_total_trust` the LI inputs `hbias` (calibration =
  Expectation Unbiasedness From Feedback, LI paper Thm 4.8.16) and `hbdd` (the
  no-Dutch-book criterion) are NAMED hypotheses, not proved; the market and
  traders are unmodeled.  Everything below inherits that boundary and never
  pretends otherwise.

  NEW content (this file):
    Theorem-1 family (gated chain, weaker antecedent):
      pos_of_gated_pos, gated_soft_total_trust, gated_soft_total_trust_doublysoft,
      gated_conclusion_from_ungated (the logical-geography remark),
      weaker_antecedent_ungated_fails / weaker_antecedent_gated_holds (the
      compiled strictness witness), gated_weight_diverges (non-vacuity of the
      gate used in the witnesses: it keeps infinite mass).
    Theorem-2 family (gating breaks calibration — the honest heart):
      ungated_calibration (Tendsto, partial-sum cancellation, w ≡ 1, bias (−1)^n),
      gated_calibration_fails (¬Tendsto — the error-correlated even-days gate
      pins the gated ratio at 1), deletion_test (gate ≡ 1 recovers the Tendsto:
      the corruption deletion test), cEven_not_pairClass (the destructive gate
      sits outside the closure class of Theorem 3).
    Theorem-3 family (closure):
      closure_gated_soft_total_trust (abstract: calibration on a class 𝒲 closed
      under gates 𝒞 ⇒ gated soft Total Trust for every c ∈ 𝒞), PairClass (a
      concrete, structurally-defined class), pairClass_calibrated (calibration
      for the WHOLE class is PROVED, not assumed — pairwise cancellation plus a
      convergence dichotomy), pairClass_mul (closure PROVED), cMix (a
      non-constant interior-valued gate in the class, cMix_nonconstant),
      gated_calibration_via_closure and pairClass_closure_instance (the closure
      hypothesis doing visible work).
    Silence (prose obligation (b), compiled anchor):
      gate_silence — a gate with bounded total mass makes the gated conclusion
      vacuously true for EVERY weight stream: no protection where no obligation.

  Axiom audit at the end; expected [propext, Classical.choice, Quot.sound].
-/
import Mathlib

open Filter Topology

namespace LegitGate

/- ====================================================================================
   COPIED BLOCK — verbatim from lean-deference/FaithfulAcceleration.lean
   (namespace FaithfulAccel), lines 34–213.  Cited, not re-proved: the trader chain
   round_profit_ge → profit_partial_sum_ge → profit_diverges → violation_not_persistent
   → soft_total_trust, and the softInd/dsWeight construction with its support lemmas.
   ==================================================================================== -/

/-- COPIED: FaithfulAcceleration.lean L39. Per-day profit bound (exact). -/
theorem round_profit_ge (w v p a t ε : ℝ) (hw : 0 ≤ w)
    (hone : 0 < w → t < a) (hmis : 0 < w → p < t - ε) :
    w * (v - a) + ε * w ≤ w * (v - p) := by
  rcases eq_or_lt_of_le hw with h | h
  · simp [← h]
  · have ha := hone h
    have hp := hmis h
    have key : 0 < w * (a - p - ε) := mul_pos h (by linarith)
    nlinarith [key]

/-- COPIED: FaithfulAcceleration.lean L51. Summed profit bound: `P n ≥ C n + ε·W n`. -/
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

/-- COPIED: FaithfulAcceleration.lean L69. Calibration + persistent violation ⇒ P → ∞. -/
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

/-- COPIED: FaithfulAcceleration.lean L95. Criterion bound ⇒ the violation cannot persist. -/
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

/-- COPIED: FaithfulAcceleration.lean L110. End-to-end soft Total Trust (LI inputs named). -/
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

/-- COPIED: FaithfulAcceleration.lean L152. The soft (continuous) indicator. -/
noncomputable def softInd (δ x : ℝ) : ℝ := max 0 (min 1 (x / δ))

/-- COPIED: FaithfulAcceleration.lean L154. -/
theorem softInd_nonneg (δ x : ℝ) : 0 ≤ softInd δ x := le_max_left _ _

/-- COPIED: FaithfulAcceleration.lean L161. One-sidedness of the soft indicator. -/
theorem softInd_pos_imp (δ x : ℝ) (hδ : 0 < δ) (h : 0 < softInd δ x) : 0 < x := by
  unfold softInd at h
  have h1 : 0 < min 1 (x / δ) := (lt_max_iff.1 h).resolve_left (lt_irrefl 0)
  have h2 : 0 < x / δ := lt_of_lt_of_le h1 (min_le_right 1 (x / δ))
  have h3 := mul_pos h2 hδ
  rwa [div_mul_cancel₀ _ (ne_of_gt hδ)] at h3

/-- COPIED: FaithfulAcceleration.lean L169. The doubly-soft §5 violation weight. -/
noncomputable def dsWeight (t ε δ a p : ℝ) : ℝ := softInd δ (a - t) * softInd δ (t - ε - p)

/-- COPIED: FaithfulAcceleration.lean L171. -/
theorem dsWeight_nonneg (t ε δ a p : ℝ) : 0 ≤ dsWeight t ε δ a p :=
  mul_nonneg (softInd_nonneg _ _) (softInd_nonneg _ _)

/-- COPIED: FaithfulAcceleration.lean L180. -/
theorem dsWeight_pos_imp_fst (t ε δ a p : ℝ) (hδ : 0 < δ) (h : 0 < dsWeight t ε δ a p) :
    t < a := by
  unfold dsWeight at h
  have hf : 0 < softInd δ (a - t) := by
    rcases mul_pos_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 (not_lt.2 (softInd_nonneg _ _))
  linarith [softInd_pos_imp δ (a - t) hδ hf]

/-- COPIED: FaithfulAcceleration.lean L189. -/
theorem dsWeight_pos_imp_snd (t ε δ a p : ℝ) (hδ : 0 < δ) (h : 0 < dsWeight t ε δ a p) :
    p < t - ε := by
  unfold dsWeight at h
  have hs : 0 < softInd δ (t - ε - p) := by
    rcases mul_pos_iff.1 h with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2
    · exact absurd h2 (not_lt.2 (softInd_nonneg _ _))
  linarith [softInd_pos_imp δ (t - ε - p) hδ hs]

/- ====================================================================================
   END OF COPIED BLOCK.  Everything below is NEW (run3, this TODO).
   ==================================================================================== -/

/- ------------------------------------------------------------------------------------
   §1  THEOREM 1 — the gated trader chain, with a genuinely weaker antecedent.

   The §0.3 move "predict human feedback only through non-corrupted futures" becomes:
   multiply the violation weight `w` by a legitimacy gate `c : ℕ → ℝ`, `0 ≤ c`.
   The support/one-sidedness hypotheses TRANSFER from `w` to `c·w`
   (`pos_of_gated_pos`), so the whole copied chain applies to the gated weight —
   with calibration (`hbias`) required ONLY for the gated weight `c·w`.  The gate
   factor is visible in every sum of the statement.
   ------------------------------------------------------------------------------------ -/

/-- Transfer lemma: a positive gated weight certifies a positive raw weight
    (`0 < c n * w n → 0 < w n`), so the gated weight inherits the one-sidedness
    and violation support properties of the raw weight. -/
theorem pos_of_gated_pos {c w : ℝ} (hw : 0 ≤ w) (h : 0 < c * w) : 0 < w := by
  rcases hw.lt_or_eq with h' | h'
  · exact h'
  · exfalso
    rw [← h', mul_zero] at h
    exact lt_irrefl 0 h

/-- **Theorem 1 (gated soft Total Trust).**  The trader chain for the GATED violation
    weight `c·w`.  Note the antecedent: calibration `hbias_gated` and the criterion
    bound `hbdd_gated` are demanded for the gated weight ONLY — nothing is assumed
    about the ungated weight's calibration.  (That this antecedent is genuinely,
    strictly weaker than the ungated one is the compiled witness pair
    `weaker_antecedent_ungated_fails` / `weaker_antecedent_gated_holds` below;
    that it is genuinely needed — ungated calibration does NOT imply it — is
    Theorem 2, `gated_calibration_fails`.)  The conclusion: the gated violation
    weight does not accumulate — soft Total Trust on the legitimacy-flagged days. -/
theorem gated_soft_total_trust (c w v p a : ℕ → ℝ) (t ε : ℝ) (hε : 0 < ε)
    (hc : ∀ i, 0 ≤ c i)
    (hw : ∀ i, 0 ≤ w i) (hone : ∀ i, 0 < w i → t < a i) (hmis : ∀ i, 0 < w i → p i < t - ε)
    (hbias_gated : Tendsto
      (fun n => (∑ i ∈ Finset.range n, c i * w i * (v i - a i))
              / (∑ i ∈ Finset.range n, c i * w i)) atTop (𝓝 0))
    (hbdd_gated : ∃ M, ∀ n, (∑ i ∈ Finset.range n, c i * w i * (v i - p i)) ≤ M) :
    ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, c i * w i) atTop atTop :=
  soft_total_trust (fun i => c i * w i) v p a t ε hε
    (fun i => mul_nonneg (hc i) (hw i))
    (fun i h => hone i (pos_of_gated_pos (hw i) h))
    (fun i h => hmis i (pos_of_gated_pos (hw i) h))
    hbias_gated hbdd_gated

/-- **Theorem 1 at the real §5 weight.**  The gate composed with the corpus's
    doubly-soft violation weight `dsWeight` (copied above): the support hypotheses
    are DISCHARGED from the construction (as in `soft_total_trust_doublysoft`,
    FaithfulAcceleration.lean L203), and the only remaining hypotheses are the
    named LI inputs — for the GATED weight. -/
theorem gated_soft_total_trust_doublysoft (c v p a : ℕ → ℝ) (t ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hc : ∀ i, 0 ≤ c i)
    (hbias_gated : Tendsto
      (fun n => (∑ i ∈ Finset.range n, c i * dsWeight t ε δ (a i) (p i) * (v i - a i))
              / (∑ i ∈ Finset.range n, c i * dsWeight t ε δ (a i) (p i))) atTop (𝓝 0))
    (hbdd_gated : ∃ M, ∀ n,
      (∑ i ∈ Finset.range n, c i * dsWeight t ε δ (a i) (p i) * (v i - p i)) ≤ M) :
    ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, c i * dsWeight t ε δ (a i) (p i))
        atTop atTop :=
  gated_soft_total_trust c (fun i => dsWeight t ε δ (a i) (p i)) v p a t ε hε hc
    (fun i => dsWeight_nonneg t ε δ (a i) (p i))
    (fun i h => dsWeight_pos_imp_fst t ε δ (a i) (p i) hδ h)
    (fun i h => dsWeight_pos_imp_snd t ε δ (a i) (p i) hδ h)
    hbias_gated hbdd_gated

/-- **Logical geography (honesty lemma).**  For a `[0,1]` gate the gated CONCLUSION is
    monotonically implied by the ungated one (`∑ c·w ≤ ∑ w` termwise), so Theorem 1
    would be worthless if its antecedent were not weaker: the entire value of the
    gated theorem is that it reaches the gated conclusion from gated-class-only
    calibration.  This lemma states the trivial direction explicitly so the
    non-trivial one (the witness pair below) is visible against it. -/
theorem gated_conclusion_from_ungated (c w : ℕ → ℝ)
    (_hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) (hw : ∀ i, 0 ≤ w i)
    (h : ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) :
    ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, c i * w i) atTop atTop := by
  intro hg
  apply h
  refine tendsto_atTop_mono (fun n => Finset.sum_le_sum fun i _ => ?_) hg
  calc c i * w i ≤ 1 * w i := by
        have := mul_le_mul_of_nonneg_right (hc1 i) (hw i)
        simpa using this
    _ = w i := one_mul _

/- ------------------------------------------------------------------------------------
   §2  THE CONCRETE SEQUENCES.

   bAlt n = (−1)^n           the alternating forecast bias (v − a)
   bOdd n = 1 on odd days    a bias concentrated on odd days
   wOne  ≡ 1                 the uniform violation weight
   cEven n = 1 on even days  the ERROR-CORRELATED gate (keeps exactly the days the
                             forecast errs high) — Theorem 2's destroyer
   cOne  ≡ 1                 the trivialized gate (deletion test)
   cMix                      a NON-CONSTANT interior-valued gate (1 on days 4m,4m+1;
                             1/2 on days 4m+2,4m+3) — inside Theorem 3's class
   ------------------------------------------------------------------------------------ -/

noncomputable def bAlt (n : ℕ) : ℝ := (-1) ^ n

noncomputable def bOdd (n : ℕ) : ℝ := if n % 2 = 1 then 1 else 0

noncomputable def wOne (_ : ℕ) : ℝ := 1

noncomputable def cEven (n : ℕ) : ℝ := if n % 2 = 0 then 1 else 0

noncomputable def cOne (_ : ℕ) : ℝ := 1

noncomputable def cMix (n : ℕ) : ℝ := if n % 4 ≤ 1 then 1 else 1/2

lemma bAlt_even (m : ℕ) : bAlt (2 * m) = 1 := by
  unfold bAlt
  exact Even.neg_one_pow (even_two_mul m)

lemma bAlt_odd (m : ℕ) : bAlt (2 * m + 1) = -1 := by
  unfold bAlt
  exact Odd.neg_one_pow ⟨m, rfl⟩

lemma cEven_even (m : ℕ) : cEven (2 * m) = 1 := by
  have h : (2 * m) % 2 = 0 := by omega
  simp [cEven, h]

lemma cEven_odd (m : ℕ) : cEven (2 * m + 1) = 0 := by
  simp [cEven]

/- ------------------------------------------------------------------------------------
   §3  THEOREM 3's CLASS — defined FIRST because Theorem 2's positive half
   (`ungated_calibration`) is its `w ≡ 1` instance.

   PairClass: weights in [0,1] taking equal values on each day-pair {2m, 2m+1}.
   This is a STRUCTURAL condition (nothing about calibration is built in);
   calibration of the whole class against the alternating bias is a THEOREM
   (`pairClass_calibrated`: exact pairwise cancellation + a convergence
   dichotomy), and closure under pointwise multiplication is a THEOREM
   (`pairClass_mul`).  The destructive gate of Theorem 2 is OUTSIDE the class
   (`cEven_not_pairClass`) — the class boundary is exactly what separates the
   safe gates from the calibration-killer.
   ------------------------------------------------------------------------------------ -/

def PairClass : Set (ℕ → ℝ) :=
  {w | (∀ n, 0 ≤ w n) ∧ (∀ n, w n ≤ 1) ∧ (∀ m, w (2 * m + 1) = w (2 * m))}

lemma wOne_mem : wOne ∈ PairClass :=
  ⟨fun _ => by norm_num [wOne], fun _ => by norm_num [wOne], fun _ => rfl⟩

lemma cOne_mem : cOne ∈ PairClass :=
  ⟨fun _ => by norm_num [cOne], fun _ => by norm_num [cOne], fun _ => rfl⟩

/-- Closure: PairClass is closed under pointwise multiplication (in particular,
    under gating by any of its members).  A real, structural proof — not fiat. -/
lemma pairClass_mul (c w : ℕ → ℝ) (hc : c ∈ PairClass) (hw : w ∈ PairClass) :
    (fun i => c i * w i) ∈ PairClass := by
  obtain ⟨hc0, hc1, hcp⟩ := hc
  obtain ⟨hw0, hw1, hwp⟩ := hw
  refine ⟨fun n => mul_nonneg (hc0 n) (hw0 n), fun n => ?_, fun m => ?_⟩
  · calc c n * w n ≤ 1 * 1 := mul_le_mul (hc1 n) (hw1 n) (hw0 n) zero_le_one
      _ = 1 := one_mul 1
  · show c (2 * m + 1) * w (2 * m + 1) = c (2 * m) * w (2 * m)
    rw [hcp m, hwp m]

/-- The non-constant, interior-valued gate is in the class. -/
lemma cMix_mem : cMix ∈ PairClass := by
  refine ⟨fun n => ?_, fun n => ?_, fun m => ?_⟩
  · unfold cMix; split <;> norm_num
  · unfold cMix; split <;> norm_num
  · by_cases hm : m % 2 = 0
    · have h1 : (2 * m) % 4 ≤ 1 := by omega
      have h2 : (2 * m + 1) % 4 ≤ 1 := by omega
      simp [cMix, h1, h2]
    · have h1 : ¬ (2 * m) % 4 ≤ 1 := by omega
      have h2 : ¬ (2 * m + 1) % 4 ≤ 1 := by omega
      simp [cMix, h1, h2]

/-- Non-vacuity of the gate instance: `cMix` is genuinely non-constant
    (an interior-valued 1 / ½ mixture), not an inert relabeling. -/
lemma cMix_nonconstant : cMix 0 = 1 ∧ cMix 2 = 1/2 ∧ cMix 0 ≠ cMix 2 := by
  refine ⟨by norm_num [cMix], by norm_num [cMix], by norm_num [cMix]⟩

/-- **The class does visible work:** Theorem 2's calibration-destroying gate is NOT
    in the class — pair-equality fails at the very first pair. -/
lemma cEven_not_pairClass : cEven ∉ PairClass := by
  intro h
  have := h.2.2 0
  norm_num [cEven] at this

/-- Exact pairwise cancellation: over any even horizon, a pair-equal weight kills
    the alternating bias EXACTLY. -/
lemma pair_cancel (w : ℕ → ℝ) (hpair : ∀ m, w (2 * m + 1) = w (2 * m)) :
    ∀ m, ∑ i ∈ Finset.range (2 * m), w i * bAlt i = 0 := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
    have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        bAlt_even k, bAlt_odd k, hpair k]
    ring

/-- Closed form of the weighted-bias partial sum for a pair-equal weight. -/
lemma pair_num_eq (w : ℕ → ℝ) (hpair : ∀ m, w (2 * m + 1) = w (2 * m)) :
    ∀ n, ∑ i ∈ Finset.range n, w i * bAlt i = if n % 2 = 0 then 0 else w (n - 1) := by
  intro n
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, hm⟩ := he
    rw [← two_mul] at hm
    subst hm
    rw [pair_cancel w hpair m, if_pos (by omega)]
  · obtain ⟨m, hm⟩ := ho
    subst hm
    rw [Finset.sum_range_succ, pair_cancel w hpair m, bAlt_even m, if_neg (by omega)]
    have : 2 * m + 1 - 1 = 2 * m := by omega
    rw [this]
    ring

/-- **Calibration of the whole class, PROVED.**  Every weight in PairClass is
    calibrated against the alternating bias: the weighted-bias ratio tends to 0.
    Real analysis, not assumption: the numerator is exactly 0 at even horizons and
    a single term at odd ones; the proof splits on whether the weight mass diverges
    (numerator bounded by 1, denominator → ∞), converges to a positive limit
    (numerator → 0 by summability), or is identically zero (ratio ≡ 0 under Lean's
    junk-value division). -/
theorem pairClass_calibrated (w : ℕ → ℝ) (hw : w ∈ PairClass) :
    Tendsto (fun n => (∑ i ∈ Finset.range n, w i * bAlt i) / (∑ i ∈ Finset.range n, w i))
      atTop (𝓝 0) := by
  obtain ⟨h0, h1, hpair⟩ := hw
  have hbound : ∀ n, ‖∑ i ∈ Finset.range n, w i * bAlt i‖ ≤ w (n - 1) := by
    intro n
    rw [pair_num_eq w hpair n, Real.norm_eq_abs]
    split
    · simpa using h0 (n - 1)
    · rw [abs_of_nonneg (h0 (n - 1))]
  set den : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, w i with hden
  have hmono : Monotone den := by
    apply monotone_nat_of_le_succ
    intro n
    simp only [hden, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (h0 n)
  by_cases hdiv : Tendsto den atTop atTop
  · -- divergent mass: squeeze |ratio| ≤ 1/den → 0
    have hb1 : ∀ n, ‖∑ i ∈ Finset.range n, w i * bAlt i‖ ≤ 1 :=
      fun n => (hbound n).trans (h1 _)
    have hg : Tendsto (fun n => (den n)⁻¹) atTop (𝓝 0) := hdiv.inv_tendsto_atTop
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [hdiv.eventually_gt_atTop 0] with n hpos
    rw [norm_div, Real.norm_eq_abs (den n), abs_of_pos hpos, inv_eq_one_div]
    gcongr
    exact hb1 n
  · -- bounded mass: den converges; numerator → 0 by summability
    have hbdd : BddAbove (Set.range den) := by
      by_contra hb
      apply hdiv
      refine tendsto_atTop_atTop.2 fun b => ?_
      obtain ⟨x, ⟨n, rfl⟩, hx⟩ := not_bddAbove_iff.1 hb b
      exact ⟨n, fun k hk => le_trans hx.le (hmono hk)⟩
    obtain ⟨C, hC⟩ := hbdd
    have hCle : ∀ n, den n ≤ C := fun n => hC ⟨n, rfl⟩
    have hsummable : Summable w := summable_of_sum_range_le h0 hCle
    have hw0 : Tendsto w atTop (𝓝 0) := hsummable.tendsto_atTop_zero
    have hshift : Tendsto (fun n : ℕ => n - 1) atTop atTop :=
      tendsto_atTop_atTop.2 (fun b => ⟨b + 1, fun n hn => by omega⟩)
    have hnum0 : Tendsto (fun n => ∑ i ∈ Finset.range n, w i * bAlt i) atTop (𝓝 0) :=
      squeeze_zero_norm hbound (hw0.comp hshift)
    have hconv : Tendsto den atTop (𝓝 (⨆ n, den n)) :=
      tendsto_atTop_ciSup hmono ⟨C, hC⟩
    by_cases hL : (⨆ n, den n) = 0
    · -- all mass zero: ratio is identically 0 (division-by-zero convention)
      have hden0 : ∀ n, den n = 0 := by
        intro n
        have hle : den n ≤ ⨆ k, den k := le_ciSup ⟨C, hC⟩ n
        have hge : (0 : ℝ) ≤ den n := Finset.sum_nonneg (fun i _ => h0 i)
        rw [hL] at hle
        linarith
      have heq : (fun n => (∑ i ∈ Finset.range n, w i * bAlt i) / den n)
          = fun _ => (0 : ℝ) := by
        funext n
        rw [hden0 n, div_zero]
      rw [heq]
      exact tendsto_const_nhds
    · have := hnum0.div hconv hL
      simpa using this

/-- **Theorem 3 (abstract closure).**  If calibration holds for EVERY weight in a
    class `𝒲` and `𝒲` is closed under pointwise multiplication by gates in `𝒞`,
    then gated soft Total Trust holds for every `w ∈ 𝒲`, `c ∈ 𝒞` (with the support
    and criterion data as in Theorem 1): "legitimacy-gated deference is forced
    exactly as long as the gate keeps the weight inside the calibration class."
    The class hypotheses are exactly the TODO's encoding (`hbias_class` + `hclosed`);
    that they are NON-definitional is witnessed by the PairClass instance below,
    where both are proved from structure. -/
theorem closure_gated_soft_total_trust
    (𝒲 𝒞 : Set (ℕ → ℝ)) (w c v p a : ℕ → ℝ) (t ε : ℝ) (hε : 0 < ε)
    (hbias_class : ∀ u ∈ 𝒲, Tendsto
      (fun n => (∑ i ∈ Finset.range n, u i * (v i - a i)) / (∑ i ∈ Finset.range n, u i))
      atTop (𝓝 0))
    (hclosed : ∀ u ∈ 𝒲, ∀ g ∈ 𝒞, (fun i => g i * u i) ∈ 𝒲)
    (hw𝒲 : w ∈ 𝒲) (hc𝒞 : c ∈ 𝒞) (hc : ∀ i, 0 ≤ c i)
    (hw : ∀ i, 0 ≤ w i) (hone : ∀ i, 0 < w i → t < a i)
    (hmis : ∀ i, 0 < w i → p i < t - ε)
    (hbdd_gated : ∃ M, ∀ n, (∑ i ∈ Finset.range n, c i * w i * (v i - p i)) ≤ M) :
    ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, c i * w i) atTop atTop :=
  gated_soft_total_trust c w v p a t ε hε hc hw hone hmis
    (hbias_class _ (hclosed w hw𝒲 c hc𝒞)) hbdd_gated

/-- **Theorem 3, instantiated on the PairClass with both class hypotheses PROVED**
    (calibration by `pairClass_calibrated`, closure by `pairClass_mul`) — for any
    scenario whose forecast bias is the alternating one.  The gate `c` ranges over
    the whole class, which contains the non-constant `cMix`.  NOTE the honest
    conditional structure inherited from the corpus: `hone`/`hmis`/`hbdd` are the
    LI-side inputs, and for weights of divergent mass they are JOINTLY
    unsatisfiable with the conclusion's negation — that exclusion IS the theorem. -/
theorem pairClass_closure_instance (v p a : ℕ → ℝ) (t ε : ℝ) (hε : 0 < ε)
    (hva : ∀ i, v i - a i = bAlt i)
    (w c : ℕ → ℝ) (hw𝒫 : w ∈ PairClass) (hc𝒫 : c ∈ PairClass)
    (hone : ∀ i, 0 < w i → t < a i) (hmis : ∀ i, 0 < w i → p i < t - ε)
    (hbdd_gated : ∃ M, ∀ n, (∑ i ∈ Finset.range n, c i * w i * (v i - p i)) ≤ M) :
    ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, c i * w i) atTop atTop := by
  refine closure_gated_soft_total_trust PairClass PairClass w c v p a t ε hε
    ?_ (fun u hu g hg => pairClass_mul g u hg hu) hw𝒫 hc𝒫 hc𝒫.1 hw𝒫.1 hone hmis hbdd_gated
  intro u hu
  have hcal := pairClass_calibrated u hu
  refine hcal.congr fun n => ?_
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by rw [hva i])

/-- **The closure hypothesis doing visible work on the non-constant gate:** gated
    calibration for the interior-valued gate `cMix` on the uniform weight, derived
    THROUGH the class machinery (membership + closure + class calibration), not by
    direct computation. -/
theorem gated_calibration_via_closure :
    Tendsto (fun n => (∑ i ∈ Finset.range n, cMix i * wOne i * bAlt i)
                    / (∑ i ∈ Finset.range n, cMix i * wOne i)) atTop (𝓝 0) := by
  have h := pairClass_calibrated (fun i => cMix i * wOne i)
    (pairClass_mul cMix wOne cMix_mem wOne_mem)
  simpa using h

/- ------------------------------------------------------------------------------------
   §4  THEOREM 2 — gating BREAKS calibration (the honest heart, compiled).

   Ungated: w ≡ 1 against the alternating bias (−1)^n is calibrated — the
   partial sums cancel pairwise and the ratio → 0 (`ungated_calibration`, an
   instance of the class theorem).  Gate it by the ERROR-CORRELATED gate cEven
   (keep exactly the days the forecast errs high): the gated ratio is
   identically 1 from day 1 on — calibration is destroyed
   (`gated_calibration_fails`), even though the gated weight keeps INFINITE mass
   (`gated_weight_diverges` — the failure is not the silent/vacuous kind).
   Deleting the corruption (gate ≡ 1) provably recovers the Tendsto
   (`deletion_test`).  Interpretation (labeled): a "legitimacy" filter that
   correlates with the sign of the forecast error voids the forced-trust
   argument; "predict only through non-corrupt futures" is not free — it is a
   NEW calibration demand about the gated feedback.
   ------------------------------------------------------------------------------------ -/

/-- Ungated half: `w ≡ 1` is calibrated against the alternating bias (ratio → 0,
    by exact pairwise cancellation).  Instance of `pairClass_calibrated`. -/
theorem ungated_calibration :
    Tendsto (fun n => (∑ i ∈ Finset.range n, wOne i * bAlt i)
                    / (∑ i ∈ Finset.range n, wOne i)) atTop (𝓝 0) :=
  pairClass_calibrated wOne wOne_mem

/-- On every day the error-correlated gate fires, the bias is +1: pointwise,
    `cEven·wOne·bAlt = cEven·wOne`. -/
lemma cEven_absorbs_bAlt : ∀ i, cEven i * wOne i * bAlt i = cEven i * wOne i := by
  intro i
  rcases Nat.even_or_odd i with he | ho
  · obtain ⟨m, hm⟩ := he
    rw [← two_mul] at hm
    subst hm
    rw [bAlt_even m, mul_one]
  · obtain ⟨m, hm⟩ := ho
    subst hm
    rw [cEven_odd m]
    ring

/-- Partial gated mass: `∑_{i<2m} cEven i · wOne i = m`. -/
lemma cEven_mass (m : ℕ) : ∑ i ∈ Finset.range (2 * m), cEven i * wOne i = (m : ℝ) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih, cEven_even k, cEven_odd k]
    push_cast
    norm_num [wOne]

/-- Non-vacuity of the gate: the error-correlated gate keeps INFINITE weight —
    the breakage below is not the vacuous (silent) kind. -/
theorem gated_weight_diverges :
    Tendsto (fun n => ∑ i ∈ Finset.range n, cEven i * wOne i) atTop atTop := by
  have hmono : Monotone (fun n => ∑ i ∈ Finset.range n, cEven i * wOne i) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [Finset.sum_range_succ]
    have h0 : (0 : ℝ) ≤ cEven n * wOne n := by
      unfold cEven wOne
      split <;> norm_num
    linarith
  refine tendsto_atTop_atTop.2 fun b => ⟨2 * (⌈b⌉₊ + 1), fun k hk => ?_⟩
  calc b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    _ ≤ ((⌈b⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
    _ = ∑ i ∈ Finset.range (2 * (⌈b⌉₊ + 1)), cEven i * wOne i := (cEven_mass _).symm
    _ ≤ ∑ i ∈ Finset.range k, cEven i * wOne i := hmono hk

/-- **Theorem 2 (gating breaks calibration).**  The SAME weight and the SAME bias
    that are calibrated ungated (`ungated_calibration`) fail calibration after the
    error-correlated gate: the gated bias ratio is identically 1 from day 1 on,
    so it does not tend to 0.  An error-correlated "legitimacy" filter destroys a
    calibration that provably held ungated. -/
theorem gated_calibration_fails :
    ¬ Tendsto (fun n => (∑ i ∈ Finset.range n, cEven i * wOne i * bAlt i)
                      / (∑ i ∈ Finset.range n, cEven i * wOne i)) atTop (𝓝 0) := by
  intro h
  have hden1 : ∀ n, 1 ≤ n → (1 : ℝ) ≤ ∑ i ∈ Finset.range n, cEven i * wOne i := by
    intro n hn
    have h1 : (∑ i ∈ Finset.range 1, cEven i * wOne i) = 1 := by
      rw [Finset.sum_range_one]
      norm_num [cEven, wOne]
    calc (1 : ℝ) = ∑ i ∈ Finset.range 1, cEven i * wOne i := h1.symm
      _ ≤ ∑ i ∈ Finset.range n, cEven i * wOne i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp only [Finset.mem_range] at hx ⊢
            omega
          · intro i _ _
            unfold cEven wOne
            split <;> norm_num
  have hev : (fun n => (∑ i ∈ Finset.range n, cEven i * wOne i * bAlt i)
                     / (∑ i ∈ Finset.range n, cEven i * wOne i))
      =ᶠ[atTop] fun _ => (1 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Finset.sum_congr rfl (fun i _ => cEven_absorbs_bAlt i)]
    exact div_self (by linarith [hden1 n hn])
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := h.congr' hev
  have := tendsto_nhds_unique h1 tendsto_const_nhds
  norm_num at this

/-- **Corruption deletion test.**  Replace Theorem 2's gate by the trivial gate
    `c ≡ 1` (in the very same gated-statement shape): the compiled `Tendsto`
    RETURNS.  The gate object is load-bearing — delete the corruption and the
    breakage disappears. -/
theorem deletion_test :
    Tendsto (fun n => (∑ i ∈ Finset.range n, cOne i * wOne i * bAlt i)
                    / (∑ i ∈ Finset.range n, cOne i * wOne i)) atTop (𝓝 0) := by
  have h := ungated_calibration
  refine h.congr fun n => ?_
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by unfold cOne; ring)
  · exact Finset.sum_congr rfl (fun i _ => by unfold cOne; ring)

/- ------------------------------------------------------------------------------------
   §5  THE WEAKER-ANTECEDENT WITNESS (Theorem 1's strictness, compiled).

   Bias concentrated on odd days (bOdd), gate = cEven (keep even days).  The
   UNGATED calibration FAILS (the uniform ratio sits at 1/2 along even horizons),
   while the GATED calibration HOLDS (the gate never overlaps the bias; the gated
   ratio is identically 0 — and the gated weight still has infinite mass, by
   `gated_weight_diverges`).  So "calibration of the gated weight" is a strictly
   weaker assumption than "calibration of the raw weight": Theorem 1 applies where
   the ungated theorem cannot even be invoked.  Together with Theorem 2 (ungated
   holds, gated fails) the two witnesses show the two antecedents are INCOMPARABLE
   — gating is a genuine change of calibration class, in both directions.
   ------------------------------------------------------------------------------------ -/

lemma bOdd_even (m : ℕ) : bOdd (2 * m) = 0 := by
  simp [bOdd]

lemma bOdd_odd (m : ℕ) : bOdd (2 * m + 1) = 1 := by
  simp [bOdd]

lemma bOdd_sum (m : ℕ) : ∑ i ∈ Finset.range (2 * m), wOne i * bOdd i = (m : ℝ) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih, bOdd_even k, bOdd_odd k]
    push_cast
    norm_num [wOne]

/-- Ungated calibration FAILS for the odd-days bias: along even horizons the
    uniform bias ratio is exactly 1/2. -/
theorem weaker_antecedent_ungated_fails :
    ¬ Tendsto (fun n => (∑ i ∈ Finset.range n, wOne i * bOdd i)
                      / (∑ i ∈ Finset.range n, wOne i)) atTop (𝓝 0) := by
  intro h
  have htwo : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun n hn => by omega⟩
  have hcomp := h.comp htwo
  have hev : ((fun n => (∑ i ∈ Finset.range n, wOne i * bOdd i)
                      / (∑ i ∈ Finset.range n, wOne i)) ∘ fun m : ℕ => 2 * m)
      =ᶠ[atTop] fun _ => (1/2 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hden : ∑ i ∈ Finset.range (2 * m), wOne i = ((2 * m : ℕ) : ℝ) := by
      simp [wOne]
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    simp only [Function.comp_apply]
    rw [bOdd_sum m, hden]
    push_cast
    rw [mul_comm, div_mul_eq_div_div, div_self hm0]
  have h1 : Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (𝓝 0) := hcomp.congr' hev
  have := tendsto_nhds_unique h1 tendsto_const_nhds
  norm_num at this

/-- Gated calibration HOLDS for the same scenario: the gate never overlaps the
    bias, so the gated ratio is identically 0.  (And by `gated_weight_diverges`
    the gated weight keeps infinite mass — this is not vacuous silence.) -/
theorem weaker_antecedent_gated_holds :
    Tendsto (fun n => (∑ i ∈ Finset.range n, cEven i * wOne i * bOdd i)
                    / (∑ i ∈ Finset.range n, cEven i * wOne i)) atTop (𝓝 0) := by
  have hpt : ∀ i, cEven i * wOne i * bOdd i = 0 := by
    intro i
    rcases Nat.even_or_odd i with he | ho
    · obtain ⟨m, hm⟩ := he
      rw [← two_mul] at hm
      subst hm
      rw [bOdd_even m]
      ring
    · obtain ⟨m, hm⟩ := ho
      subst hm
      rw [cEven_odd m]
      ring
  have heq : ∀ n, (∑ i ∈ Finset.range n, cEven i * wOne i * bOdd i)
                / (∑ i ∈ Finset.range n, cEven i * wOne i) = 0 := by
    intro n
    rw [Finset.sum_eq_zero (fun i _ => hpt i), zero_div]
  exact tendsto_const_nhds.congr (fun n => (heq n).symm)

/- ------------------------------------------------------------------------------------
   §6  THE SILENCE COROLLARY (prose obligation (b)), compiled anchor.

   Quantifiers: for EVERY gate `c` of bounded total mass and EVERY `[0,1]` weight
   stream `w` — however violating — the gated conclusion `¬(∑ c·w → ∞)` holds
   unconditionally: no calibration, no criterion, no support hypotheses.  On days
   the gate sleeps, NOTHING is forced; a corrupted gate (≈0 exactly where the
   violations live) converts gated soft Total Trust into a tautology.  This is
   Theorem 2 met from the positive side: an error-correlated gate can kill the
   theorem's antecedent (Theorem 2) or hollow out its conclusion (here).
   ------------------------------------------------------------------------------------ -/

theorem gate_silence (c w : ℕ → ℝ) (M : ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (_hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hM : ∀ n, ∑ i ∈ Finset.range n, c i ≤ M) :
    ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, c i * w i) atTop atTop := by
  intro h
  obtain ⟨n, hn⟩ := (h.eventually_gt_atTop M).exists
  have hle : ∑ i ∈ Finset.range n, c i * w i ≤ ∑ i ∈ Finset.range n, c i :=
    Finset.sum_le_sum fun i _ => by
      calc c i * w i ≤ c i * 1 := mul_le_mul_of_nonneg_left (hw1 i) (hc0 i)
        _ = c i := mul_one _
  linarith [hM n]

end LegitGate

-- Axiom audit: each must rest on ONLY [propext, Classical.choice, Quot.sound] (no sorryAx).
-- Theorem-1 family
#print axioms LegitGate.pos_of_gated_pos
#print axioms LegitGate.gated_soft_total_trust
#print axioms LegitGate.gated_soft_total_trust_doublysoft
#print axioms LegitGate.gated_conclusion_from_ungated
#print axioms LegitGate.weaker_antecedent_ungated_fails
#print axioms LegitGate.weaker_antecedent_gated_holds
#print axioms LegitGate.gated_weight_diverges
-- Theorem-2 family
#print axioms LegitGate.ungated_calibration
#print axioms LegitGate.gated_calibration_fails
#print axioms LegitGate.deletion_test
#print axioms LegitGate.cEven_not_pairClass
-- Theorem-3 family
#print axioms LegitGate.pairClass_calibrated
#print axioms LegitGate.pairClass_mul
#print axioms LegitGate.cMix_mem
#print axioms LegitGate.cMix_nonconstant
#print axioms LegitGate.closure_gated_soft_total_trust
#print axioms LegitGate.pairClass_closure_instance
#print axioms LegitGate.gated_calibration_via_closure
-- Silence
#print axioms LegitGate.gate_silence
