/-
  Kernel-checked core of the DESTINATION-AUDIT theorem
  (`dose-response.md` §7: Theorem T3, with Lemma 4.4 as the engine).

  Discipline (identical to the `lean-deference` corpus): the genuine
  arithmetic/asymptotic cores are PROVED outright; Logical-Induction facts enter
  ONLY as named hypotheses.  In this module the sole LI input is *Expectations
  Converge* [LI 4.8.3] — "destinations exist" — carried as the convergence
  hypotheses `hi`/`hj` of each audit theorem.  Everything else is real analysis.
  No `sorry`; axiom audit at the end.

  The setup (D4 of the note): the auditor holds per-arm expectation streams and
  forms weighted averages of the cross-arm gap.
    auditStat w r n = (Σ_{i<n} w i · r i) / (Σ_{i<n} w i)   the D4 audit statistic
    cesaroGap Ei Ej n = (Σ_{i<n} (Ei i − Ej i)) / n          the uniform statistic G^{ij}

  Map to the note:
    weighted_null_average   Lemma 4.4: null gap ⇒ every divergent-weighting audit passes
    finite_prefix_washout   Lemma 4.4's consequence: prefix-supported r contributes 0
    cesaro_of_tendsto       the Cesàro engine of T3(ii) (and later T2(d))
    audit_sound             T3(i): equal destinations ⇒ every battery passes (no false alarms)
    audit_complete          T3(ii): distinct destinations ⇒ the uniform statistic converges
                            to the gap, hence fires — detection exact and permanent
    audit_exact             the headline iff: pass ⇔ destinations agree
    decided_content_auto_passes  Corollary T3.5, with [LI 4.8.10] as the named hypotheses
-/
import Mathlib

open Filter Topology

namespace DoseAudit

/-- D4's audit statistic: the `w`-weighted running average of the per-day record `r`. -/
noncomputable def auditStat (w r : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, w i * r i) / (∑ i ∈ Finset.range n, w i)

/-- The uniform Cesàro gap statistic `G^{ij}` of D4. -/
noncomputable def cesaroGap (Ei Ej : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, (Ei i - Ej i)) / n

/-- **Lemma 4.4 (weighted null averages).**  If the per-day record `r` is null and `w` is
    any divergent weighting, the audit statistic vanishes.  The proof is the classical
    split: a fixed prefix (washed out by `W → ∞`) plus a tail where `|r| < ε/4`. -/
theorem weighted_null_average (w r : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hW : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop)
    (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (auditStat w r) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hr (ε / 4) (by linarith)
  set C : ℝ := |∑ i ∈ Finset.range N, w i * r i| with hCdef
  have hC : 0 ≤ C := abs_nonneg _
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hW.eventually_ge_atTop (max (4 * C / ε) 1))
  refine ⟨max M N, fun n hn => ?_⟩
  have hMn : M ≤ n := le_trans (le_max_left _ _) hn
  have hNn : N ≤ n := le_trans (le_max_right _ _) hn
  set W : ℝ := ∑ i ∈ Finset.range n, w i with hWdef
  have hWge : max (4 * C / ε) 1 ≤ W := hM n hMn
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_right _ _) hWge
  have hWpos : (0 : ℝ) < W := lt_of_lt_of_le one_pos hW1
  -- split the numerator at N
  have hsplit : (∑ i ∈ Finset.range n, w i * r i)
      = (∑ i ∈ Finset.range N, w i * r i) + ∑ i ∈ Finset.Ico N n, w i * r i :=
    (Finset.sum_range_add_sum_Ico _ hNn).symm
  -- tail estimate: |Σ_{[N,n)} w r| ≤ (ε/4) W
  have htail : |∑ i ∈ Finset.Ico N n, w i * r i| ≤ ε / 4 * W := by
    calc |∑ i ∈ Finset.Ico N n, w i * r i|
        ≤ ∑ i ∈ Finset.Ico N n, |w i * r i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ico N n, w i * (ε / 4) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hiN : N ≤ i := (Finset.mem_Ico.1 hi).1
          have := hN i hiN
          rw [Real.dist_eq, sub_zero] at this
          rw [abs_mul, abs_of_nonneg (hw i)]
          exact mul_le_mul_of_nonneg_left (le_of_lt this) (hw i)
      _ = (∑ i ∈ Finset.Ico N n, w i) * (ε / 4) := by rw [Finset.sum_mul]
      _ ≤ W * (ε / 4) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          rw [hWdef, ← Finset.sum_range_add_sum_Ico w hNn]
          have : 0 ≤ ∑ i ∈ Finset.range N, w i :=
            Finset.sum_nonneg fun i _ => hw i
          linarith
      _ = ε / 4 * W := mul_comm _ _
  -- prefix constant is dominated: C ≤ (ε/4) W
  have hpre : C ≤ ε / 4 * W := by
    have h4 : 4 * C / ε ≤ W := le_trans (le_max_left _ _) hWge
    rw [div_le_iff₀ hε] at h4
    linarith
  -- assemble
  have hnum : |∑ i ∈ Finset.range n, w i * r i| ≤ ε / 2 * W := by
    rw [hsplit]
    calc |(∑ i ∈ Finset.range N, w i * r i) + ∑ i ∈ Finset.Ico N n, w i * r i|
        ≤ C + |∑ i ∈ Finset.Ico N n, w i * r i| := abs_add_le _ _
      _ ≤ ε / 4 * W + ε / 4 * W := add_le_add hpre htail
      _ = ε / 2 * W := by ring
  have hstat : auditStat w r n = (∑ i ∈ Finset.range n, w i * r i) / W := by
    simp only [auditStat]
    rw [← hWdef]
  have hlt : ε / 2 * W < ε * W :=
    mul_lt_mul_of_pos_right (half_lt_self hε) hWpos
  rw [Real.dist_eq, sub_zero, hstat, abs_div, abs_of_pos hWpos, div_lt_iff₀ hWpos]
  linarith

/-- **Lemma 4.4, displayed consequence.**  A record supported on a finite prefix
    contributes `0` to every divergent-weighting audit: calibration audits are memoryless
    (the engine of Corollary T2.1's "transient trace"). -/
theorem finite_prefix_washout (w r : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hW : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop)
    (hr : ∀ᶠ i in atTop, r i = 0) :
    Tendsto (auditStat w r) atTop (𝓝 0) :=
  weighted_null_average w r hw hW (tendsto_nhds_of_eventually_eq hr)

/-- The uniform weighting is a divergent weighting (non-vacuity of the `w ≡ 1` instance,
    and the bridge from `auditStat 1` to `cesaroGap`). -/
theorem uniform_divergent :
    Tendsto (fun n => ∑ _i ∈ Finset.range n, (1 : ℝ)) atTop atTop := by
  simpa using tendsto_natCast_atTop_atTop (R := ℝ)

/-- **The Cesàro engine** (T3(ii), and T2(d) downstream): a convergent sequence's running
    average converges to the same limit.  Derived from Lemma 4.4 at the uniform weighting. -/
theorem cesaro_of_tendsto (x : ℕ → ℝ) (L : ℝ) (hx : Tendsto x atTop (𝓝 L)) :
    Tendsto (fun n => (∑ i ∈ Finset.range n, x i) / n) atTop (𝓝 L) := by
  have hnull : Tendsto (fun i => x i - L) atTop (𝓝 0) := by
    simpa using hx.sub_const L
  have h := weighted_null_average (fun _ => 1) (fun i => x i - L)
    (fun _ => zero_le_one) uniform_divergent hnull
  have heq : ∀ᶠ n : ℕ in atTop,
      auditStat (fun _ => 1) (fun i => x i - L) n
        = (∑ i ∈ Finset.range n, x i) / n - L := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [auditStat, one_mul, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    rw [sub_div, mul_div_cancel_left₀ _ hn']
  have h2 : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, x i) / n - L)
      atTop (𝓝 0) := h.congr' heq
  exact tendsto_sub_nhds_zero_iff.1 h2

/-- **T3(i) — Soundness, for every battery.**  If the two arms' destinations agree
    (their expectation streams converge to a common limit — existence of the limits is
    [LI 4.8.3], the named hypothesis), then for *every* divergent weighting the cross-arm
    audit passes.  Enlarging the battery never creates false alarms. -/
theorem audit_sound (Ei Ej : ℕ → ℝ) (L : ℝ)
    (hi : Tendsto Ei atTop (𝓝 L)) (hj : Tendsto Ej atTop (𝓝 L))
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hW : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) :
    Tendsto (auditStat w (fun n => Ei n - Ej n)) atTop (𝓝 0) := by
  refine weighted_null_average w _ hw hW ?_
  simpa using hi.sub hj

/-- **T3(ii) — Completeness, from the uniform weighting alone.**  If the destinations
    differ, the uniform Cesàro statistic converges to the (nonzero) destination gap:
    detection is exact and permanent, with no battery needed. -/
theorem audit_complete (Ei Ej : ℕ → ℝ) (Li Lj : ℝ)
    (hi : Tendsto Ei atTop (𝓝 Li)) (hj : Tendsto Ej atTop (𝓝 Lj)) :
    Tendsto (cesaroGap Ei Ej) atTop (𝓝 (Li - Lj)) := by
  have : Tendsto (fun n => Ei n - Ej n) atTop (𝓝 (Li - Lj)) := hi.sub hj
  exact cesaro_of_tendsto _ _ this

/-- **T3, headline form.**  Dose-invariance of destinations is *exactly* the event that
    the uniform Cesàro audit passes: given that both destinations exist ([LI 4.8.3]),
    `G^{ij} → 0` iff the destinations are equal. -/
theorem audit_exact (Ei Ej : ℕ → ℝ) (Li Lj : ℝ)
    (hi : Tendsto Ei atTop (𝓝 Li)) (hj : Tendsto Ej atTop (𝓝 Lj)) :
    Tendsto (cesaroGap Ei Ej) atTop (𝓝 0) ↔ Li = Lj := by
  constructor
  · intro hpass
    have hfire := audit_complete Ei Ej Li Lj hi hj
    have := tendsto_nhds_unique hpass hfire
    linarith [this]
  · intro hLL
    subst hLL
    have h0 : Tendsto (fun n => Ei n - Ej n) atTop (𝓝 0) := by simpa using hi.sub hj
    exact cesaro_of_tendsto (fun n => Ei n - Ej n) 0 h0

/-- **Corollary T3.5 (decided content auto-passes).**  If `X` is decided by the shared
    base deductive process, [LI 4.8.10] (the named hypotheses `hi`, `hj`: both arms'
    expectations converge to the decided value `val`) makes every cross-arm audit on `X`
    pass — for any inductors and any quote policy.  Misfiling a decidable into the
    protected class is harmless. -/
theorem decided_content_auto_passes (Ei Ej : ℕ → ℝ) (val : ℝ)
    (hi : Tendsto Ei atTop (𝓝 val)) (hj : Tendsto Ej atTop (𝓝 val)) :
    Tendsto (cesaroGap Ei Ej) atTop (𝓝 0) :=
  (audit_exact Ei Ej val val hi hj).2 rfl

/-- Non-vacuity of completeness, non-degenerate: two genuinely time-varying streams
    (the T2(a)/(d)-shaped destinations `½ + s·p̂`, approached at rate `1/(n+1)` from
    opposite sides), on which the uniform statistic really does converge to the
    nonzero gap.  Unlike a constant-stream witness, this exercises the Cesàro
    content: the gap sequence moves on every day. -/
theorem audit_complete_nonvacuous (s pi pj : ℝ) (hs : s ≠ 0) (hp : pi ≠ pj) :
    Tendsto (cesaroGap (fun n => 1/2 + s * pi + 1/(n+1))
        (fun n => 1/2 + s * pj - 1/(n+1))) atTop
      (𝓝 (s * (pi - pj))) ∧ s * (pi - pj) ≠ 0 := by
  have hlim : Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  constructor
  · have hi : Tendsto (fun n : ℕ => 1/2 + s * pi + 1/((n : ℝ)+1)) atTop
        (𝓝 (1/2 + s * pi)) := by
      simpa using tendsto_const_nhds.add hlim
    have hj : Tendsto (fun n : ℕ => 1/2 + s * pj - 1/((n : ℝ)+1)) atTop
        (𝓝 (1/2 + s * pj)) := by
      simpa using tendsto_const_nhds.sub hlim
    have := audit_complete _ _ _ _ hi hj
    convert this using 2
    ring
  · exact mul_ne_zero hs (sub_ne_zero.2 hp)

end DoseAudit

-- Axiom audit: each must rest on ONLY [propext, Classical.choice, Quot.sound] (no `sorryAx`).
#print axioms DoseAudit.weighted_null_average
#print axioms DoseAudit.finite_prefix_washout
#print axioms DoseAudit.cesaro_of_tendsto
#print axioms DoseAudit.audit_sound
#print axioms DoseAudit.audit_complete
#print axioms DoseAudit.audit_exact
#print axioms DoseAudit.decided_content_auto_passes
#print axioms DoseAudit.audit_complete_nonvacuous
