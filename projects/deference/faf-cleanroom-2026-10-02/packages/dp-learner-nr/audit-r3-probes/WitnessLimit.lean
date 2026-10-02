import Cleanroom.Decision.DpLearnerNr.EstimatorWitness

/-!
# Audit r3 (adversarial) probe: the N+ witness's limit is `½`

`cell_mean_witness` is stated for every response table `F`; at the heads indicator the
conclusion reads "the heads frequency over the even rounds tends a.s. to `½`" — a limit that is
neither `0` nor `1`, so the witness exercises a genuine frequency statement, not a constant
sequence. Confirms the N+ grade (`coinSeq_coord_half` gives the mass; this gives the integral the
theorem's conclusion names). Not imported by the library.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace Cleanroom.Decision.DpLearnerNr

/-- The heads indicator as a response table (the policy coordinate is ignored). -/
def headsInd : Bool → Bool → ℝ := fun _ b => if b = true then 1 else 0

/-- `∫ headsInd true (ω 0) dcoinSeq = ½`. -/
theorem headsInd_integral : ∫ ω, headsInd true (ω 0) ∂coinSeq = 1 / 2 := by
  have hs : MeasurableSet {ω : ℕ → Bool | ω 0 = true} := by
    have hpre : {ω : ℕ → Bool | ω 0 = true} = (fun ω : ℕ → Bool => ω 0) ⁻¹' {true} := by
      ext ω; simp
    rw [hpre]
    exact measurable_pi_apply 0 (measurableSet_singleton true)
  have hfun : (fun ω : ℕ → Bool => headsInd true (ω 0))
      = Set.indicator {ω : ℕ → Bool | ω 0 = true} (1 : (ℕ → Bool) → ℝ) := by
    ext ω; simp [headsInd, Set.indicator]
  rw [hfun, integral_indicator_one hs, measureReal_def, coinSeq_coord_half, ENNReal.toReal_inv]
  norm_num

/-- **The probe**: a.s., the heads frequency over the even rounds tends to `½`. -/
theorem witness_heads_frequency :
    ∀ᵐ ω ∂coinSeq, Tendsto (fun T : ℕ =>
        (∑ t ∈ (range T).filter (fun t => decide (t % 2 = 0) = true), headsInd true (ω t))
          / (((range T).filter (fun t => decide (t % 2 = 0) = true)).card : ℝ))
      atTop (𝓝 (1 / 2)) := by
  have h := cell_mean_witness headsInd
  rw [headsInd_integral] at h
  exact h

end Cleanroom.Decision.DpLearnerNr
