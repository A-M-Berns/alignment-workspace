import Cleanroom.Info.InfoVoiLatents.Voi
import ShannonInformation.API
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# info-voi-latents — the bridge to PFR's mutual information (Target 3(iv)–(v))

Carrier (ii) for the finite decision layer: the **joint measure** of a prior `μ ∈ stdSimplex ℝ W`
and an experiment `k : Experiment W S` on `W × S` (`joint μ k hμ`, a `PMF.toMeasure`), whose
point masses are `μ w · k w s`. Over it, PFR's `I[Prod.fst : Prod.snd ; joint μ k hμ]` is the
mutual information between state and signal, and

* `sum_klFin_eq_mutualInfo`: `∑ s, P(s) · klFin (post s) μ = I[Prod.fst : Prod.snd ; joint μ k hμ]`
  (null signals contribute `0` on both sides);
* `voi_le_mul_sqrt_mutualInfo`: **`voi μ k u ≤ M · √(I[Prod.fst : Prod.snd ; joint μ k hμ] / 2)`**,
  the last step of S2's chain, by Pinsker on each positive-mass posterior, Jensen for `√`, and
  the bridge.

The mutual information is PFR's `mutualInfo` (`I[X : Y ; μ] := H[X] + H[Y] − H[⟨X, Y⟩]`), never a
local finite sum; the finite sum is a *lemma about it*.

Mandate: `run/wp/info-voi-latents/info-voi-latents-mandate.md`, Target 3(iv)–(v).
-/

namespace Cleanroom.Info.InfoVoiLatents.Bridge

open MeasureTheory ProbabilityTheory Finset Real
open Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Info.InfoVoiLatents.Voi

noncomputable section

set_option linter.unusedSectionVars false

variable {W S : Type} [Fintype W] [Fintype S] [MeasurableSpace W] [MeasurableSpace S]
  [MeasurableSingletonClass W] [MeasurableSingletonClass S]

/-! ### The joint measure of `(μ, k)` -/

/-- The joint law of state and signal as a `PMF` on `W × S`: `(w, s) ↦ μ w · k w s`.
Source: none: infrastructure (Target 3(iv))
Kind: D
Fidelity: exact -/
def jointPMF (μ : W → ℝ) (k : Experiment W S) (hμ : μ ∈ stdSimplex ℝ W) : PMF (W × S) :=
  PMF.ofFintype (fun p => ENNReal.ofReal (μ p.1 * k.k p.1 p.2)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg (hμ.1 p.1) ((k.k_mem p.1).1 p.2)),
      Fintype.sum_prod_type]
    have : ∑ w, ∑ s, μ w * k.k w s = 1 := by
      calc ∑ w, ∑ s, μ w * k.k w s = ∑ w, μ w * ∑ s, k.k w s := by simp_rw [Finset.mul_sum]
        _ = ∑ w, μ w := Finset.sum_congr rfl fun w _ => by rw [(k.k_mem w).2, mul_one]
        _ = 1 := hμ.2
    rw [this, ENNReal.ofReal_one])

/-- **The joint measure** of a prior and an experiment on `W × S` (carrier (ii) for the finite
decision layer).
Source: none: infrastructure (Target 3(iv))
Kind: D
Fidelity: exact -/
def joint (μ : W → ℝ) (k : Experiment W S) (hμ : μ ∈ stdSimplex ℝ W) : Measure (W × S) :=
  (jointPMF μ k hμ).toMeasure

instance joint_isProbabilityMeasure (μ : W → ℝ) (k : Experiment W S) (hμ : μ ∈ stdSimplex ℝ W) :
    IsProbabilityMeasure (joint μ k hμ) := by
  unfold joint
  infer_instance

/-- Point masses of the joint measure.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem joint_real_singleton {μ : W → ℝ} (k : Experiment W S) (hμ : μ ∈ stdSimplex ℝ W)
    (p : W × S) : (joint μ k hμ).real {p} = μ p.1 * k.k p.1 p.2 := by
  rw [joint, measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p),
    jointPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (mul_nonneg (hμ.1 p.1) ((k.k_mem p.1).1 p.2))]

/-- The first marginal of the joint measure is the prior.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem joint_map_fst_real {μ : W → ℝ} (k : Experiment W S) (hμ : μ ∈ stdSimplex ℝ W) (w : W) :
    ((joint μ k hμ).map Prod.fst).real {w} = μ w := by
  rw [ShannonInformation.measureReal_map_fst_singleton, tsum_fintype]
  simp_rw [joint_real_singleton k hμ]
  rw [← Finset.mul_sum, (k.k_mem w).2, mul_one]

/-- The second marginal of the joint measure is the signal mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem joint_map_snd_real {μ : W → ℝ} (k : Experiment W S) (hμ : μ ∈ stdSimplex ℝ W) (s : S) :
    ((joint μ k hμ).map Prod.snd).real {s} = sigMass μ k s := by
  rw [ShannonInformation.measureReal_map_snd_singleton, tsum_fintype]
  simp_rw [joint_real_singleton k hμ]
  rfl

/-- `⟨Prod.fst, Prod.snd⟩` is the identity, so the law of the pair is the joint measure.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem joint_map_pair_real {μ : W → ℝ} (k : Experiment W S) (hμ : μ ∈ stdSimplex ℝ W)
    (p : W × S) :
    ((joint μ k hμ).map (⟨Prod.fst, Prod.snd⟩ : W × S → W × S)).real {p} = μ p.1 * k.k p.1 p.2 := by
  have : (⟨Prod.fst, Prod.snd⟩ : W × S → W × S) = id := funext fun p => rfl
  rw [this, Measure.map_id, joint_real_singleton k hμ]

/-- `H[Prod.fst ; joint] = ∑ w, negMulLog (μ w)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_fst_joint {μ : W → ℝ} (k : Experiment W S) (hμ : μ ∈ stdSimplex ℝ W) :
    H[Prod.fst ; joint μ k hμ] = ∑ w, negMulLog (μ w) := by
  rw [ProbabilityTheory.entropy_eq_sum, tsum_fintype]
  simp_rw [joint_map_fst_real k hμ]

/-- `H[Prod.snd ; joint] = ∑ s, negMulLog (P(s))`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_snd_joint {μ : W → ℝ} (k : Experiment W S) (hμ : μ ∈ stdSimplex ℝ W) :
    H[Prod.snd ; joint μ k hμ] = ∑ s, negMulLog (sigMass μ k s) := by
  rw [ProbabilityTheory.entropy_eq_sum, tsum_fintype]
  simp_rw [joint_map_snd_real k hμ]

/-- `H[⟨Prod.fst, Prod.snd⟩ ; joint] = ∑ (w, s), negMulLog (μ w · k w s)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_pair_joint {μ : W → ℝ} (k : Experiment W S) (hμ : μ ∈ stdSimplex ℝ W) :
    H[(⟨Prod.fst, Prod.snd⟩ : W × S → W × S) ; joint μ k hμ]
      = ∑ w, ∑ s, negMulLog (μ w * k.k w s) := by
  rw [ProbabilityTheory.entropy_eq_sum, tsum_fintype, Fintype.sum_prod_type]
  simp_rw [joint_map_pair_real k hμ]

/-! ### The bridge -/

/-- The per-coordinate log identity behind the bridge, junk-safe on null coordinates:
`P(s) · post_s(w) · log (post_s(w) / μ w) = −negMulLog J − J·log P(s) − J·log μ w` with
`J = μ w · k w s`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bridge_term {μ : W → ℝ} (k : Experiment W S) (hμ : μ ∈ stdSimplex ℝ W) (s : S) (w : W) :
    sigMass μ k s * (post μ k s w * Real.log (post μ k s w / μ w))
      = -negMulLog (μ w * k.k w s) - μ w * k.k w s * Real.log (sigMass μ k s)
        - μ w * k.k w s * Real.log (μ w) := by
  have hJ : sigMass μ k s * post μ k s w = μ w * k.k w s := by
    rw [mul_comm]
    exact post_mul_sigMass hμ k s w
  rw [← mul_assoc, hJ]
  rcases (mul_nonneg (hμ.1 w) ((k.k_mem w).1 s)).lt_or_eq with hpos | hzero
  · have hP : 0 < sigMass μ k s :=
      lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun w => μ w * k.k w s)
        (fun w _ => mul_nonneg (hμ.1 w) ((k.k_mem w).1 s)) (mem_univ w))
    have hμw : 0 < μ w := by
      rcases (hμ.1 w).lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at hpos
        exact absurd hpos (lt_irrefl 0)
    have hpost : post μ k s w = μ w * k.k w s / sigMass μ k s := rfl
    rw [hpost, Real.log_div (div_pos hpos hP).ne' hμw.ne', Real.log_div hpos.ne' hP.ne',
      negMulLog]
    ring
  · rw [← hzero]
    simp

/-- **The bridge**: the expected finite KL of the posteriors against the prior is PFR's mutual
information between state and signal on the joint measure,
`∑ s, P(s) · klFin (post s) μ = I[Prod.fst : Prod.snd ; joint μ k hμ]`. Null signals contribute
`0` on both sides (their posterior is the junk `0` vector and their `klFin` is `0`).
Source: [[generalization-final]] S2 l. 61, P2 l. 107 ("Pinsker then Jensen for √ give
`M√(½ I(ω_A; E))`"); Target 3(iv)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem sum_klFin_eq_mutualInfo {μ : W → ℝ} (k : Experiment W S) (hμ : μ ∈ stdSimplex ℝ W) :
    ∑ s, sigMass μ k s * klFin (post μ k s) μ = I[Prod.fst : Prod.snd ; joint μ k hμ] := by
  rw [mutualInfo_def, entropy_fst_joint k hμ, entropy_snd_joint k hμ, entropy_pair_joint k hμ]
  have h0 : ∑ s, ∑ w, negMulLog (μ w * k.k w s) = ∑ w, ∑ s, negMulLog (μ w * k.k w s) :=
    Finset.sum_comm
  have h1 : ∑ s, ∑ w, μ w * k.k w s * Real.log (sigMass μ k s)
      = ∑ s, sigMass μ k s * Real.log (sigMass μ k s) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_mul]
    rfl
  have h2 : ∑ s, ∑ w, μ w * k.k w s * Real.log (μ w) = ∑ w, μ w * Real.log (μ w) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, (k.k_mem w).2, mul_one]
  have h3 : ∑ s, sigMass μ k s * Real.log (sigMass μ k s) = -∑ s, negMulLog (sigMass μ k s) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun s _ => by simp [negMulLog]
  have h4 : ∑ w, μ w * Real.log (μ w) = -∑ w, negMulLog (μ w) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun w _ => by simp [negMulLog]
  calc ∑ s, sigMass μ k s * klFin (post μ k s) μ
      = ∑ s, ∑ w, (-negMulLog (μ w * k.k w s) - μ w * k.k w s * Real.log (sigMass μ k s)
          - μ w * k.k w s * Real.log (μ w)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        unfold klFin
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => bridge_term k hμ s w
    _ = -(∑ s, ∑ w, negMulLog (μ w * k.k w s)) - ∑ s, ∑ w, μ w * k.k w s * Real.log (sigMass μ k s)
          - ∑ s, ∑ w, μ w * k.k w s * Real.log (μ w) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    _ = ∑ w, negMulLog (μ w) + ∑ s, negMulLog (sigMass μ k s)
          - ∑ w, ∑ s, negMulLog (μ w * k.k w s) := by
        rw [h0, h1, h2, h3, h4]
        ring

/-! ### The last step of the chain -/

/-- `klFin (post s) μ ≥ 0` for every signal (null signals have the zero posterior and `klFin = 0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem klFin_post_nonneg {μ : W → ℝ} (k : Experiment W S) (hμ : μ ∈ stdSimplex ℝ W) (s : S) :
    0 ≤ klFin (post μ k s) μ := by
  rcases (sigMass_nonneg hμ k s).lt_or_eq with hs | hs
  · exact klFin_nonneg (post_mem_stdSimplex hμ k hs) hμ
      (fun w hw => by simp [post, hw])
  · simp [klFin, post, ← hs]

/-- **The VOI is bounded by `M √(I/2)`** over PFR's mutual information on the joint measure:
`voi μ k u ≤ M · √(I[Prod.fst : Prod.snd ; joint μ k hμ] / 2)` for a menu of within-action range
`M ≥ 0`. Chain: `voi_le_mul_sum_tv` (Lipschitz), `pinsker` on each positive-mass posterior,
`sum_mul_sqrt_le` (Jensen for `√`), `sum_klFin_eq_mutualInfo` (the bridge).
Source: [[generalization-final]] S2 l. 61 (the third inequality), P2 l. 107;
[[generalization-adversary]] A2.1 l. 34; items 126, 2-078
Kind: C
Fidelity: exact
Hyps: (a) all — `hμ` simplex, `hM` the within-action range, `hM0 : 0 ≤ M` (implied by `hM` at any
state, kept explicit) -/
theorem voi_le_mul_sqrt_mutualInfo [DecidableEq S] {μ : W → ℝ} (k : Experiment W S)
    (hμ : μ ∈ stdSimplex ℝ W) {n : ℕ} {u : Fin (n + 1) → W → ℝ} {M : ℝ}
    (hM : ∀ a w w', u a w - u a w' ≤ M) (hM0 : 0 ≤ M) :
    voi μ k u ≤ M * Real.sqrt (I[Prod.fst : Prod.snd ; joint μ k hμ] / 2) := by
  rw [← sum_klFin_eq_mutualInfo k hμ]
  refine le_trans (voi_le_mul_sum_tv hμ k hM) (mul_le_mul_of_nonneg_left ?_ hM0)
  have hx : ∀ s, 0 ≤ klFin (post μ k s) μ / 2 := fun s => by
    have := klFin_post_nonneg k hμ s
    positivity
  calc ∑ s, sigMass μ k s * tv (post μ k s) μ
      ≤ ∑ s, sigMass μ k s * Real.sqrt (klFin (post μ k s) μ / 2) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rcases (sigMass_nonneg hμ k s).lt_or_eq with hs | hs
        · refine mul_le_mul_of_nonneg_left ?_ hs.le
          exact pinsker (post_mem_stdSimplex hμ k hs) hμ (fun w hw => by simp [post, hw])
        · rw [← hs, zero_mul, zero_mul]
    _ ≤ Real.sqrt (∑ s, sigMass μ k s * (klFin (post μ k s) μ / 2)) :=
        sum_mul_sqrt_le ⟨sigMass_nonneg hμ k, sum_sigMass hμ k⟩ hx
    _ = Real.sqrt ((∑ s, sigMass μ k s * klFin (post μ k s) μ) / 2) := by
        rw [Finset.sum_div]
        congr 1
        exact Finset.sum_congr rfl fun s _ => by ring

end

end Cleanroom.Info.InfoVoiLatents.Bridge
