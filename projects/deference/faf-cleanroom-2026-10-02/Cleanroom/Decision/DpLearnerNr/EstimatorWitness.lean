import Cleanroom.Decision.DpLearnerNr.Estimator
import Mathlib.Probability.Independence.InfinitePi

/-!
# `dp-learner-nr` target 14, the N+ witness

The hypothesis package of `cell_mean_converges` (pairwise-independent, identically distributed,
measurable exogenous draws; a deterministic policy sequence adopting `π₀` on an infinite set of
rounds) is inhabited *non-degenerately*: genuinely i.i.d. fair-coin draws `w t ω := ω t` on
`ℕ → Bool` under Mathlib's infinite product measure `Measure.infinitePi`, with the policy
`π t := (t even)` adopting `π₀ := true` on the even rounds. The coordinate `ω 0` is not almost
surely constant (`P(ω 0 = true) = ½`, `coinSeq_coord_half`), so this is an N+ witness, not the
Dirac one. Adopted from audit r2's `EstimatorWitness` probe (adversarial §3 item 1); the fair coin
is written out as `½·δ_true + ½·δ_false` rather than through Mathlib's `PMF.bernoulli` (deprecated
at this pin).
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace Cleanroom.Decision.DpLearnerNr

/-- The fair coin on `Bool`: `½·δ_true + ½·δ_false`.
Source: none: infrastructure (for `cell_mean_witness`)
Kind: D -/
noncomputable def fairCoin : Measure Bool :=
  (2⁻¹ : ENNReal) • Measure.dirac true + (2⁻¹ : ENNReal) • Measure.dirac false

instance : IsProbabilityMeasure fairCoin := by
  constructor
  simp [fairCoin, ENNReal.inv_two_add_inv_two]

/-- The i.i.d. sequence of fair coins: the infinite product of `fairCoin` over `ℕ`.
Source: none: infrastructure (for `cell_mean_witness`)
Kind: D -/
noncomputable def coinSeq : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => fairCoin)

instance : IsProbabilityMeasure coinSeq := by unfold coinSeq; infer_instance

/-- The coordinates of `coinSeq` are pairwise independent (from `iIndepFun_infinitePi`).
Source: none: infrastructure (for `cell_mean_witness`)
Kind: L -/
theorem coinSeq_coords_indep :
    Pairwise fun i j => IndepFun (fun ω : ℕ → Bool => ω i) (fun ω => ω j) coinSeq := by
  intro i j hij
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => fairCoin) (X := fun _ => (id : Bool → Bool))
    (fun _ => measurable_id)
  exact h.indepFun hij

/-- The coordinates of `coinSeq` are identically distributed (each is `fairCoin`).
Source: none: infrastructure (for `cell_mean_witness`)
Kind: L -/
theorem coinSeq_coords_ident (i : ℕ) :
    IdentDistrib (fun ω : ℕ → Bool => ω i) (fun ω => ω 0) coinSeq coinSeq :=
  ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable, by
    unfold coinSeq
    rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]⟩

/-- The even rounds are infinite.
Source: none: infrastructure (for `cell_mean_witness`)
Kind: L -/
theorem even_rounds_infinite : Set.Infinite {t : ℕ | decide (t % 2 = 0) = true} := by
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n) (fun a b h => by
    simpa using h) ?_
  intro n; simp

/-- **Non-degeneracy**: the first coordinate is heads with probability `½`, so the draws are not
almost surely constant.
Source: none: infrastructure (the N+ grade of `cell_mean_witness`)
Kind: L -/
theorem coinSeq_coord_half : coinSeq {ω | ω 0 = true} = 2⁻¹ := by
  have h : coinSeq {ω | ω 0 = true} = (coinSeq.map (fun ω : ℕ → Bool => ω 0)) {true} := by
    rw [Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton true)]
    rfl
  rw [h]
  unfold coinSeq
  rw [Measure.infinitePi_map_eval]
  simp [fairCoin]

/-- **N+ witness for `cell_mean_converges`** (target 14): the full hypothesis package is inhabited by
i.i.d. fair coins under `Measure.infinitePi` and the even-round policy, and the conclusion is the
theorem's, for every response table `F`. The variant disclosed on `cell_mean_converges` (the
per-round outcome is the deterministic `F π₀ (w t)`) is exercised exactly as disclosed.
Source: [[policy-level-fdt-learner]] §6 Conjecture F (i); [[dp-learner-nr-audit-r2-adversarial]]
§3 item 1 (probe `EstimatorWitness`); [[dp-learner-nr-mandate]] target 14
Kind: N+
Fidelity: n/a (witness)
Hyps: (a) none -/
theorem cell_mean_witness (F : Bool → Bool → ℝ) :
    ∀ᵐ ω ∂coinSeq, Tendsto (fun T : ℕ =>
        (∑ t ∈ (range T).filter (fun t => decide (t % 2 = 0) = true), F true (ω t))
          / (((range T).filter (fun t => decide (t % 2 = 0) = true)).card : ℝ))
      atTop (𝓝 (∫ ω, F true (ω 0) ∂coinSeq)) :=
  cell_mean_converges (μ := coinSeq) (fun t ω => ω t) (fun t => measurable_pi_apply t)
    coinSeq_coords_indep coinSeq_coords_ident (fun t => decide (t % 2 = 0)) true
    even_rounds_infinite F

end Cleanroom.Decision.DpLearnerNr
