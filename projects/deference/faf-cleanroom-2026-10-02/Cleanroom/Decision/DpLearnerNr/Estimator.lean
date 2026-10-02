/-
  `dp-learner-nr` target 14 (stretch): the estimator half of Conjecture F(i), proved over
  Mathlib's strong law on the subsequence of `π₀`-rounds.

  Kept in its own file (the only `MeasureTheory`-importing module of the package) so that its
  elaboration cost is isolated. Stated OPEN in the first session; proved at repair round 1
  (2026-10-01).
-/

import Mathlib.Probability.StrongLaw
import Mathlib.Data.Nat.Nth

open MeasureTheory ProbabilityTheory Filter Topology Finset Function

namespace Cleanroom.Decision.DpLearnerNr

/-- **Reindexing the `p`-rounds below `T` by `Nat.nth p`**: for `p` holding infinitely often,
`∑_{t < T, p t} f t = ∑_{k < count p T} f (nth p k)` (`nth p` is a bijection from
`{k < count p T}` onto `{t < T ∣ p t}`: `Nat.nth_lt_of_lt_count`, `Nat.nth_mem_of_infinite`,
`Nat.nth_injective`, `Nat.nth_count`, `Nat.count_strict_mono`).
Source: none: infrastructure (for target 14)
Kind: L -/
theorem sum_filter_eq_sum_nth {p : ℕ → Prop} [DecidablePred p] (hp : (setOf p).Infinite)
    (f : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ (range T).filter p, f t = ∑ k ∈ range (Nat.count p T), f (Nat.nth p k) := by
  symm
  refine Finset.sum_nbij (Nat.nth p) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.nth_lt_of_lt_count hk, Nat.nth_mem_of_infinite hp k⟩
  · exact (Nat.nth_injective hp).injOn
  · intro t ht
    rw [Finset.coe_filter] at ht
    obtain ⟨htT, hpt⟩ := ht
    rw [Finset.mem_range] at htT
    refine ⟨Nat.count p t, ?_, Nat.nth_count hpt⟩
    rw [Finset.coe_range, Set.mem_Iio]
    exact Nat.count_strict_mono hpt htT
  · intro k _
    rfl

/-- **`Nat.count p` tends to infinity** when `p` holds infinitely often (monotone, and
`count p (nth p b + 1) = b + 1`).
Source: none: infrastructure (for target 14)
Kind: L -/
theorem tendsto_count_atTop {p : ℕ → Prop} [DecidablePred p] (hp : (setOf p).Infinite) :
    Tendsto (Nat.count p) atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone (Nat.count_monotone p)
  intro b
  exact ⟨Nat.nth p b + 1, by rw [Nat.count_nth_succ_of_infinite hp]; omega⟩

/-- **Conjecture F(i), the estimator half** (target 14; stretch): for i.i.d. exogenous draws
`w_t ∼ P*` (pairwise independent, identically distributed, measurable), a *deterministic* policy
sequence `π` adopting `π₀` on an infinite set of rounds, and the cell mean `F π₀ w` as the
per-round payoff, the empirical mean of the payoff over the rounds `t < T` with `π t = π₀` tends
almost surely to `𝔼_{w ∼ P*}[F π₀ w]`. Proof: `ProbabilityTheory.strong_law_ae` (Etemadi's
pairwise-independent SLLN) applied to `X k := F π₀ ∘ w (nth p k)` on the subsequence
`nth p` of `p := (π · = π₀)` — independence transported by injectivity of `nth p`
(`IndepFun.comp`), identical distribution by `IdentDistrib.trans`/`.comp`, integrability by the
bound `∑_{w'} |F π₀ w'|` (`W` finite); then the empirical mean at horizon `T` is the SLLN average
at `n := count p T` (`sum_filter_eq_sum_nth`, `Nat.count_eq_card_filter_range`) and
`count p T → ∞` (`tendsto_count_atTop`), so the two sequences are a composition. The division is
the junk `0` only while no `π₀`-round has occurred (`count p T = 0`), which is finitely often and
irrelevant to the limit. This is the statement the mandate's target 14 wrote, and the "provable"
part of Conjecture F(i) in the pooled form below; it is never assumed elsewhere in the package as a
`∀ t` equality (`e1_static` carries it as an eventual-closeness hypothesis). N+ witness:
`cell_mean_witness` (`EstimatorWitness.lean`, i.i.d. fair coins under `Measure.infinitePi`).
Source: [[policy-level-fdt-learner]] §6 Conjecture F (i) ("provable: frequency convergence on
infinitely-visited cells"); [[dp-core-2-inventory]] 033(c); [[dp-core-inventory]] 111(i);
[[dp-learner-nr-mandate]] targets 7(c), 14
Kind: C
Fidelity: variant: (1) the per-round outcome is the deterministic cell mean `F π₀ (w t)` rather
than a draw from a law `F π₀ w`, so with the outcome deterministic given `w` the content is the
convergence of the empirical *exogenous* frequencies in the direction `F π₀` (the random-outcome
form follows by reading `W` as exogenous × outcome noise, not shipped); (2) the average is pooled
over `w` (the `π₀`-cell), where F(i) as printed is per `(π, w)`-cell (the per-cell form follows by
the indicator-ratio corollary — apply the theorem to `1[w = w₀]·F π₀ w` and to `1[w = w₀]` and
divide — not shipped); (3) the policy sequence is deterministic (independent of `w`)
Hyps: (a) Mathlib's i.i.d. package (pairwise `IndepFun`, `IdentDistrib`, measurability); (a)
`{t ∣ π t = π₀}` infinite -/
theorem cell_mean_converges {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {W : Type} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] {Pol : Type}
    (w : ℕ → Ω → W) (hmeas : ∀ t, Measurable (w t))
    (hindep : Pairwise fun i j => IndepFun (w i) (w j) μ)
    (hident : ∀ i, IdentDistrib (w i) (w 0) μ μ)
    (π : ℕ → Pol) (π₀ : Pol) [DecidablePred fun t => π t = π₀]
    (hinf : Set.Infinite {t | π t = π₀})
    (F : Pol → W → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun T : ℕ =>
        (∑ t ∈ (range T).filter (fun t => π t = π₀), F π₀ (w t ω))
          / (((range T).filter (fun t => π t = π₀)).card : ℝ))
      atTop (𝓝 (∫ ω, F π₀ (w 0 ω) ∂μ)) := by
  have hpinf : (setOf fun t => π t = π₀).Infinite := hinf
  have hF : Measurable (F π₀) := measurable_of_finite _
  -- the subsequence of exogenous draws at the `π₀`-rounds, pushed through the cell mean
  set X : ℕ → Ω → ℝ := fun k ω => F π₀ (w (Nat.nth (fun t => π t = π₀) k) ω) with hX
  have hXmeas : ∀ k, Measurable (X k) := fun k => hF.comp (hmeas _)
  have hint : Integrable (X 0) μ := by
    refine Integrable.of_bound (hXmeas 0).aestronglyMeasurable (∑ w', |F π₀ w'|) ?_
    refine Eventually.of_forall fun ω => ?_
    simp only [hX, Real.norm_eq_abs]
    exact Finset.single_le_sum (fun w' _ => abs_nonneg (F π₀ w')) (Finset.mem_univ _)
  have hindep' : Pairwise ((· ⟂ᵢ[μ] ·) on X) := by
    intro i j hij
    have hn : Nat.nth (fun t => π t = π₀) i ≠ Nat.nth (fun t => π t = π₀) j :=
      fun h => hij (Nat.nth_injective hpinf h)
    exact (hindep hn).comp hF hF
  have hident' : ∀ i, IdentDistrib (X i) (X 0) μ μ := fun i =>
    ((hident _).trans (hident _).symm).comp hF
  have hslln := strong_law_ae X hint hindep' hident'
  have hintegral : μ[X 0] = ∫ ω, F π₀ (w 0 ω) ∂μ := ((hident _).comp hF).integral_eq
  have hcount := tendsto_count_atTop hpinf
  filter_upwards [hslln] with ω hω
  rw [hintegral] at hω
  refine (hω.comp hcount).congr fun T => ?_
  simp only [Function.comp]
  rw [sum_filter_eq_sum_nth hpinf (fun t => F π₀ (w t ω)) T, ← Nat.count_eq_card_filter_range,
    smul_eq_mul, div_eq_inv_mul]

end Cleanroom.Decision.DpLearnerNr
