import Cleanroom.Corrigibility.CorrReflectFrames.Collapse
import Mathlib.Analysis.Convex.Combination

/-!
# corr-reflect-frames — T14: the expanded agent and the reflection identities

`Ω' = Ω × Θ`, `Ustar U (ω, θ) := U θ ω`. (a) When the joint factorizes, `P'(ω, θ) = P ω · μ θ`,
the expected expanded utility is the expected mixed utility `Ū := ∑_θ μ θ • U θ` under `P`, so
the best-action sets agree (`E_factorized_eq`, `sup'_factorized_eq`). (b) `Ū` lies in the convex
hull of the range of `U` iff it is a mixture `∑_θ μ θ • U θ` for a probability `μ` on `Θ`
(`mem_convexHull_range_iff_exists_mixture`): utility change within the hull is prior change.
(c) The martingale of `P'_t(θ)`: under Reflection, `∑_w π w · P_w(θ) = π θ`
(`point_martingale_of_reflects`, from stationarity). (d) is T10 (`Good.lean`).
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

/-- The expanded utility on `Ω × Θ`: `Ustar U (ω, θ) = U θ ω`.
Source: bli-soto-b-055; corr-core-003 (the expanded agent)
Kind: D
Fidelity: exact -/
def Ustar {Ω Θ : Type} (U : Θ → Ω → ℝ) : Ω × Θ → ℝ := fun x => U x.2 x.1

/-- The mixed utility `Ū := ∑_θ μ θ • U θ`.
Source: bli-soto-b-055; corr-core-003
Kind: D
Fidelity: exact -/
def mixU {Ω Θ : Type} [Fintype Θ] (μ : Θ → ℝ) (U : Θ → Ω → ℝ) : Ω → ℝ := ∑ θ, μ θ • U θ

/-- **Factorization identity (T14(a))**: if the joint is `P ω · μ θ`, the expected expanded
utility equals the expected mixed utility under `P`.
Source: bli-soto-b-055; corr-core-003, 006 (chat ll. 35–37); mandate T14(a)
Kind: L
Fidelity: exact
Hyps: (a) none (the factorization is the hypothesis, stated as the joint's form) -/
theorem E_factorized_eq {Ω Θ : Type} [Fintype Ω] [Fintype Θ] (P : Ω → ℝ) (μ : Θ → ℝ)
    (U : Θ → Ω → ℝ) :
    E (fun x : Ω × Θ => P x.1 * μ x.2) (Ustar U) = E P (mixU μ U) := by
  unfold E Ustar mixU
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro ω _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro θ _
  ring

/-- **The best-action values agree (T14(a))**: for a menu `a ↦ P a` of factorized joints
`P a ω · μ θ`, the best expected expanded utility equals the best expected mixed utility.
Source: bli-soto-b-055; mandate T14(a) ("the argmax sets agree")
Kind: L
Fidelity: exact (values of the maxima; equal values give equal maximizer sets)
Hyps: (a) none -/
theorem sup'_factorized_eq {Ω Θ A : Type} [Fintype Ω] [Fintype Θ] [Fintype A]
    (hA : (univ : Finset A).Nonempty) (P : A → Ω → ℝ) (μ : Θ → ℝ) (U : Θ → Ω → ℝ) :
    univ.sup' hA (fun a => E (fun x : Ω × Θ => P a x.1 * μ x.2) (Ustar U)) =
      univ.sup' hA (fun a => E (P a) (mixU μ U)) := by
  simp only [E_factorized_eq]

/-- **Utility change within the hull is prior change (T14(b))**: `Ū ∈ convexHull (range U)` iff
`Ū = ∑_θ μ θ • U θ` for some probability vector `μ` on `Θ`.
Source: bli-soto-b-055; corr-core-003; mandate T14(b)
Kind: D
Fidelity: exact (Mathlib's `mem_convexHull_iff_exists_fintype`, weights pushed forward to `Θ`)
Hyps: (a) none -/
theorem mem_convexHull_range_iff_exists_mixture {Ω Θ : Type} [Fintype Θ] (U : Θ → Ω → ℝ)
    (Ū : Ω → ℝ) :
    Ū ∈ convexHull ℝ (Set.range U) ↔
      ∃ μ : Θ → ℝ, (∀ θ, 0 ≤ μ θ) ∧ ∑ θ, μ θ = 1 ∧ Ū = ∑ θ, μ θ • U θ := by
  classical
  constructor
  · intro h
    obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.1 h
    choose θ hθ using fun i => Set.mem_range.1 (hz i)
    have hmaps : ∀ i ∈ (univ : Finset ι), θ i ∈ (univ : Finset Θ) := fun i _ => mem_univ _
    refine ⟨fun t => ∑ i ∈ univ.filter (fun i => θ i = t), w i, ?_, ?_, ?_⟩
    · intro t
      exact sum_nonneg (fun i _ => hw0 i)
    · rw [sum_fiberwise_of_maps_to hmaps]
      exact hw1
    · rw [← hsum]
      symm
      simp only [sum_smul]
      rw [← sum_fiberwise_of_maps_to hmaps (fun i => w i • z i)]
      apply sum_congr rfl
      intro t _
      apply sum_congr rfl
      intro i hi
      rw [← (mem_filter.1 hi).2, hθ i]
  · rintro ⟨μ, hμ0, hμ1, rfl⟩
    exact (convex_convexHull ℝ _).sum_mem (fun θ _ => hμ0 θ) hμ1
      (fun θ _ => subset_convexHull ℝ _ (Set.mem_range_self θ))

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **The martingale of `P'_t(θ)` (T14(c), corr-core-006)**: under Reflection,
`∑_w π w · P_w(θ) = π θ` — estimate matching at the point indicator, i.e. stationarity.
Source: corr-core-006; [[radical]] I3.3(a) l. 107; mandate T14(c)
Kind: L
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, Reflection -/
theorem point_martingale_of_reflects {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : Reflects π F) (θ : W) : ∑ w, π w * F.P w θ = π θ :=
  (estimateMatching_iff_stationary.1
    (estimateMatching_of_varReflects (varReflects_of_reflects hπ h))) θ

end

end Cleanroom.Corrigibility.CorrReflectFrames
