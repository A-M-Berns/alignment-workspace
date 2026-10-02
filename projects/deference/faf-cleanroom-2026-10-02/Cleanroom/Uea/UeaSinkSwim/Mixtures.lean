import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Observation 1 as an abstract mixture-dominance lemma

Model-free: for finite index types and non-negative weights, if `ψ = ∑ᵢ wᵢ μᵢ` with `μ_{i₀} = ζ`, and
`ζ = ∑ⱼ vⱼ νⱼ` with `ν_{j₀} = ψ` (pointwise on any type, all `μᵢ, νⱼ ≥ 0`), then `ψ ≥ w_{i₀} ζ` and
`ζ ≥ v_{j₀} ψ` pointwise. Fidelity `variant`: the rOSI statement (mixtures over oracle machines,
rO-computability) is not formalized; this captures "the difference is epistemic — an inductive bias";
mupi's dispute (dominance ≠ behavioural equivalence) is recorded, not adjudicated.

Namespace `Cleanroom.Uea.UeaSinkSwim.Mixtures` (faf-cleanroom run, `uea-sink-swim`, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Finset

namespace Mixtures

variable {I J X : Type*} [Fintype I] [Fintype J]

/-- **Observation 1 (abstract)**: mutual dominance of two mixtures that contain each other as components.
Source: [[uea-inventory]] 019 (Observation 1); [[sequential-self-game]] §7
Kind: L
Fidelity: variant: finite mixtures of non-negative functions on an arbitrary type in place of rOSI's mixtures over
oracle machines (disclosed)
Hyps: (a) -/
theorem mutual_dominance (w : I → ℝ) (v : J → ℝ) (μ : I → X → ℝ) (ν : J → X → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 ≤ v j) (hμ : ∀ i x, 0 ≤ μ i x) (hν : ∀ j x, 0 ≤ ν j x)
    (ψ ζ : X → ℝ) (hψ : ∀ x, ψ x = ∑ i, w i * μ i x) (hζ : ∀ x, ζ x = ∑ j, v j * ν j x)
    (i₀ : I) (j₀ : J) (hi : μ i₀ = ζ) (hj : ν j₀ = ψ) :
    (∀ x, w i₀ * ζ x ≤ ψ x) ∧ (∀ x, v j₀ * ψ x ≤ ζ x) := by
  constructor
  · intro x
    rw [hψ x, ← hi]
    exact single_le_sum (fun i _ => mul_nonneg (hw i) (hμ i x)) (mem_univ i₀)
  · intro x
    rw [hζ x, ← hj]
    exact single_le_sum (fun j _ => mul_nonneg (hv j) (hν j x)) (mem_univ j₀)

/-- The two dominance constants compose: `ψ ≥ w_{i₀} v_{j₀} ψ`, so `w_{i₀} v_{j₀} ≤ 1` wherever `ψ > 0` — the two
priors cannot both put most of their mass on each other.
Source: [[uea-inventory]] 019 (consequence)
Kind: L
Fidelity: variant (as above)
Hyps: (a) -/
theorem dominance_product_le_one (w : I → ℝ) (v : J → ℝ) (μ : I → X → ℝ) (ν : J → X → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 ≤ v j) (hμ : ∀ i x, 0 ≤ μ i x) (hν : ∀ j x, 0 ≤ ν j x)
    (ψ ζ : X → ℝ) (hψ : ∀ x, ψ x = ∑ i, w i * μ i x) (hζ : ∀ x, ζ x = ∑ j, v j * ν j x)
    (i₀ : I) (j₀ : J) (hi : μ i₀ = ζ) (hj : ν j₀ = ψ) (x : X) (hx : 0 < ψ x) :
    w i₀ * v j₀ ≤ 1 := by
  obtain ⟨h1, h2⟩ := mutual_dominance w v μ ν hw hv hμ hν ψ ζ hψ hζ i₀ j₀ hi hj
  have hw0 := hw i₀
  have h3 : w i₀ * (v j₀ * ψ x) ≤ w i₀ * ζ x := mul_le_mul_of_nonneg_left (h2 x) hw0
  have h4 : (w i₀ * v j₀) * ψ x ≤ 1 * ψ x := by rw [mul_assoc, one_mul]; linarith [h1 x]
  exact le_of_mul_le_mul_right h4 hx

end Mixtures

end Cleanroom.Uea.UeaSinkSwim
