import Cleanroom.Info.InfoVoiLatents.NaturalLatents
import Cleanroom.Info.InfoVoiLatents.Finite
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# info-voi-latents — open statements

Precise statements this package did not prove, each listed in
`run/wp/info-voi-latents/info-voi-latents-open.txt` with its reason. They are conjectures or
published theorems taken as stated, never hypotheses of anything proved here.

* `natural_latents_approx` (Target 10(iii)): the approximate (KL) version of Wentworth's simplified
  Fundamental Theorem with coefficient `1` on the third diagram's `ε₃`. The same bound with `2ε₃`
  is **proved** (`NaturalLatentsStochastic.natural_latents_approx_two_eps₃`), as is the exact
  stochastic theorem that was Target 10(ii) (`natural_latents_stochastic`, formerly listed here;
  closed in repair round 2, audit r2 adversarial item 2).
* `entropy_continuity` (Target 6(iv)): the Fannes–Audenaert continuity bound for the finite entropy
  in total variation, a published theorem (Audenaert 2007; Zhang 2007) FAF lacks.
-/

namespace Cleanroom.Info.InfoVoiLatents.Open

open MeasureTheory ProbabilityTheory ShannonInformation Finset Real
open Cleanroom.Info.InfoVoiLatents.Shannon

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω S₁ S₂ L L' : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace S₁] [MeasurableSpace S₂] [MeasurableSpace L] [MeasurableSpace L']
  [Countable S₁] [Countable S₂] [Countable L] [Countable L']
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂] [MeasurableSingletonClass L]
  [MeasurableSingletonClass L']
  {X₁ : Ω → S₁} {X₂ : Ω → S₂} {Λ : Ω → L} {Λ' : Ω → L'}

/-- **OPEN — Target 10(iii), the approximate version with coefficient `1` on `ε₃`**: if the four
diagrams hold up to `ε₁, ε₂, ε₂', ε₃` in conditional mutual information, then
`I[Λ' : X | Λ] ≤ ε₁ + ε₂ + ε₂' + ε₃`. What *is* proved is the same bound with `2ε₃`
(`NaturalLatentsStochastic.natural_latents_approx_two_eps₃`, from chain rules alone — the third
diagram is used once in each half of the proof) and this constant when the third diagram is exact
(`natural_latents_approx_of_third`). Whether the coefficient of `ε₃` can be `1` is the open part;
the post's own bound is an image not readable here, so its constant is unknown. The statement is
recorded as the shape of the extension, not as a claim.
Source: [[wentworth-2023-natural-latents-the-math]] ll. 81–85 ("Approximation"); the plan's named
first-new Condensation theorem; audit r2 (adversarial item 2)
Kind: OPEN
Fidelity: variant: conjectural constant (the `2ε₃` form is a theorem)
Hyps: (b)/(c) the post's approximation claim with an unverified constant -/
theorem natural_latents_approx (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hΛ : Measurable Λ) (hΛ' : Measurable Λ') [FiniteEntropyOf X₁ μ] [FiniteEntropyOf X₂ μ]
    [FiniteEntropyOf Λ μ] [FiniteEntropyOf Λ' μ] {ε₁ ε₂ ε₂' ε₃ : ℝ}
    (h₁ : I[X₁ : X₂ | Λ ; μ] ≤ ε₁) (h₂ : I[Λ' : X₁ | X₂ ; μ] ≤ ε₂) (h₂' : I[Λ' : X₂ | X₁ ; μ] ≤ ε₂')
    (h₃ : I[Λ : Λ' | (⟨X₁, X₂⟩ : Ω → S₁ × S₂) ; μ] ≤ ε₃) :
    I[Λ' : (⟨X₁, X₂⟩ : Ω → S₁ × S₂) | Λ ; μ] ≤ ε₁ + ε₂ + ε₂' + ε₃ := by
  sorry

/-- **OPEN — Target 6(iv), the Fannes–Audenaert continuity bound** for the finite Shannon entropy
`∑ negMulLog` in total variation: `|H(p) − H(q)| ≤ tv·log(|W| − 1) + h₂(tv)` for `|W| ≥ 2`. A
published theorem (Audenaert 2007, classical case; Zhang 2007) that FAF and Mathlib lack; the
adversary reports it from memory (A5.3).
Source: [[generalization-adversary]] A5.3 l. 59; [[generalization-final]] S5(ii) l. 73 (the
`ln|supp|` factor)
Kind: OPEN
Fidelity: exact
Hyps: (b) Audenaert 2007, Theorem 1 (classical specialisation) -/
theorem entropy_continuity {W : Type} [Fintype W] {p q : W → ℝ} (hp : p ∈ stdSimplex ℝ W)
    (hq : q ∈ stdSimplex ℝ W) (hW : 2 ≤ Fintype.card W) :
    |∑ w, negMulLog (p w) - ∑ w, negMulLog (q w)|
      ≤ tv p q * Real.log (Fintype.card W - 1) + Real.binEntropy (tv p q) := by
  sorry

end

end Cleanroom.Info.InfoVoiLatents.Open
