import Condensation.Probability
import Condensation.Model
import Cleanroom.Info.InfoVoiLatents.Shannon

/-!
# info-voi-latents — natural latents, the exact two-variable theorem over Condensation (Target 10)

Ambient: a countable discrete probability space `(Ω, μ)` (Condensation's), variables `X₁ X₂ Λ Λ'`
measurable into countable discrete types with `ShannonInformation.FiniteEntropyOf` each.

* `Mediates Λ X₁ X₂ μ := CondIndepFun X₁ X₂ Λ μ` (the post's first diagram).
* `DetRedundant X₁ X₂ Λ' μ := AEFunctionOf X₁ Λ' μ ∧ AEFunctionOf X₂ Λ' μ` (the post's second pair
  of diagrams in the *deterministic* reading: `Λ'` is a.e. a function of each chunk alone —
  the gas example).
* **`aeFunctionOf_of_mediates_detRedundant`**: mediation + deterministic redundancy ⇒
  `Condensation.AEFunctionOf Λ Λ' μ` (`Λ'` is a.e. a function of `Λ`, the post's own reading of the
  conclusion), and **`condMutualInfo_latent_eq_zero`**: `I[Λ' : ⟨X₁, X₂⟩ | Λ ; μ] = 0` ("`Λ` mediates
  between `Λ'` and `X`"). Route: `Λ' = f ∘ X₁ = g ∘ X₂` a.e., conditional data processing
  (`Shannon.condMutualInfo_comp_comp_le`) gives `I[Λ' : Λ' | Λ] ≤ I[X₁ : X₂ | Λ] = 0`, `I[Λ' : Λ' | Λ] =
  H[Λ' | Λ]` (`Shannon.condMutualInfo_self`), Condensation's Proposition 2.5
  (`aeFunctionOf_of_condEntropy_eq_zero`). **The third diagram is not used** (findings F5).
* `RVModel` form: `rvModel_aeFunctionOf` on `Condensation.RVModel (Fin 2)`.
* Witness N+ (`NaturalLatentsWitnessFour.lean`): four uniform bits, `X₁ = (b, n₁)`, `X₂ = (b, n₂)`,
  `Λ = (b, d)`, `Λ' = b` — mediation a genuine computation, `Λ` a function of neither chunk, the
  conclusion not among the hypotheses. The three-bit `Λ = X₁` instance (`NaturalLatentsWitness.lean`)
  is N−: there the conclusion is the first redundancy hypothesis (audit r1).

Stochastic redundancy (ii) is **proved** in `NaturalLatentsStochastic.lean`
(`natural_latents_stochastic`, repair round 2, from the package's chain rules), which also proves
the approximate version (iii) with the constant `ε₁ + ε₂ + ε₂' + 2ε₃` and reduces this file's
deterministic form to a special case of the stochastic one. Whether the coefficient of `ε₃` can be
`1` is `Open.natural_latents_approx`. Mandate: Target 10.
-/

namespace Cleanroom.Info.InfoVoiLatents.NaturalLatents

open MeasureTheory ProbabilityTheory ShannonInformation
open Cleanroom.Info.InfoVoiLatents.Shannon
open _root_.Condensation

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω S₁ S₂ L L' : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace S₁] [MeasurableSpace S₂] [MeasurableSpace L] [MeasurableSpace L']
  [Countable S₁] [Countable S₂] [Countable L] [Countable L']
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂] [MeasurableSingletonClass L]
  [MeasurableSingletonClass L']
  {X₁ : Ω → S₁} {X₂ : Ω → S₂} {Λ : Ω → L} {Λ' : Ω → L'}

/-- **Mediation**: `Λ` induces independence between `X₁` and `X₂` (Mathlib/PFR `CondIndepFun`, the
conditioning variable last).
Source: [[wentworth-2023-natural-latents-the-math]] l. 31 (first diagram); [[generalization-final]]
D9 l. 43
Kind: D
Fidelity: exact -/
def Mediates (Λ : Ω → L) (X₁ : Ω → S₁) (X₂ : Ω → S₂) (μ : Measure Ω) : Prop :=
  CondIndepFun X₁ X₂ Λ μ

/-- **Deterministic redundancy**: `Λ'` is a.e. a function of `X₁` alone and of `X₂` alone (the
post's "the temperature can be read off either chunk", ll. 33–35, 67).
Source: [[wentworth-2023-natural-latents-the-math]] ll. 33–35, 67; [[generalization-final]] D9 l. 43
("the candidate's value can be backed out from any individual part")
Kind: D
Fidelity: variant: the deterministic reading of the second pair of diagrams (the post's
Fundamental Theorem proper uses stochastic redundancy; findings F5) -/
def DetRedundant (X₁ : Ω → S₁) (X₂ : Ω → S₂) (Λ' : Ω → L') (μ : Measure Ω) : Prop :=
  AEFunctionOf X₁ Λ' μ ∧ AEFunctionOf X₂ Λ' μ

/-- **The exact two-variable fundamental theorem, deterministic form**: mediation and deterministic
redundancy force `Λ'` to be a.e. a function of `Λ` (`Condensation.AEFunctionOf Λ Λ' μ`, argument order
"`Λ'` is a function of `Λ`"). The post's third diagram (`X` mediates `Λ, Λ'`) is not used.
Source: [[wentworth-2023-natural-latents-the-math]] ll. 27–47 ("claim: `Λ` mediates between `Λ'`
and `X`"), l. 67 ("`Λ'` is a function of `Λ`"); item 075
Kind: P
Fidelity: weaker: special case of the post's theorem — deterministic redundancy (`Λ'` a.e. a
function of each chunk, the gas example) implies the post's stochastic redundancy and its third
diagram (`NaturalLatentsStochastic.lean`: `stochRedundant_of_detRedundant`,
`thirdDiagram_of_detRedundant`), and the conclusion is the post's own l. 67 wording; the general
stochastic form is `natural_latents_stochastic` (repair round 2)
Hyps: (a) all — `hmed`, `hred` are the claim's own antecedents; measurability and finite entropy
are the ambient -/
theorem aeFunctionOf_of_mediates_detRedundant (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hΛ : Measurable Λ) (hΛ' : Measurable Λ') [FiniteEntropyOf X₁ μ] [FiniteEntropyOf X₂ μ]
    [FiniteEntropyOf Λ μ] [FiniteEntropyOf Λ' μ] (hmed : Mediates Λ X₁ X₂ μ)
    (hred : DetRedundant X₁ X₂ Λ' μ) : AEFunctionOf Λ Λ' μ := by
  obtain ⟨⟨f, hf, hfae⟩, ⟨g, hg, hgae⟩⟩ := hred
  have h1 : Λ' =ᵐ[μ] f ∘ X₁ := hfae
  have h2 : Λ' =ᵐ[μ] g ∘ X₂ := hgae
  have hI : I[X₁ : X₂ | Λ ; μ] = 0 :=
    (ShannonInformation.condMutualInfo_eq_zero hX₁ hX₂ hΛ).2 hmed
  have hle : I[f ∘ X₁ : g ∘ X₂ | Λ ; μ] ≤ I[X₁ : X₂ | Λ ; μ] :=
    condMutualInfo_comp_comp_le hX₁ hX₂ hΛ f g
  have hcongr : I[Λ' : Λ' | Λ ; μ] = I[f ∘ X₁ : g ∘ X₂ | Λ ; μ] := by
    rw [condMutualInfo_congr_left h1,
      condMutualInfo_congr_right (hf.comp hX₁) hΛ' (hg.comp hX₂) h2]
  have hself : I[Λ' : Λ' | Λ ; μ] = H[Λ' | Λ ; μ] := condMutualInfo_self hΛ' hΛ
  have hH : H[Λ' | Λ ; μ] = 0 := by
    refine le_antisymm ?_ (condEntropy_nonneg _ _ _)
    rw [← hself, hcongr]
    linarith
  exact aeFunctionOf_of_condEntropy_eq_zero hΛ hΛ' hH

/-- **"`Λ` mediates between `Λ'` and `X`"**: under mediation and deterministic redundancy,
`I[Λ' : ⟨X₁, X₂⟩ | Λ ; μ] = 0`.
Source: [[wentworth-2023-natural-latents-the-math]] l. 47 (the claim's diagram)
Kind: C
Fidelity: weaker: special case (as above; also a corollary of the stochastic theorem,
`condMutualInfo_latent_eq_zero'`)
Hyps: (a) all -/
theorem condMutualInfo_latent_eq_zero (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hΛ : Measurable Λ) (hΛ' : Measurable Λ') [FiniteEntropyOf X₁ μ] [FiniteEntropyOf X₂ μ]
    [FiniteEntropyOf Λ μ] [FiniteEntropyOf Λ' μ] (hmed : Mediates Λ X₁ X₂ μ)
    (hred : DetRedundant X₁ X₂ Λ' μ) :
    I[Λ' : (⟨X₁, X₂⟩ : Ω → S₁ × S₂) | Λ ; μ] = 0 := by
  haveI : FiniteEntropyOf (⟨X₁, X₂⟩ : Ω → S₁ × S₂) μ := finiteEntropyOf_pair hX₁ hX₂
  have hH : H[Λ' | Λ ; μ] = 0 := condEntropy_eq_zero_of_aeFunctionOf hΛ hΛ'
    (aeFunctionOf_of_mediates_detRedundant hX₁ hX₂ hΛ hΛ' hmed hred)
  refine le_antisymm ?_ (ShannonInformation.condMutualInfo_nonneg hΛ' (hX₁.prodMk hX₂))
  exact le_trans (condMutualInfo_le_condEntropy hΛ' (hX₁.prodMk hX₂) hΛ) hH.le

/-- The theorem on Condensation's model type: for `M : RVModel (Fin 2)` with chunks `M.X 0`, `M.X 1`
and latents `Λ Λ'` measurable on `M.Ω`.
Source: [[wentworth-2023-natural-latents-the-math]] ll. 27–47; Condensation Definition 3.1
Kind: C
Fidelity: weaker: special case (as above)
Hyps: (a) all -/
theorem rvModel_aeFunctionOf (M : RVModel (Fin 2)) {L L' : Type*} [MeasurableSpace L]
    [MeasurableSpace L'] [Countable L] [Countable L'] [MeasurableSingletonClass L]
    [MeasurableSingletonClass L'] {Λ : M.Ω → L} {Λ' : M.Ω → L'} (hΛ : Measurable Λ)
    (hΛ' : Measurable Λ') (hmed : Mediates Λ (M.X 0) (M.X 1) M.P)
    (hred : DetRedundant (M.X 0) (M.X 1) Λ' M.P) : AEFunctionOf Λ Λ' M.P := by
  haveI := M.finiteEntropyOf hΛ
  haveI := M.finiteEntropyOf hΛ'
  exact aeFunctionOf_of_mediates_detRedundant (M.measurable_X 0) (M.measurable_X 1) hΛ hΛ' hmed
    hred

end

end Cleanroom.Info.InfoVoiLatents.NaturalLatents
