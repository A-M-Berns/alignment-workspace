import Cleanroom.Info.InfoVoiLatents.Shannon
import Cleanroom.Info.InfoVoiLatents.Voi

/-!
# info-voi-latents — decay is inertness: the finite component-hazard chain (Target 9)

Carrier (ii): a probability space `(Ω, μ)`, the loss `X`, the acquirable component `Θ`, the agent's
information `Z` (a variable, not a filtration; `t` is fixed), the humans' information `FH`,
independent noise `ξ`, and the press `Pr = g ∘ ⟨FH, ξ⟩`. All variables into countable discrete
types with finite entropy.

* (a) **`condMutualInfo_press_le`**: conditional data processing
  `I[X : g ∘ ⟨FH, ξ⟩ | Z] ≤ I[X : FH | Z]` when `ξ ⊥ ⟨X, ⟨FH, Z⟩⟩` — through
  `Shannon.condMutualInfo_comp_le_right`, the CMI chain rule and `condMutualInfo_eq_zero_of_indepFun`
  (FAF has no "independent noise adds nothing" lemma; it is proved in `Shannon.lean`).
* (c) **`condMutualInfo_le_condEntropy_component`**: `I[X : Θ | Z] ≤ H[Θ | Z]`, the finite-time form
  of "`→ 0`". The Lévy-upward limit is not a finite statement and is **not stated** (no OPEN
  entry: PFR's conditional entropy takes a variable, not a σ-algebra; see the report, Target 9).
* (e) **`inert_press_condIndep`**: `I[X : Pr | Z] = 0 ↔ CondIndepFun X Pr Z μ` (the inert press is
  conditional independence), and the **Pinsker clause on carrier (i)**,
  `mean_shift_le_two_sup_mul_tv`: `|E_ρ v − E_σ v| ≤ 2‖v‖_∞ · tv ρ σ` (the note's crude constant; the
  range bound `M · tv` of Target 3(ii) is sharper and is `Voi.E_sub_E_le_mul_tv`).

The conditional-means identity in product form and the expected posterior shift
`≤ 2‖X‖_∞ √(I/2)` are in `HazardMeans.lean` (repair round 2: `condLaw2_eq_condLaw_of_inert`,
`condMean_eq_of_inert`, `expected_mean_shift_le`). Mandate: Target 9 (a), (c), (e).
-/

namespace Cleanroom.Info.InfoVoiLatents.Hazard

open MeasureTheory ProbabilityTheory ShannonInformation Finset
open Cleanroom.Info.InfoVoiLatents.Shannon Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω S T U V P : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
  [MeasurableSpace P] [Countable S] [Countable T] [Countable U] [Countable V] [Countable P]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [MeasurableSingletonClass V] [MeasurableSingletonClass P]
  {X : Ω → S} {FH : Ω → T} {Z : Ω → U} {ξ : Ω → V}

/-- **(a) Data processing for the press, conditional on the agent's information**:
`I[X : g ∘ ⟨FH, ξ⟩ | Z] ≤ I[X : FH | Z]` when the press noise `ξ` is independent of
`⟨X, ⟨FH, Z⟩⟩`. Chain: post-processing (`condMutualInfo_comp_le_right`), then
`I[X : ⟨FH, ξ⟩ | Z] = I[X : FH | Z] + I[X : ξ | ⟨FH, Z⟩]` (`condMutualInfo_pair_right`), and the last
term vanishes (`condMutualInfo_eq_zero_of_indepFun`).
Source: [[d1-special-case-final]] S2(a) l. 48, P2(a) l. 80; item wf14b-038
Kind: C
Fidelity: exact (finite `t`; `Z` a variable, not a filtration)
Hyps: (a) all — the independence of the noise is the model's (D6) own assumption, stated as
`IndepFun` -/
theorem condMutualInfo_press_le (hX : Measurable X) (hFH : Measurable FH) (hZ : Measurable Z)
    (hξ : Measurable ξ) [FiniteEntropyOf X μ] [FiniteEntropyOf FH μ] [FiniteEntropyOf Z μ]
    [FiniteEntropyOf ξ μ] (hind : IndepFun ξ (⟨X, (⟨FH, Z⟩ : Ω → T × U)⟩ : Ω → S × (T × U)) μ)
    (g : T × V → P) :
    I[X : g ∘ (⟨FH, ξ⟩ : Ω → T × V) | Z ; μ] ≤ I[X : FH | Z ; μ] := by
  haveI : FiniteEntropyOf (⟨FH, ξ⟩ : Ω → T × V) μ := finiteEntropyOf_pair hFH hξ
  haveI : FiniteEntropyOf (⟨FH, Z⟩ : Ω → T × U) μ := finiteEntropyOf_pair hFH hZ
  have h1 : I[X : g ∘ (⟨FH, ξ⟩ : Ω → T × V) | Z ; μ] ≤ I[X : (⟨FH, ξ⟩ : Ω → T × V) | Z ; μ] :=
    condMutualInfo_comp_le_right hX (hFH.prodMk hξ) hZ g
  have h2 : I[X : (⟨FH, ξ⟩ : Ω → T × V) | Z ; μ]
      = I[X : FH | Z ; μ] + I[X : ξ | (⟨FH, Z⟩ : Ω → T × U) ; μ] :=
    condMutualInfo_pair_right hX hFH hZ hξ
  have h3 : I[X : ξ | (⟨FH, Z⟩ : Ω → T × U) ; μ] = 0 :=
    condMutualInfo_eq_zero_of_indepFun hX (hFH.prodMk hZ) hξ hind
  linarith

/-- **(c) `I ≤ H`**: `I[X : Θ | Z] ≤ H[Θ | Z]` — the finite-time form of "`I(X; Θ_H | F_{A,t}) ≤
H(Θ_H | F_{A,t}) → 0`". The limit (Lévy upward + bounded convergence) is not a finite statement
and is not stated here as a hypothesis.
Source: [[d1-special-case-final]] S2(c) l. 48, P2(c) l. 80; item wf14b-038(c)
Kind: L
Fidelity: weaker: the finite-time bound only; the `→ 0` limit is **not stated** (no OPEN entry:
PFR's conditional entropy takes a variable, not a σ-algebra, so the Lévy-upward limit along a
filtration has no statement in the API without new infrastructure — report, Target 9)
Hyps: (a) all -/
theorem condMutualInfo_le_condEntropy_component {Θ : Ω → T} (hX : Measurable X)
    (hΘ : Measurable Θ) (hZ : Measurable Z) [FiniteEntropyOf X μ] [FiniteEntropyOf Θ μ]
    [FiniteEntropyOf Z μ] : I[X : Θ | Z ; μ] ≤ H[Θ | Z ; μ] := by
  rw [condMutualInfo_comm hX hΘ]
  exact condMutualInfo_le_condEntropy hΘ hX hZ

/-- **(e) An inert press is conditional independence**: `I[X : Pr | Z] = 0 ↔ CondIndepFun X Pr Z μ`
(FAF's `condMutualInfo_eq_zero`, restated for the press). The conditional means then agree on
every fibre; the product-form identity is not done here (see the report).
Source: [[d1-special-case-final]] S2(e) l. 48, P2(e) l. 80 ("`I = 0` is conditional independence")
Kind: L
Fidelity: exact for the equivalence; the conditional-means clause is not formalized
Hyps: (a) all -/
theorem inert_press_condIndep {Pr : Ω → P} (hX : Measurable X) (hPr : Measurable Pr)
    (hZ : Measurable Z) [FiniteEntropyOf X μ] [FiniteEntropyOf Pr μ] [FiniteEntropyOf Z μ] :
    I[X : Pr | Z ; μ] = 0 ↔ CondIndepFun X Pr Z μ :=
  ShannonInformation.condMutualInfo_eq_zero hX hPr hZ

/-- **(e), the Pinsker clause on carrier (i)**: for distributions `ρ σ` on a finite carrier and a
bounded `v` (`|v w| ≤ B`), `|E_ρ v − E_σ v| ≤ 2B · tv ρ σ` — the note's crude `2‖X‖_∞` constant,
from the range bound `Voi.E_sub_E_le_mul_tv` with `M = 2B` (which is the sharper form).
Source: [[d1-special-case-final]] S2(e) l. 48, P2(e) l. 80 ("mean shift of a bounded variable
`≤ 2‖X‖_∞ d_TV`")
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem mean_shift_le_two_sup_mul_tv {W : Type} [Fintype W] {ρ σ : W → ℝ}
    (hρ : ρ ∈ stdSimplex ℝ W) (hσ : σ ∈ stdSimplex ℝ W) {v : W → ℝ} {B : ℝ}
    (hB : ∀ w, |v w| ≤ B) : |E ρ v - E σ v| ≤ 2 * B * tv ρ σ := by
  have hM : ∀ w w', v w - v w' ≤ 2 * B := by
    intro w w'
    have h1 := (abs_le.1 (hB w)).2
    have h2 := (abs_le.1 (hB w')).1
    linarith
  rw [abs_le]
  constructor
  · have := Cleanroom.Info.InfoVoiLatents.Voi.E_sub_E_le_mul_tv hσ hρ hM
    rw [tv_comm] at this
    linarith
  · exact Cleanroom.Info.InfoVoiLatents.Voi.E_sub_E_le_mul_tv hρ hσ hM

end

end Cleanroom.Info.InfoVoiLatents.Hazard
