import Cleanroom.Info.InfoVoiLatents.Shannon

/-!
# `Cleanroom.Udt.UdtCondenseDd.Submod`: approximate submodularity (T11, stretch; FAF API request)

Work package `udt-condense-dd`, target T11 (udt-rep-042, 041). Eisenstat's "approximate
submodularity" ([[topics/optimal-prediction]] lines 34–44, the corpus's "Lemma 6.1"; FAF proves its
consequences behind the `private` `Quantitative.condEntropy_eq_tree`):

* `condEntropy_le_add_add_condMutualInfo`:
  `H[X | C] ≤ H[X | ⟨Y₁, C⟩] + H[X | ⟨Y₂, C⟩] + I[Y₁ : Y₂ | C]`;
* `condEntropy_eq_add_add_sub_add_interaction`, the exact identity
  `H[X | C] = H[X | ⟨Y₁, C⟩] + H[X | ⟨Y₂, C⟩] − H[X | ⟨Y₁, ⟨Y₂, C⟩⟩] + (I[Y₁ : Y₂ | C] − I[Y₁ : Y₂ | ⟨X, C⟩])`.

Both for measurable, `FiniteEntropyOf` variables on countable discrete ranges, from the chain rule
for conditional mutual information (`condMutualInfo_pair_right`), conditional data processing
(`condMutualInfo_comp_le_right`), `I ≤ H` (`condMutualInfo_le_condEntropy`) — all generic lemmas of
`Cleanroom.Info.InfoVoiLatents.Shannon` (the one module of that package this package may import,
mandate §0) — and FAF's `condMutualInfo_eq'` with PFR's `condMutualInfo_comm`. Recorded as an FAF
API request: the standalone inequality is not exported by FAF.
-/

namespace Cleanroom.Udt.UdtCondenseDd

open MeasureTheory ProbabilityTheory ShannonInformation
open Cleanroom.Info.InfoVoiLatents.Shannon

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω S T U V : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
  [Countable S] [Countable T] [Countable U] [Countable V]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [MeasurableSingletonClass V]
  {X : Ω → S} {Y₁ : Ω → T} {Y₂ : Ω → U} {C : Ω → V}

/-- **The submodularity-type bound**: `I[X : Y₁ | C] ≤ I[Y₁ : Y₂ | C] + H[X | ⟨Y₂, C⟩]` — the
information `Y₁` carries about `X` beyond `C` is bounded by what `Y₁` shares with `Y₂` plus what
remains of `X` given `Y₂`.
Source: [[topics/optimal-prediction]] lines 36–38 (Eisenstat "Lemma 6.1"; udt-rep-042)
Kind: P
Fidelity: exact (the step behind the inequality)
Hyps: (a) -/
theorem condMutualInfo_le_condMutualInfo_add_condEntropy (hX : Measurable X) (hY₁ : Measurable Y₁)
    (hY₂ : Measurable Y₂) (hC : Measurable C) [FiniteEntropyOf X μ] [FiniteEntropyOf Y₁ μ]
    [FiniteEntropyOf Y₂ μ] [FiniteEntropyOf C μ] :
    I[X : Y₁ | C ; μ] ≤ I[Y₁ : Y₂ | C ; μ] + H[X | ⟨Y₂, C⟩ ; μ] := by
  haveI := finiteEntropyOf_pair (μ := μ) hY₂ hX
  haveI := finiteEntropyOf_pair (μ := μ) hY₂ hC
  -- `I[Y₁ : X | C] ≤ I[Y₁ : ⟨Y₂, X⟩ | C] = I[Y₁ : Y₂ | C] + I[Y₁ : X | ⟨Y₂, C⟩]`
  have h1 : I[Y₁ : X | C ; μ] ≤ I[Y₁ : ⟨Y₂, X⟩ | C ; μ] := by
    have := condMutualInfo_comp_le_right (μ := μ) hY₁ (hY₂.prodMk hX) hC Prod.snd
    exact this
  have h2 : I[Y₁ : ⟨Y₂, X⟩ | C ; μ] = I[Y₁ : Y₂ | C ; μ] + I[Y₁ : X | ⟨Y₂, C⟩ ; μ] :=
    condMutualInfo_pair_right hY₁ hY₂ hC hX
  have h3 : I[Y₁ : X | ⟨Y₂, C⟩ ; μ] ≤ H[X | ⟨Y₂, C⟩ ; μ] := by
    rw [condMutualInfo_comm hY₁ hX]
    exact condMutualInfo_le_condEntropy hX hY₁ (hY₂.prodMk hC)
  rw [condMutualInfo_comm hX hY₁]
  linarith

/-- **Approximate submodularity (T11)**: `H[X | C] ≤ H[X | ⟨Y₁, C⟩] + H[X | ⟨Y₂, C⟩] + I[Y₁ : Y₂ | C]`.
The engine of Eisenstat's approximate correspondence theorem (corpus "Lemma 6.1"), stated standalone.
FAF API request: FAF proves its consequences but keeps the inequality private.
Source: [[topics/optimal-prediction]] lines 36–38 (udt-rep-042, 041)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem condEntropy_le_add_add_condMutualInfo (hX : Measurable X) (hY₁ : Measurable Y₁)
    (hY₂ : Measurable Y₂) (hC : Measurable C) [FiniteEntropyOf X μ] [FiniteEntropyOf Y₁ μ]
    [FiniteEntropyOf Y₂ μ] [FiniteEntropyOf C μ] :
    H[X | C ; μ] ≤ H[X | ⟨Y₁, C⟩ ; μ] + H[X | ⟨Y₂, C⟩ ; μ] + I[Y₁ : Y₂ | C ; μ] := by
  have h := condMutualInfo_le_condMutualInfo_add_condEntropy (μ := μ) hX hY₁ hY₂ hC
  rw [ShannonInformation.condMutualInfo_eq' hX hY₁ hC μ] at h
  linarith

/-- **The exact identity with the interaction term (T11)**:
`H[X | C] = H[X | ⟨Y₁, C⟩] + H[X | ⟨Y₂, C⟩] − H[X | ⟨Y₁, ⟨Y₂, C⟩⟩] + (I[Y₁ : Y₂ | C] − I[Y₁ : Y₂ | ⟨X, C⟩])`;
the inequality drops the non-positive `−H[X | ⟨Y₁, ⟨Y₂, C⟩⟩]` and the non-negative
`I[Y₁ : Y₂ | ⟨X, C⟩]`.
Source: [[topics/optimal-prediction]] lines 40–44 (udt-rep-042)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem condEntropy_eq_add_add_sub_add_interaction (hX : Measurable X) (hY₁ : Measurable Y₁)
    (hY₂ : Measurable Y₂) (hC : Measurable C) [FiniteEntropyOf X μ] [FiniteEntropyOf Y₁ μ]
    [FiniteEntropyOf Y₂ μ] [FiniteEntropyOf C μ] :
    H[X | C ; μ] = H[X | ⟨Y₁, C⟩ ; μ] + H[X | ⟨Y₂, C⟩ ; μ] - H[X | ⟨Y₁, ⟨Y₂, C⟩⟩ ; μ] +
      (I[Y₁ : Y₂ | C ; μ] - I[Y₁ : Y₂ | ⟨X, C⟩ ; μ]) := by
  haveI := finiteEntropyOf_pair (μ := μ) hY₂ hX
  haveI := finiteEntropyOf_pair (μ := μ) hX hY₂
  haveI := finiteEntropyOf_pair (μ := μ) hY₂ hC
  haveI := finiteEntropyOf_pair (μ := μ) hX hC
  -- the two chain-rule expansions of `I[Y₁ : (X, Y₂) | C]`
  have e1 : I[Y₁ : ⟨Y₂, X⟩ | C ; μ] = I[Y₁ : Y₂ | C ; μ] + I[Y₁ : X | ⟨Y₂, C⟩ ; μ] :=
    condMutualInfo_pair_right hY₁ hY₂ hC hX
  have e2 : I[Y₁ : ⟨X, Y₂⟩ | C ; μ] = I[Y₁ : X | C ; μ] + I[Y₁ : Y₂ | ⟨X, C⟩ ; μ] :=
    condMutualInfo_pair_right hY₁ hX hC hY₂
  -- the pair can be swapped (data processing both ways)
  have e3 : I[Y₁ : ⟨Y₂, X⟩ | C ; μ] = I[Y₁ : ⟨X, Y₂⟩ | C ; μ] := by
    apply le_antisymm
    · have := condMutualInfo_comp_le_right (μ := μ) hY₁ (hX.prodMk hY₂) hC Prod.swap
      exact this
    · have := condMutualInfo_comp_le_right (μ := μ) hY₁ (hY₂.prodMk hX) hC Prod.swap
      exact this
  -- the mutual informations about `X` as entropy differences
  have e4 : I[Y₁ : X | C ; μ] = H[X | C ; μ] - H[X | ⟨Y₁, C⟩ ; μ] := by
    rw [condMutualInfo_comm hY₁ hX, ShannonInformation.condMutualInfo_eq' hX hY₁ hC μ]
  have e5 : I[Y₁ : X | ⟨Y₂, C⟩ ; μ] = H[X | ⟨Y₂, C⟩ ; μ] - H[X | ⟨Y₁, ⟨Y₂, C⟩⟩ ; μ] := by
    rw [condMutualInfo_comm hY₁ hX, ShannonInformation.condMutualInfo_eq' hX hY₁ (hY₂.prodMk hC) μ]
  linarith

end

end Cleanroom.Udt.UdtCondenseDd
