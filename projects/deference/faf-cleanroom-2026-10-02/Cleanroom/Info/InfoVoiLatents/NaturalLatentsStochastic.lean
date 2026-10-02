import Cleanroom.Info.InfoVoiLatents.NaturalLatents

/-!
# info-voi-latents — natural latents: the stochastic two-variable theorem and the approximate
bound (Target 10(ii), (iii); repair round 2)

Audit r2 (adversarial item 2) showed that `Open.natural_latents_stochastic` follows from the
package's own chain rules in forty lines (probe `run/wp/info-voi-latents/audit-r2-probes/ApproxBound.lean`,
promoted here; its four generic helpers went to `Shannon.lean`).

* **`natural_latents_approx_two_eps₃`**: under the four approximate diagrams
  `I[X₁ : X₂ | Λ] ≤ ε₁`, `I[Λ' : X₁ | X₂] ≤ ε₂`, `I[Λ' : X₂ | X₁] ≤ ε₂'`, `I[Λ : Λ' | X] ≤ ε₃`,
  `I[Λ' : X | Λ] ≤ ε₁ + ε₂ + ε₂' + 2ε₃`. Route: `I[Λ' : X | Λ] ≤ I[Λ' : X₂ | Λ] + I[Λ' : X₁ | ⟨X₂, Λ⟩]`;
  `I[Λ' : X₂ | Λ] ≤ I[X₁ : X₂ | Λ] + I[Λ' : X₂ | X₁] + I[Λ : Λ' | X]`;
  `I[Λ' : X₁ | ⟨X₂, Λ⟩] ≤ I[Λ' : X₁ | X₂] + I[Λ : Λ' | X]` — the third diagram is used once in each
  half, hence `2ε₃`.
* `natural_latents_approx_of_third`: with the third diagram exact the constant is `ε₁ + ε₂ + ε₂'`.
* **`natural_latents_stochastic`** (Target 10(ii), formerly OPEN): with every `ε = 0`, FAF's
  `condMutualInfo_eq_zero` in both directions gives Wentworth's simplified Fundamental Theorem —
  mediation, stochastic redundancy and the third diagram imply `CondIndepFun Λ' ⟨X₁, X₂⟩ Λ`.
  `[Countable Ω]` is not needed.
* `StochRedundant`, `ThirdDiagram` (definitions of record for the post's second pair of diagrams
  and its third assumption), and **the reduction of the deterministic form to the stochastic
  one**: `stochRedundant_of_detRedundant`, `thirdDiagram_of_detRedundant` (findings F5 made exact:
  deterministic redundancy implies stochastic redundancy *and* the third diagram), so
  `condMutualInfo_latent_eq_zero` is a corollary of the stochastic theorem
  (`condMutualInfo_latent_eq_zero'`) — the ledger's "weaker: special case" machine-checked.

What stays open is whether the coefficient of `ε₃` can be `1` (`Open.natural_latents_approx`).
Mandate: Target 10(ii), (iii).
-/

namespace Cleanroom.Info.InfoVoiLatents.NaturalLatents

open MeasureTheory ProbabilityTheory ShannonInformation
open Cleanroom.Info.InfoVoiLatents.Shannon
open _root_.Condensation

noncomputable section

set_option linter.unusedSectionVars false

section Stochastic

variable {Ω S₁ S₂ L L' : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace S₁] [MeasurableSpace S₂] [MeasurableSpace L] [MeasurableSpace L']
  [Countable S₁] [Countable S₂] [Countable L] [Countable L']
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂] [MeasurableSingletonClass L]
  [MeasurableSingletonClass L']
  {X₁ : Ω → S₁} {X₂ : Ω → S₂} {Λ : Ω → L} {Λ' : Ω → L'}

/-- **Stochastic redundancy** (the post's second pair of diagrams): `X₁` and `X₂` give the same
information about `Λ'` — `Λ' ⊥ X₁ | X₂` and `Λ' ⊥ X₂ | X₁`.
Source: [[wentworth-2023-natural-latents-the-math]] ll. 33–35 (second diagram)
Kind: D
Fidelity: exact -/
def StochRedundant (X₁ : Ω → S₁) (X₂ : Ω → S₂) (Λ' : Ω → L') (μ : Measure Ω) : Prop :=
  CondIndepFun Λ' X₁ X₂ μ ∧ CondIndepFun Λ' X₂ X₁ μ

/-- **The third diagram**: `X = ⟨X₁, X₂⟩` mediates between `Λ` and `Λ'`, `Λ ⊥ Λ' | X`.
Source: [[wentworth-2023-natural-latents-the-math]] l. 37 ("assume that `X` mediates between `Λ`
and `Λ'`")
Kind: D
Fidelity: exact -/
def ThirdDiagram (X₁ : Ω → S₁) (X₂ : Ω → S₂) (Λ : Ω → L) (Λ' : Ω → L') (μ : Measure Ω) : Prop :=
  CondIndepFun Λ Λ' (⟨X₁, X₂⟩ : Ω → S₁ × S₂) μ

/-- **The approximate natural-latents bound with `2ε₃`**, from chain rules alone:
`I[Λ' : ⟨X₁, X₂⟩ | Λ] ≤ ε₁ + ε₂ + ε₂' + 2ε₃` under the four approximate diagrams. The third
diagram is used once in each half of the proof; whether its coefficient can be `1` is
`Open.natural_latents_approx`.
Source: [[wentworth-2023-natural-latents-the-math]] ll. 81–85 ("Approximation"; the post's own
constant is an image not readable here); audit r2 (adversarial item 2, probe promoted)
Kind: P
Fidelity: variant: the post's approximate theorem with the constant `ε₁ + ε₂ + ε₂' + 2ε₃` proved
here (the post's constant unknown)
Hyps: (a) all — the four approximate diagrams are the claim's own antecedents -/
theorem natural_latents_approx_two_eps₃ (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hΛ : Measurable Λ) (hΛ' : Measurable Λ') [FiniteEntropyOf X₁ μ] [FiniteEntropyOf X₂ μ]
    [FiniteEntropyOf Λ μ] [FiniteEntropyOf Λ' μ] {ε₁ ε₂ ε₂' ε₃ : ℝ}
    (h₁ : I[X₁ : X₂ | Λ ; μ] ≤ ε₁) (h₂ : I[Λ' : X₁ | X₂ ; μ] ≤ ε₂) (h₂' : I[Λ' : X₂ | X₁ ; μ] ≤ ε₂')
    (h₃ : I[Λ : Λ' | (⟨X₁, X₂⟩ : Ω → S₁ × S₂) ; μ] ≤ ε₃) :
    I[Λ' : (⟨X₁, X₂⟩ : Ω → S₁ × S₂) | Λ ; μ] ≤ ε₁ + ε₂ + ε₂' + 2 * ε₃ := by
  -- (1) swap the second argument, (2) chain rule
  have s1 : I[Λ' : (⟨X₁, X₂⟩ : Ω → S₁ × S₂) | Λ ; μ] ≤ I[Λ' : (⟨X₂, X₁⟩ : Ω → S₂ × S₁) | Λ ; μ] :=
    condMutualInfo_swap_right_le hΛ' hX₁ hX₂ hΛ
  have s2 : I[Λ' : (⟨X₂, X₁⟩ : Ω → S₂ × S₁) | Λ ; μ]
      = I[Λ' : X₂ | Λ ; μ] + I[Λ' : X₁ | (⟨X₂, Λ⟩ : Ω → S₂ × L) ; μ] :=
    condMutualInfo_pair_right hΛ' hX₂ hΛ hX₁
  -- (3) the first term: `I[Λ' : X₂ | Λ] ≤ ε₁ + ε₂' + ε₃`
  have t1a : I[Λ' : X₂ | Λ ; μ] ≤ I[(⟨X₁, Λ'⟩ : Ω → S₁ × L') : X₂ | Λ ; μ] :=
    condMutualInfo_snd_le hX₁ hΛ' hX₂ hΛ
  have t1b : I[(⟨X₁, Λ'⟩ : Ω → S₁ × L') : X₂ | Λ ; μ] = I[X₂ : (⟨X₁, Λ'⟩ : Ω → S₁ × L') | Λ ; μ] :=
    condMutualInfo_comm (hX₁.prodMk hΛ') hX₂ Λ μ
  have t1c : I[X₂ : (⟨X₁, Λ'⟩ : Ω → S₁ × L') | Λ ; μ]
      = I[X₂ : X₁ | Λ ; μ] + I[X₂ : Λ' | (⟨X₁, Λ⟩ : Ω → S₁ × L) ; μ] :=
    condMutualInfo_pair_right hX₂ hX₁ hΛ hΛ'
  have t1d : I[X₂ : X₁ | Λ ; μ] = I[X₁ : X₂ | Λ ; μ] := condMutualInfo_comm hX₂ hX₁ Λ μ
  have t1e : I[X₂ : Λ' | (⟨X₁, Λ⟩ : Ω → S₁ × L) ; μ] = I[Λ' : X₂ | (⟨X₁, Λ⟩ : Ω → S₁ × L) ; μ] :=
    condMutualInfo_comm hX₂ hΛ' _ μ
  have t1f : I[Λ' : X₂ | (⟨X₁, Λ⟩ : Ω → S₁ × L) ; μ] = I[Λ' : X₂ | (⟨Λ, X₁⟩ : Ω → L × S₁) ; μ] :=
    condMutualInfo_cond_swap hΛ' hX₂ hX₁ hΛ
  have t1g : I[Λ' : X₂ | (⟨Λ, X₁⟩ : Ω → L × S₁) ; μ] ≤ I[Λ' : (⟨Λ, X₂⟩ : Ω → L × S₂) | X₁ ; μ] :=
    condMutualInfo_le_pair_of_cond hΛ' hΛ hX₂ hX₁
  have t1h : I[Λ' : (⟨Λ, X₂⟩ : Ω → L × S₂) | X₁ ; μ] ≤ I[Λ' : (⟨X₂, Λ⟩ : Ω → S₂ × L) | X₁ ; μ] :=
    condMutualInfo_swap_right_le hΛ' hΛ hX₂ hX₁
  have t1i : I[Λ' : (⟨X₂, Λ⟩ : Ω → S₂ × L) | X₁ ; μ]
      = I[Λ' : X₂ | X₁ ; μ] + I[Λ' : Λ | (⟨X₂, X₁⟩ : Ω → S₂ × S₁) ; μ] :=
    condMutualInfo_pair_right hΛ' hX₂ hX₁ hΛ
  have t1j : I[Λ' : Λ | (⟨X₂, X₁⟩ : Ω → S₂ × S₁) ; μ] = I[Λ : Λ' | (⟨X₂, X₁⟩ : Ω → S₂ × S₁) ; μ] :=
    condMutualInfo_comm hΛ' hΛ _ μ
  have t1k : I[Λ : Λ' | (⟨X₂, X₁⟩ : Ω → S₂ × S₁) ; μ] = I[Λ : Λ' | (⟨X₁, X₂⟩ : Ω → S₁ × S₂) ; μ] :=
    condMutualInfo_cond_swap hΛ hΛ' hX₂ hX₁
  -- (4) the second term: `I[Λ' : X₁ | ⟨X₂, Λ⟩] ≤ ε₂ + ε₃`
  have t2a : I[Λ' : X₁ | (⟨X₂, Λ⟩ : Ω → S₂ × L) ; μ] = I[Λ' : X₁ | (⟨Λ, X₂⟩ : Ω → L × S₂) ; μ] :=
    condMutualInfo_cond_swap hΛ' hX₁ hX₂ hΛ
  have t2b : I[Λ' : X₁ | (⟨Λ, X₂⟩ : Ω → L × S₂) ; μ] ≤ I[Λ' : (⟨Λ, X₁⟩ : Ω → L × S₁) | X₂ ; μ] :=
    condMutualInfo_le_pair_of_cond hΛ' hΛ hX₁ hX₂
  have t2c : I[Λ' : (⟨Λ, X₁⟩ : Ω → L × S₁) | X₂ ; μ] ≤ I[Λ' : (⟨X₁, Λ⟩ : Ω → S₁ × L) | X₂ ; μ] :=
    condMutualInfo_swap_right_le hΛ' hΛ hX₁ hX₂
  have t2d : I[Λ' : (⟨X₁, Λ⟩ : Ω → S₁ × L) | X₂ ; μ]
      = I[Λ' : X₁ | X₂ ; μ] + I[Λ' : Λ | (⟨X₁, X₂⟩ : Ω → S₁ × S₂) ; μ] :=
    condMutualInfo_pair_right hΛ' hX₁ hX₂ hΛ
  have t2e : I[Λ' : Λ | (⟨X₁, X₂⟩ : Ω → S₁ × S₂) ; μ] = I[Λ : Λ' | (⟨X₁, X₂⟩ : Ω → S₁ × S₂) ; μ] :=
    condMutualInfo_comm hΛ' hΛ _ μ
  linarith

/-- With the third diagram exact (`ε₃ = 0`) the conjectured constant `ε₁ + ε₂ + ε₂'` is proved.
Source: [[wentworth-2023-natural-latents-the-math]] ll. 81–85; audit r2 (adversarial item 2)
Kind: C
Fidelity: weaker: the approximate theorem with the third diagram exact
Hyps: (a) all -/
theorem natural_latents_approx_of_third (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hΛ : Measurable Λ) (hΛ' : Measurable Λ') [FiniteEntropyOf X₁ μ] [FiniteEntropyOf X₂ μ]
    [FiniteEntropyOf Λ μ] [FiniteEntropyOf Λ' μ] {ε₁ ε₂ ε₂' : ℝ}
    (h₁ : I[X₁ : X₂ | Λ ; μ] ≤ ε₁) (h₂ : I[Λ' : X₁ | X₂ ; μ] ≤ ε₂) (h₂' : I[Λ' : X₂ | X₁ ; μ] ≤ ε₂')
    (h₃ : I[Λ : Λ' | (⟨X₁, X₂⟩ : Ω → S₁ × S₂) ; μ] = 0) :
    I[Λ' : (⟨X₁, X₂⟩ : Ω → S₁ × S₂) | Λ ; μ] ≤ ε₁ + ε₂ + ε₂' := by
  have := natural_latents_approx_two_eps₃ hX₁ hX₂ hΛ hΛ' h₁ h₂ h₂' h₃.le
  linarith

/-- **Wentworth's simplified Fundamental Theorem, stochastic form** (Target 10(ii), the statement
that was `Open.natural_latents_stochastic`): mediation (`X₁ ⊥ X₂ | Λ`), stochastic redundancy
(`Λ' ⊥ X₁ | X₂`, `Λ' ⊥ X₂ | X₁`) and the third diagram (`Λ ⊥ Λ' | X`) imply that `Λ` mediates
between `Λ'` and `X`: `Λ' ⊥ ⟨X₁, X₂⟩ | Λ`. Proof: the `2ε₃` bound with every `ε = 0` and FAF's
`condMutualInfo_eq_zero` in both directions. The diagrammatic proof of the post (ll. 71–79) is
replaced by chain rules; `[Countable Ω]` is not needed.
Source: [[wentworth-2023-natural-latents-the-math]] ll. 27–47 (statement), 71–79 (proof);
[[generalization-final]] D9 l. 43; audit r2 (adversarial item 2, probe promoted)
Kind: P
Fidelity: exact (the post's own hypotheses and conclusion, over PFR's `CondIndepFun`)
Hyps: (a) all — the four diagrams are the claim's own antecedents -/
theorem natural_latents_stochastic (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hΛ : Measurable Λ) (hΛ' : Measurable Λ') [FiniteEntropyOf X₁ μ] [FiniteEntropyOf X₂ μ]
    [FiniteEntropyOf Λ μ] [FiniteEntropyOf Λ' μ] (hmed : CondIndepFun X₁ X₂ Λ μ)
    (hred₁ : CondIndepFun Λ' X₁ X₂ μ) (hred₂ : CondIndepFun Λ' X₂ X₁ μ)
    (hthird : CondIndepFun Λ Λ' (⟨X₁, X₂⟩ : Ω → S₁ × S₂) μ) :
    CondIndepFun Λ' (⟨X₁, X₂⟩ : Ω → S₁ × S₂) Λ μ := by
  haveI : FiniteEntropyOf (⟨X₁, X₂⟩ : Ω → S₁ × S₂) μ := finiteEntropyOf_pair hX₁ hX₂
  have h₁ : I[X₁ : X₂ | Λ ; μ] = 0 :=
    (ShannonInformation.condMutualInfo_eq_zero hX₁ hX₂ hΛ).2 hmed
  have h₂ : I[Λ' : X₁ | X₂ ; μ] = 0 :=
    (ShannonInformation.condMutualInfo_eq_zero hΛ' hX₁ hX₂).2 hred₁
  have h₂' : I[Λ' : X₂ | X₁ ; μ] = 0 :=
    (ShannonInformation.condMutualInfo_eq_zero hΛ' hX₂ hX₁).2 hred₂
  have h₃ : I[Λ : Λ' | (⟨X₁, X₂⟩ : Ω → S₁ × S₂) ; μ] = 0 :=
    (ShannonInformation.condMutualInfo_eq_zero hΛ hΛ' (hX₁.prodMk hX₂)).2 hthird
  have hle := natural_latents_approx_two_eps₃ hX₁ hX₂ hΛ hΛ' h₁.le h₂.le h₂'.le h₃.le
  have hge : 0 ≤ I[Λ' : (⟨X₁, X₂⟩ : Ω → S₁ × S₂) | Λ ; μ] :=
    ShannonInformation.condMutualInfo_nonneg hΛ' (hX₁.prodMk hX₂)
  exact (ShannonInformation.condMutualInfo_eq_zero hΛ' (hX₁.prodMk hX₂) hΛ).1 (by linarith)

/-- The stochastic theorem with the packaged hypotheses `Mediates`, `StochRedundant`,
`ThirdDiagram`.
Source: [[wentworth-2023-natural-latents-the-math]] ll. 27–47
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem natural_latents_stochastic' (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hΛ : Measurable Λ) (hΛ' : Measurable Λ') [FiniteEntropyOf X₁ μ] [FiniteEntropyOf X₂ μ]
    [FiniteEntropyOf Λ μ] [FiniteEntropyOf Λ' μ] (hmed : Mediates Λ X₁ X₂ μ)
    (hred : StochRedundant X₁ X₂ Λ' μ) (hthird : ThirdDiagram X₁ X₂ Λ Λ' μ) :
    CondIndepFun Λ' (⟨X₁, X₂⟩ : Ω → S₁ × S₂) Λ μ :=
  natural_latents_stochastic hX₁ hX₂ hΛ hΛ' hmed hred.1 hred.2 hthird

end Stochastic

/-! ### The deterministic form is a special case -/

section Deterministic

variable {Ω S₁ S₂ L L' : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace S₁] [MeasurableSpace S₂] [MeasurableSpace L] [MeasurableSpace L']
  [Countable S₁] [Countable S₂] [Countable L] [Countable L']
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂] [MeasurableSingletonClass L]
  [MeasurableSingletonClass L']
  {X₁ : Ω → S₁} {X₂ : Ω → S₂} {Λ : Ω → L} {Λ' : Ω → L'}

/-- A variable that is a.e. a function of the conditioning variable is conditionally independent
of anything: `AEFunctionOf Z Y μ → CondIndepFun Y X Z μ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condIndepFun_of_aeFunctionOf {U : Type*} [MeasurableSpace U] [Countable U]
    [MeasurableSingletonClass U] {X : Ω → S₁} {Y : Ω → L'} {Z : Ω → U} (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ]
    [FiniteEntropyOf Z μ] (h : AEFunctionOf Z Y μ) : CondIndepFun Y X Z μ := by
  obtain ⟨f, hf, hfae⟩ := h
  have hae : Y =ᵐ[μ] f ∘ Z := hfae
  refine (ShannonInformation.condMutualInfo_eq_zero hY hX hZ).1 ?_
  refine le_antisymm ?_ (ShannonInformation.condMutualInfo_nonneg hY hX)
  rw [condMutualInfo_congr_left hae]
  calc I[f ∘ Z : X | Z ; μ] ≤ I[Z : X | Z ; μ] := condMutualInfo_comp_le_left hZ hX hZ f
    _ = 0 := condMutualInfo_self_left hZ hX

/-- **Deterministic redundancy implies stochastic redundancy**: if `Λ'` is a.e. a function of each
chunk, then `Λ' ⊥ X₁ | X₂` and `Λ' ⊥ X₂ | X₁`.
Source: [[wentworth-2023-natural-latents-the-math]] ll. 33–35, 65–67 (the gas example); findings F5
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem stochRedundant_of_detRedundant (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hΛ' : Measurable Λ') [FiniteEntropyOf X₁ μ] [FiniteEntropyOf X₂ μ] [FiniteEntropyOf Λ' μ]
    (hred : DetRedundant X₁ X₂ Λ' μ) : StochRedundant X₁ X₂ Λ' μ :=
  ⟨condIndepFun_of_aeFunctionOf hX₁ hΛ' hX₂ hred.2, condIndepFun_of_aeFunctionOf hX₂ hΛ' hX₁ hred.1⟩

/-- **Deterministic redundancy makes the third diagram automatic**: if `Λ'` is a.e. a function of
`X₁`, then `Λ ⊥ Λ' | ⟨X₁, X₂⟩` for every `Λ` (findings F5, now a theorem rather than a remark).
Source: [[wentworth-2023-natural-latents-the-math]] l. 37; findings F5; audit r1 (fidelity F5)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem thirdDiagram_of_detRedundant (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hΛ : Measurable Λ) (hΛ' : Measurable Λ') [FiniteEntropyOf X₁ μ] [FiniteEntropyOf X₂ μ]
    [FiniteEntropyOf Λ μ] [FiniteEntropyOf Λ' μ] (hred : DetRedundant X₁ X₂ Λ' μ) :
    ThirdDiagram X₁ X₂ Λ Λ' μ := by
  obtain ⟨⟨f, hf, hfae⟩, -⟩ := hred
  have hae : Λ' =ᵐ[μ] f ∘ X₁ := hfae
  haveI : FiniteEntropyOf (⟨X₁, X₂⟩ : Ω → S₁ × S₂) μ := finiteEntropyOf_pair hX₁ hX₂
  have hX : Measurable (⟨X₁, X₂⟩ : Ω → S₁ × S₂) := hX₁.prodMk hX₂
  unfold ThirdDiagram
  refine (ShannonInformation.condMutualInfo_eq_zero hΛ hΛ' hX).1 ?_
  refine le_antisymm ?_ (ShannonInformation.condMutualInfo_nonneg hΛ hΛ')
  rw [condMutualInfo_congr_right hΛ hΛ' (hf.comp hX₁) hae]
  have e : f ∘ X₁ = (f ∘ Prod.fst) ∘ (⟨X₁, X₂⟩ : Ω → S₁ × S₂) := funext fun ω => rfl
  rw [e]
  calc I[Λ : (f ∘ Prod.fst) ∘ (⟨X₁, X₂⟩ : Ω → S₁ × S₂) | (⟨X₁, X₂⟩ : Ω → S₁ × S₂) ; μ]
      ≤ I[Λ : (⟨X₁, X₂⟩ : Ω → S₁ × S₂) | (⟨X₁, X₂⟩ : Ω → S₁ × S₂) ; μ] :=
        condMutualInfo_comp_le_right hΛ hX hX (f ∘ Prod.fst)
    _ = I[(⟨X₁, X₂⟩ : Ω → S₁ × S₂) : Λ | (⟨X₁, X₂⟩ : Ω → S₁ × S₂) ; μ] :=
        condMutualInfo_comm hΛ hX _ μ
    _ = 0 := condMutualInfo_self_left hX hΛ

/-- **`condMutualInfo_latent_eq_zero` as a corollary of the stochastic theorem**: the deterministic
form is the special case the ledger says it is (deterministic redundancy supplies stochastic
redundancy and the third diagram).
Source: [[wentworth-2023-natural-latents-the-math]] l. 47; audit r2 (adversarial items 2, 4)
Kind: C
Fidelity: weaker: special case of `natural_latents_stochastic` (an alternative proof of
`NaturalLatents.condMutualInfo_latent_eq_zero`)
Hyps: (a) all -/
theorem condMutualInfo_latent_eq_zero' (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hΛ : Measurable Λ) (hΛ' : Measurable Λ') [FiniteEntropyOf X₁ μ] [FiniteEntropyOf X₂ μ]
    [FiniteEntropyOf Λ μ] [FiniteEntropyOf Λ' μ] (hmed : Mediates Λ X₁ X₂ μ)
    (hred : DetRedundant X₁ X₂ Λ' μ) :
    I[Λ' : (⟨X₁, X₂⟩ : Ω → S₁ × S₂) | Λ ; μ] = 0 := by
  haveI : FiniteEntropyOf (⟨X₁, X₂⟩ : Ω → S₁ × S₂) μ := finiteEntropyOf_pair hX₁ hX₂
  exact (ShannonInformation.condMutualInfo_eq_zero hΛ' (hX₁.prodMk hX₂) hΛ).2
    (natural_latents_stochastic' hX₁ hX₂ hΛ hΛ' hmed
      (stochRedundant_of_detRedundant hX₁ hX₂ hΛ' hred)
      (thirdDiagram_of_detRedundant hX₁ hX₂ hΛ hΛ' hred))

end Deterministic

end

end Cleanroom.Info.InfoVoiLatents.NaturalLatents
