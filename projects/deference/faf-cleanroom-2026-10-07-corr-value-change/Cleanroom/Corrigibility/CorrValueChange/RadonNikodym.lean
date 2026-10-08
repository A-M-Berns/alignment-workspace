import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# corr-value-change — E4, the Radon–Nikodym step of the infinite translation (measure-space form)

Source: [[value-change-as-epistemic-update]] §5.3–5.4; mandate E4 ("with `μ = P·V` bounded by
`c P`, `V(A) = E[U ∣ Â]` for `U = dμ/dP`"). This module states and proves the measure-theoretic
core of E4 over Mathlib's `Measure.rnDeriv`, on an arbitrary measurable space: given a finite
"goodness" measure `μ` and a σ-finite `P` with `μ ≤ c • P`, the desirability `V(A) = μ(A)/P(A)` of
every measurable event is the conditional expectation on `A` of the density `U = dμ/dP`
(`radon_nikodym_desir`, in `ℝ≥0∞`; `radon_nikodym_desir_real`, the real form with Bochner's
integral), the density is bounded by `c` almost everywhere (`rnDeriv_le_of_le_smul`), and any
measurable density reproducing `μ` on every measurable set is `U` almost everywhere
(`density_unique`).

What is **not** here (disclosed): the note's `V` is a desirability on a Boolean algebra `B`
carried to the Stone space by `A ↦ Â` (E1–E3), and may be signed. Here the carrier is any
measurable space (so E4 is stated after E1–E3 would have delivered one, not through them), and
`μ` is a nonnegative measure, i.e. `V ≥ 0` — a gauge shift (`bolker_gauge`, T11) takes a
bounded-below desirability to a nonnegative one, so this is the note's hypothesis "bounded by
`c P`" taken literally for a measure. E1, E2, E3 and E5 remain open (ledger).

This module imports measure theory and is kept out of the core's import graph except through
the root module.
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open MeasureTheory ENNReal
open scoped NNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The desirability induced by a goodness measure `μ` over the prior `P`: `V(A) = μ(A)/P(A)`
(the note's `μ = P·V` read backwards). In `ℝ≥0∞`, where `x/0 = ∞` for `x ≠ 0`, `0/0 = 0` and
`x/∞ = 0` (the last for `P(A) = ∞`, when `P` is not finite) are junk values; every headline below is
an identity of two such quotients with the same denominator, so no junk value reaches a conclusion.
Source: [[value-change-as-epistemic-update]] §5.3
Kind: D
Fidelity: exact (for a nonnegative `V`; see the module docstring) -/
def desirOf (μ P : Measure Ω) (A : Set Ω) : ℝ≥0∞ := μ A / P A

/-- The conditional expectation of a nonnegative `U` on an event `A`: `(∫⁻_A U dP) / P(A)`.
Source: [[value-change-as-epistemic-update]] §5.4
Kind: D
Fidelity: exact -/
def condLIntegral (P : Measure Ω) (U : Ω → ℝ≥0∞) (A : Set Ω) : ℝ≥0∞ :=
  (∫⁻ ω in A, U ω ∂P) / P A

/-- The real-valued conditional expectation on an event: `(∫_A U dP) / P(A)`.
Source: [[value-change-as-epistemic-update]] §5.4
Kind: D
Fidelity: exact -/
def condIntegral (P : Measure Ω) (U : Ω → ℝ) (A : Set Ω) : ℝ :=
  (∫ ω in A, U ω ∂P) / P.real A

/-- Bounded by `c P` implies absolutely continuous (what Radon–Nikodym needs).
Source: [[value-change-as-epistemic-update]] §5.4 ("bounded by `c P`")
Kind: L (Mathlib's `absolutelyContinuous_of_le_smul`)
Fidelity: exact -/
theorem absCont_of_le_smul {μ P : Measure Ω} {c : ℝ≥0∞} (h : μ ≤ c • P) : μ ≪ P :=
  Measure.absolutelyContinuous_of_le_smul h

/-- **The goodness of an event is the integral of the density over it**:
`μ(A) = ∫⁻_A (dμ/dP) dP` for every measurable `A`, when `μ ≪ P`.
Source: [[value-change-as-epistemic-update]] §5.4; mandate E4
Kind: L (Mathlib's `withDensity_rnDeriv_eq` applied to `A`)
Fidelity: exact
Hyps: (a) `h : μ ≪ P`, `hA : MeasurableSet A` -/
theorem goodness_eq_setLIntegral_rnDeriv (μ P : Measure Ω) [μ.HaveLebesgueDecomposition P]
    (h : μ ≪ P) {A : Set Ω} (hA : MeasurableSet A) :
    μ A = ∫⁻ ω in A, μ.rnDeriv P ω ∂P := by
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ P h]
  exact withDensity_apply _ hA

/-- **E4, the Radon–Nikodym step**: when `μ ≪ P` (in particular when `μ ≤ c • P`), the desirability
`V(A) = μ(A)/P(A)` of every measurable event `A` is the conditional expectation on `A` of the
density `U = dμ/dP`: `V(A) = (∫⁻_A U dP) / P(A)`.
Source: [[value-change-as-epistemic-update]] §5.4 ("`V(A) = E[U ∣ Â]` for `U = dμ/dP`");
mandate E4
Kind: L (Mathlib's `withDensity_rnDeriv_eq` applied to `A`, both sides divided by `P(A)`; the
module's content is `rnDeriv_le_of_le_smul` and `density_unique`: audit r3 fidelity N4)
Fidelity: exact (measure-space form; see the module docstring for what E1–E3 would add)
Hyps: (a) `h : μ ≪ P`, `hA : MeasurableSet A` -/
theorem radon_nikodym_desir (μ P : Measure Ω) [μ.HaveLebesgueDecomposition P] (h : μ ≪ P)
    {A : Set Ω} (hA : MeasurableSet A) :
    desirOf μ P A = condLIntegral P (μ.rnDeriv P) A := by
  unfold desirOf condLIntegral
  rw [goodness_eq_setLIntegral_rnDeriv μ P h hA]

/-- **E4 in real form**: for σ-finite `μ ≪ P`, `V(A).toReal = (∫_A U dP) / P(A)` with
`U = (dμ/dP).toReal`, Bochner's integral.
Source: [[value-change-as-epistemic-update]] §5.4; mandate E4
Kind: L (the real form of `radon_nikodym_desir` through `setIntegral_toReal_rnDeriv`)
Fidelity: exact
Hyps: (a) `h : μ ≪ P` -/
theorem radon_nikodym_desir_real (μ P : Measure Ω) [SigmaFinite μ] [SigmaFinite P] (h : μ ≪ P)
    (A : Set Ω) :
    (desirOf μ P A).toReal = condIntegral P (fun ω => (μ.rnDeriv P ω).toReal) A := by
  unfold desirOf condIntegral
  rw [ENNReal.toReal_div, Measure.setIntegral_toReal_rnDeriv h A]
  rfl

/-- **The density is bounded by the same constant**: `μ ≤ c • P` with `c ≠ 0` gives
`dμ/dP ≤ c` almost everywhere (for `c = 0`, `μ = 0` and the density is `0` a.e.: `rnDeriv_zero`).
Source: [[value-change-as-epistemic-update]] §5.4 ("bounded by `c P`")
Kind: P
Fidelity: exact
Hyps: (a) `h : μ ≤ c • P`, `hc : c ≠ 0` -/
theorem rnDeriv_le_of_le_smul (μ P : Measure Ω) [IsFiniteMeasure μ] [SigmaFinite P] {c : ℝ≥0}
    (hc : c ≠ 0) (h : μ ≤ c • P) :
    μ.rnDeriv P ≤ᵐ[P] fun _ => (c : ℝ≥0∞) := by
  have h1 : μ.rnDeriv (c • P) ≤ᵐ[c • P] 1 := Measure.rnDeriv_le_one_of_le h
  have h1' : μ.rnDeriv (c • P) ≤ᵐ[P] 1 :=
    (Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.2 hc)).ae_le h1
  have h2 : μ.rnDeriv (c • P) =ᵐ[P] c⁻¹ • μ.rnDeriv P := Measure.rnDeriv_smul_right μ P hc
  filter_upwards [h1', h2] with x hx1 hx2
  rw [hx2] at hx1
  simp only [Pi.smul_apply, Pi.one_apply] at hx1
  rw [ENNReal.smul_def, ENNReal.coe_inv hc, smul_eq_mul] at hx1
  have hc' : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hc
  calc μ.rnDeriv P x = (c : ℝ≥0∞) * ((c : ℝ≥0∞)⁻¹ * μ.rnDeriv P x) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hc' ENNReal.coe_ne_top, one_mul]
    _ ≤ (c : ℝ≥0∞) * 1 := by gcongr
    _ = c := mul_one _

/-- **The density is unique**: a measurable `U` with `μ(A) = ∫⁻_A U dP` for every measurable `A`
is `dμ/dP` almost everywhere.
Source: [[value-change-as-epistemic-update]] §5.4 (the `U` of E4 is "the" density); mandate E4
Kind: P
Fidelity: exact
Hyps: (a) `hU : Measurable U`, `hrep` -/
theorem density_unique (μ P : Measure Ω) [SigmaFinite P] {U : Ω → ℝ≥0∞} (hU : Measurable U)
    (hrep : ∀ A, MeasurableSet A → μ A = ∫⁻ ω in A, U ω ∂P) :
    U =ᵐ[P] μ.rnDeriv P := by
  have hμ : μ = 0 + P.withDensity U := by
    rw [zero_add]
    exact Measure.ext fun A hA => by rw [withDensity_apply _ hA]; exact hrep A hA
  exact Measure.eq_rnDeriv hU Measure.MutuallySingular.zero_left hμ

end

end Cleanroom.Corrigibility.CorrValueChange
