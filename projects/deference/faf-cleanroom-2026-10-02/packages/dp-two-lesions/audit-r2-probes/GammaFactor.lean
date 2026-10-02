import Cleanroom.Decision.DpTwoLesions.Laws

/-!
# Audit r2 (fidelity) probe: the general-`γ` penalty is `(γ₁ − γ₀)` times the doc's, exactly

F3 answers the mandate's T20 second extension ("say whether the wiki's factor `(γ₁ − γ₀)` is
right") with "the endpoint values carry the factor exactly, but the quadratic's middle
coefficient does not factor through it". This probe shows the factor is exact on all of
`[0, 1]`: `Δ_P(p) = (γ₁ − γ₀) · Δ_{P'}(p)` where `P'` is `P` with `γ = (1, 0)` and everything
else unchanged. So general-`γ` Proposition 3 is the doc's Proposition 3 with `C` replaced by
`C(γ₁ − γ₀)`; the quadratic's middle coefficient fails to factor only because `Q = (Δ − α)·D`
carries the `−α·D` term, which is not what the wiki guessed about.
Not imported by the library.
-/

namespace Cleanroom.Decision.DpTwoLesions

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace DlParams

/-- `P` with the doc's cancer law `γ = (1, 0)`, all other parameters unchanged. -/
def docGamma (P : DlParams K) : DlParams K :=
  { P with γ₁ := 1, γ₀ := 0, γ₀_nonneg := le_rfl, γ₀_le_γ₁ := zero_le_one, γ₁_le_one := le_rfl }

theorem docGamma_ρ (P : DlParams K) : P.docGamma.ρ = P.ρ := rfl
theorem docGamma_ρA (P : DlParams K) : P.docGamma.ρA = P.ρA := rfl
theorem docGamma_δL (P : DlParams K) : P.docGamma.δL = P.δL := rfl
theorem docGamma_δA (P : DlParams K) : P.docGamma.δA = P.δA := rfl
theorem docGamma_γ₁ (P : DlParams K) : P.docGamma.γ₁ = 1 := rfl
theorem docGamma_γ₀ (P : DlParams K) : P.docGamma.γ₀ = 0 := rfl
theorem docGamma_β (P : DlParams K) : P.docGamma.β = P.β := rfl
theorem docGamma_kappa (P : DlParams K) : P.docGamma.kappa = P.kappa := rfl

/-- The doc-law conditionals at the same `ρ, ρA, δL, δA`. -/
theorem docGamma_condSmoke (P : DlParams K) (p : K) :
    P.docGamma.condSmoke p = (P.ρ * P.δL + P.ρ * (1 - P.δL) * p) / (P.ρ * P.δL + P.kappa * p) := by
  unfold condSmoke kcC
  simp only [docGamma_ρ, docGamma_ρA, docGamma_δL, docGamma_δA, docGamma_γ₁, docGamma_γ₀,
    docGamma_kappa, mul_one, mul_zero, add_zero]

theorem docGamma_condAbstain (P : DlParams K) (p : K) :
    P.docGamma.condAbstain p =
      (P.ρ * (1 - P.δL) * (1 - p)) / (P.ρA * P.δA + P.kappa * (1 - p)) := by
  unfold condAbstain kcC
  simp only [docGamma_ρ, docGamma_ρA, docGamma_δL, docGamma_δA, docGamma_γ₁, docGamma_γ₀,
    docGamma_kappa, mul_one, mul_zero, add_zero, zero_add]

/-- **The wiki's factor is exact**: on `[0, 1]`, `Δ_P(p) = (γ₁ − γ₀) · Δ_{P'}(p)` with `P'` the
same parameters at `γ = (1, 0)`. -/
theorem Delta_eq_gamma_factor (P : DlParams K) (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    P.Delta p = (P.γ₁ - P.γ₀) * P.docGamma.Delta p := by
  have hd1 := (P.denomSmoke_pos p h0 h1).ne'
  have hd2 := (P.denomAbstain_pos p h0 h1).ne'
  rw [Delta_eq P p h0 h1, Delta_eq P.docGamma p h0 h1, docGamma_condSmoke, docGamma_condAbstain,
    docGamma_β]
  unfold condSmoke condAbstain
  have key1 : P.ρ * P.δL * P.γ₁ + P.kcC * p =
      P.γ₀ * (P.ρ * P.δL + P.kappa * p) + (P.γ₁ - P.γ₀) * (P.ρ * P.δL + P.ρ * (1 - P.δL) * p) := by
    unfold kappa kcC; ring
  have key2 : P.ρA * P.δA * P.γ₀ + P.kcC * (1 - p) =
      P.γ₀ * (P.ρA * P.δA + P.kappa * (1 - p)) + (P.γ₁ - P.γ₀) * (P.ρ * (1 - P.δL) * (1 - p)) := by
    unfold kappa kcC; ring
  rw [key1, key2, add_div, add_div, mul_div_cancel_right₀ _ hd1, mul_div_cancel_right₀ _ hd2,
    mul_div_assoc, mul_div_assoc]
  ring

/-- Consequently the general-`γ` crossings are the doc's crossings with `C ↦ C(γ₁ − γ₀)`:
`Δ_P(p) = α ↔ Δ_{P'}(p) = α/(γ₁ − γ₀)` when `γ₀ < γ₁`. -/
theorem crossing_iff_gamma_factor (P : DlParams K) (hγ : P.γ₀ < P.γ₁) (p : K) (h0 : 0 ≤ p)
    (h1 : p ≤ 1) : P.Delta p = P.α ↔ P.docGamma.Delta p = P.α / (P.γ₁ - P.γ₀) := by
  rw [Delta_eq_gamma_factor P p h0 h1]
  have hne : P.γ₁ - P.γ₀ ≠ 0 := (sub_pos.mpr hγ).ne'
  rw [eq_div_iff hne]
  constructor <;> intro h <;> linarith [h]

end DlParams

end Cleanroom.Decision.DpTwoLesions
