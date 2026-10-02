import Cleanroom.Bli.UdtBliLearning.EpsCorr

/-!
# Audit r3 (fidelity) probe: the source's *threshold* form of the exact clause is TRUE on a fixed
prior, in the choice reading

bli-soto-b-046 (Notion l. 368): "for each environment, there is some epsilon such that if the
agent's belief in acausal correlations is below epsilon, … then the performance of UDT will
eventually be optimal in that environment". The quantifier is a threshold `ε` chosen *after* the
environment. `ExactAsymptoticClause` (EpsCorr.lean) reshapes it as `ε_n → 0` over an arbitrary
sequence of priors (stakes included), and `not_exactAsymptoticClause` refutes that reshaping with a
family whose home-value gap `1/(2(n+1))` and stakes vanish.

This probe checks the claim behind audit r3 B1: with the environment (a fixed `FiniteBLIPrior`,
two actions) fixed first, there IS an `ε > 0` such that `CorrBounded P T ε` (with the standing
positivity / boundedness hypotheses of the finite form) forces every one-step choice at `T` to be an
updateful choice — the source's threshold sentence in the *choice* reading, true outright. So the
refutation in the library is a refutation of the `ε_n → 0` reshaping along sequences with vanishing
home-value gaps, not of the source's sentence under its own quantifier. Not imported by the library.
-/

set_option autoImplicit false

namespace Cleanroom.Bli.UdtBliLearning.AuditR3

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)}

/-- **Fixed prior, two actions: a threshold `ε` exists below which every one-step choice is an
updateful choice.** If the two home values at `T` coincide, every action is updateful and any `ε`
works; otherwise their gap `g > 0` is the minimal gap, and `ε := g ρ / (2C)` makes the slack
`δ(ε) = g/2 < g`, so the finite form `eps_corr_implies_eps_updateful` forces exactness. -/
theorem fixed_prior_threshold (P : FiniteBLIPrior 𝒮 m 𝒟 Bool) (T : ↥𝒟) (M ρ : ℚ)
    (hM : 0 ≤ M) (hρ : 0 < ρ) (hpol : ∀ c, 0 < P.ppMass T c) (hU : ∀ ω, |P.U ω| ≤ M)
    (hρa : ∀ a, P.IsOneStepChoice T a → ρ ≤ P.branchProb T T a) :
    ∃ ε : ℚ, 0 < ε ∧
      (CorrBounded P T ε → ∀ a, P.IsOneStepChoice T a → P.IsUpdatefulChoice T a) := by
  set C : ℚ := 1 + (2 * (Fintype.card ↥𝒟 : ℚ) + 1) * M with hC
  have hCpos : 0 < C := by
    have : 0 ≤ (2 * (Fintype.card ↥𝒟 : ℚ) + 1) * M := mul_nonneg (by positivity) hM
    linarith
  by_cases heq : P.homeEU T true = P.homeEU T false
  · refine ⟨1, one_pos, fun _ a _ b => ?_⟩
    cases a <;> cases b <;> simp [heq]
  · set g : ℚ := |P.homeEU T true - P.homeEU T false| with hg
    have hgpos : 0 < g := abs_pos.mpr (sub_ne_zero.mpr heq)
    refine ⟨g * ρ / (2 * C), by positivity, fun hcorr a ha b => ?_⟩
    have h := eps_corr_implies_eps_updateful P T (g * ρ / (2 * C)) M ρ (by positivity) hM hρ hpol
      hcorr hU a ha (hρa a ha) b
    unfold updatefulSlack at h
    have hslack : g * ρ / (2 * C) * (1 + (2 * (Fintype.card ↥𝒟 : ℚ) + 1) * M) / ρ = g / 2 := by
      rw [← hC]; field_simp
    rw [hslack] at h
    by_contra hnle
    have hlt := not_le.mp hnle
    have hge : g ≤ P.homeEU T b - P.homeEU T a := by
      cases a <;> cases b
      · exact absurd hlt (lt_irrefl _)
      · rw [hg, abs_of_pos (sub_pos.mpr hlt)]
      · rw [hg, abs_of_neg (sub_neg.mpr hlt)]; linarith
      · exact absurd hlt (lt_irrefl _)
    linarith

end Cleanroom.Bli.UdtBliLearning.AuditR3
