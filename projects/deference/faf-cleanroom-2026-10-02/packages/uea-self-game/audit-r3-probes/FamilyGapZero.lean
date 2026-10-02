import Cleanroom.Uea.UeaSelfGame.T3Family

/-!
# Audit round 3 (adversarial) probe: the degenerate corner of `T3Family.family`

`T3Family.family` is a parametric theorem: under three conditions on `(n, θ, δ, g)` the own policy is a
pure fixed point with the trust bound everywhere and gap `g`. At `g = 0` the three conditions hold for
*every* `n`, `θ`, `δ` — the own policy is then optimal (`U(aPol) = 1`) and the statement is the trivial
"an optimal policy with every available conditional at most its own". So the parametric theorem's
hypothesis package has a degenerate instance; its content is in the instantiations the ledger lists
(`limParams`, `oneParams`), which have `g > 0`. Record only; not imported by the library.
-/

namespace Cleanroom.Uea.UeaSelfGame.AuditR3

open T3Family

theorem family_hyps_at_g_zero (P : Params) (hg : P.g = 0) :
    (w P / (w P + P.θ) ≤
      ((1 - P.δ) * (1 - P.g) + P.δ * (P.n * w P)) / ((1 - P.δ) + P.δ * (P.n * w P))) ∧
    P.g ≤ P.δ + P.δ ^ 2 * (1 - P.θ) / (1 - P.δ) ∧
    P.g ≤ P.δ + P.δ ^ 2 * (P.n * w P) / (1 - P.δ) := by
  have hw := w_pos P
  have hθ := P.θ_pos
  have hδ := P.δ_pos
  have h1 : 0 < 1 - P.δ := by linarith [P.δ_lt_one]
  have hθ1 : 0 < 1 - P.θ := by linarith [P.θ_lt_one]
  have hn : (0 : ℝ) ≤ P.n := Nat.cast_nonneg _
  rw [hg]
  refine ⟨?_, ?_, ?_⟩
  · simp only [sub_zero, mul_one]
    rw [div_self (by positivity), div_le_one (by positivity)]
    linarith
  · positivity
  · positivity

/-- … and then `family` says: a fixed point with the trust bound everywhere and gap `0`. -/
theorem family_at_g_zero (P : Params) (hg : P.g = 0) :
    (game P).IsPureFP (aPol P) ∧ (∀ s, (game P).TB ((game P).muSelf (aPol P)) s) ∧
      (game P).Ustar - (game P).U (aPol P) = 0 := by
  obtain ⟨h1, h2, h3⟩ := family_hyps_at_g_zero P hg
  have := family P h1 h2 h3
  rwa [hg] at this

end Cleanroom.Uea.UeaSelfGame.AuditR3
