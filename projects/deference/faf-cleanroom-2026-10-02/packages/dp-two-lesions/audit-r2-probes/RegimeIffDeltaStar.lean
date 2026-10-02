import Cleanroom.Decision.DpTwoLesions.DeltaStar

/-!
Audit r2 (adversarial) probe. The package's `docP_discrim_pos_iff` gives `discrim > 0 ↔ δ < δ*`
only on `(0, 1/5)` and the ledger says the vertex condition of the three-fixed-point regime "is
checked only at the instance grips". Numerically (auditor's table) the discriminant is positive
again for `δ ≳ 0.2` with the vertex beyond `1`, so the restriction is necessary for the
discriminant statement, but the regime itself is `δ < δ*` on all of `(0, 1]`. This probe closes
that: the vertex `−qB/(2qA) = (1 + 56δ/5 + 4δ²/25) / (2(1 − 2δ/5)²)` lies in `(0, 1)` for
`δ ≤ 3/100` and is `≥ 1` for `δ ≥ 1/5`, hence (with `prop3_three_iff`) the three-fixed-point
regime at the doc's parameters holds **iff** `δ < δ*`, for every grip `δ ∈ (0, 1]`.
Not imported by the library.
-/

namespace Cleanroom.Decision.DpTwoLesions

open Set

namespace DlParams

theorem docP_negqB (δ : ℝ) (h0 : 0 < δ) (h1 : δ ≤ 1) :
    -(docP δ h0 h1).qB = 1 + 56/5 * δ + 4/25 * δ ^ 2 := by
  simp only [qB, kappa, kcC, docP]; ring

theorem docP_twoqA (δ : ℝ) (h0 : 0 < δ) (h1 : δ ≤ 1) :
    2 * (docP δ h0 h1).qA = 2 * (1 - 2/5 * δ) ^ 2 := by
  simp only [qA, kappa, docP]; ring

theorem docP_vertex_small (δ : ℝ) (h0 : 0 < δ) (h1 : δ ≤ 1) (h3 : δ ≤ 3/100) :
    0 < -(docP δ h0 h1).qB / (2 * (docP δ h0 h1).qA) ∧
    -(docP δ h0 h1).qB / (2 * (docP δ h0 h1).qA) < 1 := by
  rw [docP_negqB, docP_twoqA]
  have hk : 0 < 1 - 2/5 * δ := by linarith
  have hA : 0 < 2 * (1 - 2/5 * δ) ^ 2 := by positivity
  constructor
  · apply div_pos _ hA; nlinarith [sq_nonneg δ]
  · rw [div_lt_one hA]; nlinarith [sq_nonneg δ]

theorem docP_vertex_large (δ : ℝ) (h0 : 0 < δ) (h1 : δ ≤ 1) (h5 : 1/5 ≤ δ) :
    1 ≤ -(docP δ h0 h1).qB / (2 * (docP δ h0 h1).qA) := by
  rw [docP_negqB, docP_twoqA]
  have hk : 0 < 1 - 2/5 * δ := by linarith
  have hA : 0 < 2 * (1 - 2/5 * δ) ^ 2 := by positivity
  rw [le_div_iff₀ hA]
  have hsq : δ ^ 2 ≤ δ := by nlinarith
  nlinarith

/-- **The three-fixed-point regime at the doc's parameters is exactly `δ < δ*`, on all of
`(0, 1]`** — the vertex half added to the package's discriminant half. -/
theorem docP_regime_iff_deltaStar :
    ∃ δs : ℝ, 2785/100000 < δs ∧ δs < 2786/100000 ∧
      ∀ δ (h0 : 0 < δ) (h1 : δ ≤ 1),
        ((∃ p₁ p₂ : ℝ, 0 < p₁ ∧ p₁ < p₂ ∧ p₂ < 1 ∧ (docP δ h0 h1).fixedPts = {0, p₁, p₂}) ↔
          δ < δs) := by
  obtain ⟨δs, hlo, hhi, hiff⟩ := docP_discrim_pos_iff
  refine ⟨δs, hlo, hhi, fun δ h0 h1 => ?_⟩
  have hH := docP_hypH δ h0 h1
  rw [(docP δ h0 h1).prop3_three_iff hH]
  rcases lt_or_ge δ (1/5) with h5 | h5
  · constructor
    · rintro ⟨hd, -, -⟩; exact (hiff δ h0 h1 h5).mp hd
    · intro hδ
      have h3 : δ ≤ 3/100 := by linarith
      obtain ⟨v0, v1⟩ := docP_vertex_small δ h0 h1 h3
      exact ⟨(hiff δ h0 h1 h5).mpr hδ, v0, v1⟩
  · constructor
    · rintro ⟨-, -, v1⟩
      exact absurd (docP_vertex_large δ h0 h1 h5) (not_le.mpr v1)
    · intro hδ; exfalso; linarith

end DlParams

end Cleanroom.Decision.DpTwoLesions
