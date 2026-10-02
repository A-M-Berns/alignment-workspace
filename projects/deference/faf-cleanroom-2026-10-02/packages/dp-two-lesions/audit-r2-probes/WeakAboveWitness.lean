import Cleanroom.Decision.DpTwoLesions.Cumulative

/-!
# Audit r2 (fidelity) probe: `prop5_weak_above`'s full hypothesis package is inhabited

`prop5_weak_above` (repair round 1) ships no witness; its ledger row says the `between` witness
"transfers". This probe (i) builds a cumulative trajectory from *any* start by the greedy
selection (`greedyTraj`), so every `IsCumulTraj` hypothesis in the package is non-vacuous, and
(ii) proves the hypothesis-free `at_doc` form for `x₀ > p̂`: every cumulative trajectory of
`docCenti` from a rational start in `(p̂, 1]` converges to `p̂`. With (i) at `x₀ = 99/100` the
full package (regime, gap `1/2`, non-tying, start above `p̂`) is inhabited.
Not imported by the library.
-/

namespace Cleanroom.Decision.DpTwoLesions

open Set Filter Topology

namespace DlParams

/-- The greedy cumulative trajectory from `x₀`: `b_t = 0` when `α < Δ(x_t)`, else `1`. -/
noncomputable def greedyTraj (P : DlParams ℝ) (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | t + 1 => cumulStep t (greedyTraj P x₀ t) (if P.α < P.Delta (greedyTraj P x₀ t) then 0 else 1)

theorem greedyTraj_zero (P : DlParams ℝ) (x₀ : ℝ) : P.greedyTraj x₀ 0 = x₀ := rfl

/-- The greedy trajectory is a cumulative trajectory, from every start (ties resolved to `1`,
which lies in `β = [0, 1]`). -/
theorem greedyTraj_isCumulTraj (P : DlParams ℝ) (x₀ : ℝ) : P.IsCumulTraj (P.greedyTraj x₀) := by
  intro t
  refine ⟨if P.α < P.Delta (P.greedyTraj x₀ t) then 0 else 1, ?_, rfl⟩
  unfold bestResp
  simp only [Set.mem_setOf_eq]
  split_ifs with h
  · exact ⟨fun h' => absurd h' (not_lt.mpr h.le), fun _ => rfl, le_rfl, zero_le_one⟩
  · exact ⟨fun _ => rfl, fun h' => absurd h' h, zero_le_one, le_rfl⟩

/-- `prop5_weak_above` at the doc's `δ = 1/100`, hypothesis-free: every cumulative trajectory
from a rational start in `(p̂, 1]` converges to `p̂`. -/
theorem prop5_weak_above_at_doc_probe {x : ℕ → ℝ} (htraj : docCenti.IsCumulTraj x)
    (hrat : ∃ q : ℚ, x 0 = q)
    (hx0 : 23167/41334 + 25 * Real.sqrt 105835 / 20667 < x 0) (hx1 : x 0 ≤ 1) :
    Tendsto x atTop (𝓝 (23167/41334 + 25 * Real.sqrt 105835 / 20667)) := by
  obtain ⟨hr0, hr12, hr1, hset⟩ := prop3_three_at_doc_centi
  have hH := docP_hypH (1/100 : ℝ) (by norm_num) (by norm_num)
  have hmem : ∀ p ∈ docCenti.fixedPts, p = 0 ∨ (0 < p ∧ p < 1 ∧ docCenti.Q p = 0) := by
    intro p hp
    rw [docCenti.prop3_fixedPoints_eq hH] at hp
    simpa using hp
  have hq1 : docCenti.Q (23167/41334 - 25 * Real.sqrt 105835 / 20667) = 0 := by
    rcases hmem (23167/41334 - 25 * Real.sqrt 105835 / 20667) (by rw [hset]; simp) with h | h
    · exact absurd h hr0.ne'
    · exact h.2.2
  have hq2 : docCenti.Q (23167/41334 + 25 * Real.sqrt 105835 / 20667) = 0 := by
    rcases hmem (23167/41334 + 25 * Real.sqrt 105835 / 20667) (by rw [hset]; simp) with h | h
    · exact absurd h (by linarith)
    · exact h.2.2
  have hgap : 23167/41334 - 25 * Real.sqrt 105835 / 20667 + 1/2 <
      23167/41334 + 25 * Real.sqrt 105835 / 20667 := by
    have := sqrt_105835_bounds.1; linarith
  have hnt := noTie_of_rat_at_doc htraj hrat ⟨by linarith, hx1⟩
  exact docCenti.prop5_weak_above hr0 hr12 hr1 hq1 hq2 hgap htraj (fun t => (hnt t).2) hx0 hx1

/-- The package is inhabited: the greedy trajectory from `99/100 > p̂` converges to `p̂`. -/
theorem prop5_weak_above_inhabited :
    ∃ x : ℕ → ℝ, docCenti.IsCumulTraj x ∧ x 0 = 99/100 ∧
      23167/41334 + 25 * Real.sqrt 105835 / 20667 < x 0 ∧
      Tendsto x atTop (𝓝 (23167/41334 + 25 * Real.sqrt 105835 / 20667)) := by
  have hs := sqrt_105835_bounds
  have hlt : 23167/41334 + 25 * Real.sqrt 105835 / 20667 < 99/100 := by linarith [hs.2]
  refine ⟨docCenti.greedyTraj (99/100), docCenti.greedyTraj_isCumulTraj _, greedyTraj_zero _ _,
    by rw [greedyTraj_zero]; exact hlt, ?_⟩
  exact prop5_weak_above_at_doc_probe (docCenti.greedyTraj_isCumulTraj _)
    ⟨99/100, by rw [greedyTraj_zero]; norm_num⟩ (by rw [greedyTraj_zero]; exact hlt)
    (by rw [greedyTraj_zero]; norm_num)

end DlParams

end Cleanroom.Decision.DpTwoLesions
