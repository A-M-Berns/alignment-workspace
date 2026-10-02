import Cleanroom.Decision.DpTwoLesions.DynWitness

/-!
Audit r2 (adversarial) probe. `prop5_weak_above` (gap `1/2`, start in `(p̂, 1]`, non-tying) ships
no declaration inhabiting its full hypothesis package (ledger Witness cell: "no separate
instance"). This probe supplies it at the doc's `δ = 1/100`, in the same hypothesis-free form as
`prop5_weak_between_at_doc`, and adds what neither `_at_doc` theorem has: an existence lemma
(`traj_isCumul`) showing a cumulative trajectory exists from every start, so the `∀ x,
IsCumulTraj x → …` form is not vacuous. Not imported by the library.
-/

namespace Cleanroom.Decision.DpTwoLesions

open Set Filter Topology

namespace DlParams

/-- The best response is never empty. -/
theorem bestResp_nonempty (P : DlParams ℝ) (p : ℝ) : ∃ b, b ∈ P.bestResp p := by
  by_cases h : P.α < P.Delta p
  · exact ⟨0, fun h' => absurd h' (not_lt.mpr h.le), fun _ => rfl, le_rfl, zero_le_one⟩
  · exact ⟨1, fun _ => rfl, fun h' => absurd h' h, zero_le_one, le_rfl⟩

/-- A cumulative trajectory from `x₀`, choosing some best response at every step. -/
noncomputable def traj (P : DlParams ℝ) (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | t + 1 => cumulStep t (traj P x₀ t) (Classical.choose (bestResp_nonempty P (traj P x₀ t)))

theorem traj_zero (P : DlParams ℝ) (x₀ : ℝ) : traj P x₀ 0 = x₀ := rfl

theorem traj_isCumul (P : DlParams ℝ) (x₀ : ℝ) : P.IsCumulTraj (traj P x₀) :=
  fun t => ⟨_, Classical.choose_spec (bestResp_nonempty P (traj P x₀ t)), rfl⟩

/-- `prop5_weak_above`'s full package at `δ = 1/100`: every cumulative trajectory from a rational
start in `(p̂, 1]` converges to `p̂`. -/
theorem prop5_weak_above_at_doc_probe {x : ℕ → ℝ} (htraj : docCenti.IsCumulTraj x)
    (hrat : ∃ q : ℚ, x 0 = q)
    (hx0 : 23167/41334 + 25 * Real.sqrt 105835 / 20667 < x 0) (hx1 : x 0 ≤ 1) :
    Tendsto x atTop (𝓝 (23167/41334 + 25 * Real.sqrt 105835 / 20667)) := by
  obtain ⟨hr0, hr12, hr1, hset⟩ := prop3_three_at_doc_centi
  obtain ⟨hq1, hq2⟩ := docCenti_Q_roots
  have hgap : 23167/41334 - 25 * Real.sqrt 105835 / 20667 + 1/2 <
      23167/41334 + 25 * Real.sqrt 105835 / 20667 := by
    have := sqrt_105835_bounds.1; linarith
  have hnt := noTie_of_rat_at_doc htraj hrat ⟨by linarith, hx1⟩
  exact docCenti.prop5_weak_above hr0 hr12 hr1 hq1 hq2 hgap htraj (fun t => (hnt t).2) hx0 hx1

/-- An actual trajectory from the smoke label `x₀ = 1`, converging to `p̂`. -/
example : ∃ x : ℕ → ℝ, docCenti.IsCumulTraj x ∧ x 0 = 1 ∧
    Tendsto x atTop (𝓝 (23167/41334 + 25 * Real.sqrt 105835 / 20667)) := by
  refine ⟨traj docCenti 1, traj_isCumul _ _, traj_zero _ _, ?_⟩
  apply prop5_weak_above_at_doc_probe (traj_isCumul _ _) ⟨1, by rw [traj_zero]; norm_num⟩
  · rw [traj_zero]; exact prop3_three_at_doc_centi.2.2.1
  · rw [traj_zero]

end DlParams

end Cleanroom.Decision.DpTwoLesions
