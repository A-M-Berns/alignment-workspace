import Cleanroom.Corrigibility.CorrJointProcess.Buttons

/-!
# `corr-joint-process` · audit r1 (adversarial) probe: what `planVoi_ratio_unbounded` says

Not imported by the library.

Two checks on T5(b), load-bearing 2.

1. **The mechanism.** `planVoi` on the match menu is *bounded* (`≤ 10` for every `n`), so the
   unbounded ratio of `planVoi_ratio_unbounded` comes entirely from the press-sensor bound
   `min(10/(n+1), 2n/(n+1)) → 0` — the chosen plan is almost surely wrong for large `n`. For
   `n ≥ 6` the uninformed agent's best plan is the null plan (every named plan has negative prior
   expectation), so the bound is that of a plan the uninformed agent would not choose. The
   source (P.4′, adv A.9.1) says exactly "the ratio grows without bound", so the Lean is faithful;
   this is recorded so the ratio is not read as "VOI(θ) grows".
2. **The bound is the parent's object.** The package compares `planVoi` against the bare number
   `min((1 − n/(n+1))·10, (n/(n+1))·2)` (report, deviation 5). The number *is* the parent's
   `twoState_voiButton2_le_perfectInfo` at `ε = n/(n+1)`, `c = 10`, `h = 2`, for every sensor
   `(α, β)` — one line, shown here, with the ratio statement restated over the parent's
   `voiButton2` (for `0 ≤ M`). The package should ship this corollary.
-/

namespace Cleanroom.Corrigibility.CorrJointProcess.AuditR1Adversarial

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

/-- `planVoi` on the match menu never exceeds `10`: the numerator of the ratio is bounded. -/
theorem planVoi_le_ten (n : ℕ) :
    planVoi (Distr.uniform : Distr (Fin (n + 1))) matchValue ≤ 10 := by
  rw [planVoi_uniform_match]
  linarith [le_max_right ((10 - 2 * (n : ℝ)) / ((n : ℝ) + 1)) 0]

/-- For `n ≥ 6` every named plan has negative prior expectation: the uninformed agent takes
the null plan, and the "chosen plan's" press-sensor bound is for a plan it would not choose. -/
theorem uninformed_prefers_null (n : ℕ) (hn : 6 ≤ n) :
    (10 - 2 * (n : ℝ)) / ((n : ℝ) + 1) < 0 := by
  have hn' : (6 : ℝ) ≤ n := by exact_mod_cast hn
  apply div_neg_of_neg_of_pos <;> linarith

/-- `n/(n+1) ∈ [0, 1]`. -/
lemma ratio_mem_Icc (n : ℕ) : (n : ℝ) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨div_nonneg (Nat.cast_nonneg n) (by positivity), (div_le_one (by positivity)).2 (by linarith)⟩

/-- **The bound is the parent's object**: for every sensor `(α, β)`, the chosen plan's button on
`twoState (n/(n+1)) α β 10 2` is worth at most the number the package compares against. -/
theorem bound_is_parent (n : ℕ) (α β : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    (twoState ((n : ℝ) / ((n : ℝ) + 1)) α β 10 2 (ratio_mem_Icc n) hα hβ).voiButton2 () .press .cont .stop ≤
      min ((1 - (n : ℝ) / (n + 1)) * 10) ((n : ℝ) / (n + 1) * 2) :=
  twoState_voiButton2_le_perfectInfo _ _ _ _ _ (ratio_mem_Icc n) hα hβ (by norm_num) (by norm_num) .press

/-- **T5(b) over the parent's `voiButton2`**: for every `M ≥ 0` some plan set makes the
plan-choice value of `θ` exceed `M` times the value of *any* press-sensor for the chosen plan. -/
theorem ratio_unbounded_parent (M : ℝ) (hM : 0 ≤ M) :
    ∃ n : ℕ, ∀ (α β : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1),
      M * (twoState ((n : ℝ) / ((n : ℝ) + 1)) α β 10 2 (ratio_mem_Icc n) hα hβ).voiButton2 () .press .cont .stop <
        planVoi (Distr.uniform : Distr (Fin (n + 1))) matchValue := by
  obtain ⟨n, hn⟩ := planVoi_ratio_unbounded M
  refine ⟨n, fun α β hα hβ => ?_⟩
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (bound_is_parent n α β hα hβ) hM) hn

end Cleanroom.Corrigibility.CorrJointProcess.AuditR1Adversarial
