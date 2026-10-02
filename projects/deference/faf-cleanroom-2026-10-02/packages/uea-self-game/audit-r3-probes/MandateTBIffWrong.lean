import Cleanroom.Uea.UeaSelfGame.T3Family

/-!
# Audit round 3 (adversarial) probe: findings F19's second claim, machine-checked

F19 says the mandate's "`TB_{s_i} ⟺ g ≤ δ + δ²(n−2)w/(1−δ)`" is only the "if" direction: the trust
bound at a deviation situation can hold through the deviation's own conditional `w/(w+θ)`. This probe
exhibits parameters (`n = 1`, `θ = 1/100`, `δ = 1/10`, `g = 1`) where the trust bound holds at the
deviation situation (`w/(w+θ) = 99/101 ≥ 9/10`) while the mandate's cap fails (`g = 1 > 1899/18000`).
(At `g = 1` the own policy is not a fixed point — `TB_succ_iff` is a statement about the trust bound
alone, which is why the second disjunct can be the only true one.) Not imported by the library.
-/

namespace Cleanroom.Uea.UeaSelfGame.AuditR3

open T3Family

noncomputable def Q : Params where
  n := 1
  θ := 1 / 100
  δ := 1 / 10
  g := 1
  θ_pos := by norm_num
  θ_lt_one := by norm_num
  δ_pos := by norm_num
  δ_lt_one := by norm_num
  g_nonneg := by norm_num
  g_le_one := by norm_num

theorem Q_w : w Q = 99 / 200 := by unfold w Q; norm_num
theorem Q_n : ((Q.n : ℕ) : ℝ) = 1 := by simp [Q]

/-- The trust bound holds at the deviation situation `s₁` … -/
theorem TB_holds : (game Q).TB ((game Q).muSelf (aPol Q)) (Fin.succ 0) := by
  rw [TB_succ_iff, Q_w, Q_n]
  right
  show (1 - (1 / 10 : ℝ)) * (99 / 200 + 1 / 100) ≤ 99 / 200
  norm_num

/-- … while the mandate's cap `g ≤ δ + δ²(n−2)w/(1−δ)` (here `n · w`) fails. -/
theorem cap_fails : ¬ (Q.g ≤ Q.δ + Q.δ ^ 2 * (Q.n * w Q) / (1 - Q.δ)) := by
  rw [Q_w, Q_n]
  show ¬ ((1 : ℝ) ≤ 1 / 10 + (1 / 10) ^ 2 * (1 * (99 / 200)) / (1 - 1 / 10))
  norm_num

end Cleanroom.Uea.UeaSelfGame.AuditR3
