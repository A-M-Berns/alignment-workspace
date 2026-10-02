import Cleanroom.Uea.UeaSelfGame.T3Family

/-!
# Audit round 3 (adversarial) probe: `T3Family` at `n = 1` reproduces `TightnessT3`'s thresholds

The ledger says the `Fin 3` instances `T3` and `Regimes.GapOne` are "the shape at `n = 1`" of the general
family. `T3Family.lean` and `TightnessT3.lean` compute their conditions independently (the family through
`diracComb` sums over the support; `TightnessT3` through `tab3` and `sum_fin3_arrow`). This probe
instantiates the family's three exact conditions at `n = 1`, `θ = 1/10`, `δ = 1/10` and checks that they
reduce to `TightnessT3`'s `g ≤ 21/110`, `g ≤ 11/100`, `g ≤ 21/200` — the mandate's two exact instances
(`g = 11/100`, `g = 21/200`) fall where the family says. At these parameters the second disjunct of
`TB_succ_iff` (`(1−δ)(w+θ) ≤ w`, i.e. `99/200 ≤ 90/200`) is false, so the family's trust-bound condition at
a deviation situation is exactly `TightnessT3.TB_1_iff`'s. Not imported by the library.
-/

namespace Cleanroom.Uea.UeaSelfGame.AuditR3

open T3Family

/-- `T3(3, 1/10, g)` as a `Params` at `n = 1`. -/
noncomputable def P (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : Params where
  n := 1
  θ := 1 / 10
  δ := 1 / 10
  g := g
  θ_pos := by norm_num
  θ_lt_one := by norm_num
  δ_pos := by norm_num
  δ_lt_one := by norm_num
  g_nonneg := hg0
  g_le_one := hg1

theorem w_eq (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : w (P g hg0 hg1) = 9 / 20 := by
  unfold w P; norm_num

theorem n_eq (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : ((P g hg0 hg1).n : ℝ) = 1 := by simp [P]
theorem θ_eq (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : (P g hg0 hg1).θ = 1 / 10 := rfl
theorem δ_eq (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : (P g hg0 hg1).δ = 1 / 10 := rfl
theorem g_eq (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : (P g hg0 hg1).g = g := rfl

/-- The family's fixed-point condition at `n = 1`, `θ = δ = 1/10` is `TightnessT3.isPureFP_iff`'s. -/
theorem isPureFP_iff_n1 (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (game (P g hg0 hg1)).IsPureFP (aPol (P g hg0 hg1)) ↔ g ≤ 21 / 110 := by
  rw [isPureFP_iff, w_eq, n_eq, θ_eq, δ_eq, g_eq]
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- The family's `s₀` trust-bound condition is `TightnessT3.TB_0_iff`'s. -/
theorem TB_zero_iff_n1 (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (game (P g hg0 hg1)).TB ((game (P g hg0 hg1)).muSelf (aPol (P g hg0 hg1))) 0 ↔ g ≤ 11 / 100 := by
  rw [TB_zero_iff, θ_eq, δ_eq, g_eq]
  norm_num

/-- The family's deviation-situation trust-bound condition is `TightnessT3.TB_1_iff`'s: the second
disjunct is false here (`99/200 ≤ 90/200` fails). -/
theorem TB_succ_iff_n1 (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (t : Fin ((P g hg0 hg1).n + 1)) :
    (game (P g hg0 hg1)).TB ((game (P g hg0 hg1)).muSelf (aPol (P g hg0 hg1))) t.succ ↔
      g ≤ 21 / 200 := by
  rw [TB_succ_iff, w_eq, n_eq, θ_eq, δ_eq, g_eq]
  norm_num

/-- The two mandate instances, through the family: `g = 11/100` is a fixed point with the trust bound at
`s₀` and `g = 21/200` one with the trust bound everywhere (the family's gap is `g`, `T3Family.gap`). -/
theorem instances :
    ((game (P (11 / 100) (by norm_num) (by norm_num))).IsPureFP (aPol _) ∧
      (game (P (11 / 100) (by norm_num) (by norm_num))).TB
        ((game (P (11 / 100) (by norm_num) (by norm_num))).muSelf (aPol _)) 0) ∧
    ((game (P (21 / 200) (by norm_num) (by norm_num))).IsPureFP (aPol _) ∧
      ∀ s, (game (P (21 / 200) (by norm_num) (by norm_num))).TB
        ((game (P (21 / 200) (by norm_num) (by norm_num))).muSelf (aPol _)) s) := by
  refine ⟨⟨(isPureFP_iff_n1 _ _ _).2 (by norm_num), (TB_zero_iff_n1 _ _ _).2 (by norm_num)⟩,
    ⟨(isPureFP_iff_n1 _ _ _).2 (by norm_num), fun s => ?_⟩⟩
  induction s using Fin.cases with
  | zero => exact (TB_zero_iff_n1 _ _ _).2 (by norm_num)
  | succ t => exact (TB_succ_iff_n1 _ _ _ t).2 (by norm_num)

end Cleanroom.Uea.UeaSelfGame.AuditR3
