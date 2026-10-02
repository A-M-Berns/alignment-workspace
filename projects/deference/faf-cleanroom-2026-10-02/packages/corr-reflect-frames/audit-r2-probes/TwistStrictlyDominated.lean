import Cleanroom.Corrigibility.CorrReflectFrames.WitnessesF

/-!
Audit r2 (adversarial) probe — T9(e) (`Dominance.lean`) is not an equality in disguise.

`twist_choice_le_refineFrame_value` (kind C, whole family) ships no instance; this probe
exhibits a strict one on `π4`/`branch` at `l = 1/2` with the two-act world payoff
`u₀ = (0, 1, 0, 3)`, `u₁ = (1, 0, 0, 0)` and the argmax tie-break: the twisted successor picks
`u₀` on branch `A` (its row `(1/2, 1/4, 1/16, 3/16)` is pulled toward the prior, where `u₀`'s
`3` at world `3` counts), while the refinement's cellwise maximizer picks `u₁` there
(`E_{π(·|A)} u₁ = 2/3 > 1/3`); realized payoffs `31/24 < 35/24`. Nothing here is imported by the
library.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames.AuditR2

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames
  Cleanroom.Corrigibility.CorrReflectFrames.Witnesses

noncomputable section

def uT : Fin 2 → Fin 4 → ℝ := ![![0, 1, 0, 3], ![1, 0, 0, 0]]

/-- Argmax tie-break: act `0` unless act `1` is strictly better under the row. -/
def chooseT (ρ : Fin 4 → ℝ) : Fin 2 := if E ρ (uT 0) < E ρ (uT 1) then 1 else 0

abbrev tw : Frame (Fin 4) := twist π4 π4_mem branch (1 / 2) (by norm_num) (by norm_num)

theorem tw_rows : tw.P 0 = ![1 / 2, 1 / 4, 1 / 16, 3 / 16] ∧ tw.P 1 = ![1 / 2, 1 / 4, 1 / 16, 3 / 16] ∧
    tw.P 2 = ![1 / 6, 1 / 12, 3 / 16, 9 / 16] ∧ tw.P 3 = ![1 / 6, 1 / 12, 3 / 16, 9 / 16] := by
  obtain ⟨hr0, hr2⟩ := frame4_rows
  obtain ⟨hr1, hr3⟩ := frame4_rows'
  have e0 : condRow π4 branch 0 = ![2 / 3, 1 / 3, 0, 0] := hr0
  have e2 : condRow π4 branch 2 = ![0, 0, 1 / 4, 3 / 4] := hr2
  have e1 : condRow π4 branch 1 = ![2 / 3, 1 / 3, 0, 0] := hr1.trans hr0
  have e3 : condRow π4 branch 3 = ![0, 0, 1 / 4, 3 / 4] := hr3.trans hr2
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [tw, twist_P, e0, e1, e2, e3]; funext v; fin_cases v <;> simp [π4] <;> norm_num)

theorem twist_choice_A : chooseT (tw.P 0) = 0 ∧ chooseT (tw.P 1) = 0 := by
  obtain ⟨h0, h1, -, -⟩ := tw_rows
  constructor <;> (simp only [chooseT, h0, h1, uT, E, Fin.sum_univ_four, Matrix.cons_val]; norm_num)

theorem twist_choice_B : chooseT (tw.P 2) = 0 ∧ chooseT (tw.P 3) = 0 := by
  obtain ⟨-, -, h2, h3⟩ := tw_rows
  constructor <;> (simp only [chooseT, h2, h3, uT, E, Fin.sum_univ_four, Matrix.cons_val]; norm_num)

/-- **The twisted successor is strictly dominated on this instance**: twist payoff `31/24`,
refinement's cellwise-maximizer value `35/24`. -/
theorem twist_strictly_dominated :
    ∑ w, π4 w * uT (chooseT (tw.P w)) w = 31 / 24 ∧
      ∑ w, π4 w * univ.sup' hA2 (fun a => E ((refineFrame π4 π4_mem.1 branch).P w) (uT a)) =
        35 / 24 ∧
      (31 / 24 : ℝ) < 35 / 24 := by
  obtain ⟨cA0, cA1⟩ := twist_choice_A
  obtain ⟨cB2, cB3⟩ := twist_choice_B
  obtain ⟨hr0, hr2⟩ := frame4_rows
  obtain ⟨hr1, hr3⟩ := frame4_rows'
  refine ⟨?_, ?_, by norm_num⟩
  · rw [Fin.sum_univ_four, cA0, cA1, cB2, cB3]
    simp [uT, π4]; norm_num
  · have e : ∀ w, (refineFrame π4 π4_mem.1 branch).P w = frame4.P w := fun _ => rfl
    simp only [e, Fin.sum_univ_four, hr1, hr3, hr0, hr2, sup'_fin2, uT, E]
    simp [π4, max_def]
    norm_num

end

end Cleanroom.Corrigibility.CorrReflectFrames.AuditR2
