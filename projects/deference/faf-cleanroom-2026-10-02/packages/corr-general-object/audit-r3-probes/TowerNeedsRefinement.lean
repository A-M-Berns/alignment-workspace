import Cleanroom.Corrigibility.CorrGeneralObject.Inclusion

/-!
# Audit r3 (adversarial) probe — `tower_endorsed`'s refinement hypothesis is load-bearing

`Inclusion.lean`'s docstring for `w10c_tower_witness` claims "with `y` and `g` unrelated the
conclusion would fail". Checked here on the same carrier: the agent signal
`y' ω = (ω ∈ {0, 3})` is *not* refined by `w10cg = (0,0,1,2,2,3)` (the `g`-cell `{3, 4}` straddles
two `y'`-cells), and the conclusion of `tower_endorsed` at `ω₀ = 3` — endorsement of `𝟙_{3,4}`
from `P(· | y' = y' 3)` toward `P(· | {3, 4})` — is false (at world `4`: `0 ≠ (2/3)(1/3)`).

Not imported by the library. Namespace `…AuditR3`.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject.AuditR3

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

noncomputable section

/-- An agent signal not refined by `w10cg`. -/
def y' : Fin 6 → Bool := fun ω => decide (ω = 0 ∨ ω = 3)

theorem y'_cell : cellOf y' (y' 3) = {0, 3} := by decide

theorem y'_mass : 0 < pushMass w10cP (ind (cellOf y' (y' 3))) := by
  rw [pushMass_ind, y'_cell, sum_pair (by decide)]; simp [w10cP]; norm_num

/-- `y'` is not a function of `w10cg`. -/
theorem not_refines : ¬ ∃ f : Fin 4 → Bool, y' = f ∘ w10cg := by
  rintro ⟨f, hf⟩
  have h3 : y' 3 = f (w10cg 3) := congrFun hf 3
  have h4 : y' 4 = f (w10cg 4) := congrFun hf 4
  have e3 : y' 3 = true := by decide
  have e4 : y' 4 = false := by decide
  have g34 : w10cg 3 = w10cg 4 := by decide
  rw [e3, g34] at h3
  rw [e4, ← h3] at h4
  exact Bool.false_ne_true h4

/-- Without refinement, `tower_endorsed`'s conclusion fails. -/
theorem tower_fails_without_refinement :
    ¬ Endorsed (postPush w10cP (ind (cellOf y' (y' 3))) (isKernel_ind _).nonneg y'_mass)
      (ind (cellOf w10cg (w10cg 3)))
      (postPush w10cP (ind (cellOf w10cg (w10cg 3))) (isKernel_ind _).nonneg w10c_gMass) := by
  intro h
  have this := h 4
  unfold pushMass at this
  simp only [postPush_mass] at this
  rw [w10c_gCell, y'_cell] at this
  simp [pushMass, w10cP, ind, Cleanroom.Found.LitDdbFrames.ind, Fin.sum_univ_six] at this <;>
    norm_num at this

end

end Cleanroom.Corrigibility.CorrGeneralObject.AuditR3
