import Cleanroom.Corrigibility.CorrCautionPower.OptionValue

/-!
Audit r2 (adversarial) probe for `corr-caution-power` T9(c1): `optionValue_coarsen_le` (Kind P)
ships no strictness witness (ledger row: Witness "—"; audit r1 §3.1 noted it). Coarsening any
channel to the one-point observation type `Unit` gives option value exactly `0`, so on the
package's own `threeAct`/`perfectChannel` instance the inequality is strict for `0 < ε < 1`.
Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrCautionPower.AuditR2

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect expect_const

/-- The coarsening of any channel to a single observation has option value `0`: the one cell is
the whole prior, so informed = prior. -/
theorem optionValue_coarsen_unit_eq_zero {Ω A₁ A₂ E : Type*} [Fintype Ω] [Fintype A₂]
    [DecidableEq A₂] [Fintype E] (S : ThreeStep Ω A₁ A₂) (C : Channel Ω E) (a : A₁) (o₀ : Obs) :
    optionValue S (C.coarsen (fun _ : E => ())) a o₀ = 0 := by
  have hcell : ∀ b, chanValue S (C.coarsen (fun _ : E => ())) a o₀ () b
      = expect (S.μ a) (S.V a o₀ b) := by
    intro b
    rw [expect_eq_sum_chanValue S C a o₀ b]
    unfold chanValue Channel.coarsen
    simp only [mul_sum, sum_mul]
    rw [sum_comm]
    refine sum_congr ?_ fun e _ => rfl
    ext e; simp
  unfold optionValue informedContinue priorContinue
  rw [Fintype.sum_unique]
  simp only [hcell, sub_self]

/-- On `threeAct` with the perfect channel, coarsening to `Unit` strictly lowers the option value
(from `min{ε, 1 − ε} > 0` to `0`): `optionValue_coarsen_le` is strict here. -/
theorem optionValue_coarsen_strict (ε α β : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    optionValue (threeAct ε α β hε hα hβ) (perfectChannel.coarsen (fun _ : World => ())) () .silent
      < optionValue (threeAct ε α β hε hα hβ) perfectChannel () .silent := by
  rw [optionValue_coarsen_unit_eq_zero]
  exact optionValue_threeAct_pos ε α β hε hα hβ hε0 hε1

end Cleanroom.Corrigibility.CorrCautionPower.AuditR2
