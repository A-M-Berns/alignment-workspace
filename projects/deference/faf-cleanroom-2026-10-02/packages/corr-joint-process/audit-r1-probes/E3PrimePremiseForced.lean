import Cleanroom.Corrigibility.CorrJointProcess.Contents

/-!
# `corr-joint-process` · audit r1 (adversarial) probe: E3′'s value-form premise is automatic

Not imported by the library.

`Contents.e3prime` presents `E_π[X] = E_ρ[X]` as a checked coincidence between the builder's
conditional `π = twoState (1/50) (1/100) …` and the successor `ρ = twoState (1/50) (1/10) …`. On
`twoState` the decision variable `X = V(cont) − V(stop)` is a function of `θ` alone, so its
expectation is `(1 − ε)c − εh` for *every* sensor: two instances with the same prior and stakes
agree on `E[X]` whatever their `(α, β)`, and conversely (for `c + h ≠ 0`) equal `E[X]` forces equal
`ε`. So the witness is as non-degenerate as the premise allows — but the premise is not a
coincidence, and E3′ reduces to "the sensor is not determined by the prior". This is a
presentation point (the docstring should say the premise is automatic), not a defect.
-/

namespace Cleanroom.Corrigibility.CorrJointProcess.AuditR1Adversarial

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep

/-- `E[X]` on `twoState` does not depend on the sensor. -/
theorem expect_Xo_sensor_free (ε α α' β β' c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα' : α' ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hβ' : β' ∈ Set.Icc (0 : ℝ) 1) (o : Obs) :
    expect (twoPoint ε hε) ((twoState ε α β c h hε hα hβ).Xo () o .cont .stop) =
      expect (twoPoint ε hε) ((twoState ε α' β' c h hε hα' hβ').Xo () o .cont .stop) := by
  rw [twoState_expect_Xo, twoState_expect_Xo]

/-- Conversely, equal `E[X]` at the same stakes with `c + h ≠ 0` forces equal `ε`: the value-form
premise pins the prior, so E3′ cannot have a witness with distinct priors. -/
theorem expect_Xo_determines_eps (ε ε' α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hε' : ε' ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hch : c + h ≠ 0) (o : Obs)
    (heq : expect (twoPoint ε hε) ((twoState ε α β c h hε hα hβ).Xo () o .cont .stop) =
      expect (twoPoint ε' hε') ((twoState ε' α β c h hε' hα hβ).Xo () o .cont .stop)) :
    ε = ε' := by
  rw [twoState_expect_Xo, twoState_expect_Xo] at heq
  have : (ε - ε') * (c + h) = 0 := by linear_combination -heq
  rcases mul_eq_zero.1 this with h0 | h0
  · linarith
  · exact absurd h0 hch

end Cleanroom.Corrigibility.CorrJointProcess.AuditR1Adversarial
