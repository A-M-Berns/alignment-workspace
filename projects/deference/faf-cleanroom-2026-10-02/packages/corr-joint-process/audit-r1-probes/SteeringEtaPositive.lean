import Cleanroom.Corrigibility.CorrJointProcess.Coined

/-!
# `corr-joint-process` · audit r1 (adversarial) probe: the steering witness at a positive price

Not imported by the library.

`Coined.coined_witnesses` inhabits `SensorImprovingSteering` at overseer harm `η = 0`, where the
predicate's third clause collapses to T4's strict gain and the coined object's one new parameter
(the price the T-agent pays *despite* harming the overseers) is not exercised. The same instance
inhabits it at `η = 1/100 < 71/2500`; the package should ship a positive `η` (or the interval
`η < 71/2500`).
-/

namespace Cleanroom.Corrigibility.CorrJointProcess.AuditR1Adversarial

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep

/-- Sensor-improving steering at a *positive* overseer harm `η = 1/100`: the T-agent still takes
it (`1/100 < 71/2500`). -/
theorem steering_witness_eta_positive :
    SensorImprovingSteering (1 / 50) (1 / 10) (1 / 50) (3 / 5) 1 4 (1 / 100) mem_Icc_1_50 mem_Icc_1_10
      mem_Icc_1_50 mem_Icc_3_5 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [twoState_twoOptionValue, twoState_twoOptionValue]; unfold uPress vSilent; norm_num

/-- The gain itself is `71/2500`, so every `η < 71/2500` works and `η = 71/2500` does not. -/
theorem steering_gain_is_71_2500 :
    (twoState (1 / 50) (1 / 50) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_50 mem_Icc_3_5).twoOptionValue () .cont .stop -
      (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_10 mem_Icc_3_5).twoOptionValue () .cont .stop =
        71 / 2500 :=
  steering_gains.1

end Cleanroom.Corrigibility.CorrJointProcess.AuditR1Adversarial
