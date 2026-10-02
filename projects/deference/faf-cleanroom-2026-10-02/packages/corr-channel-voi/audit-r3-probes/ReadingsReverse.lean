import Cleanroom.Corrigibility.CorrChannelVoi

/-!
# `corr-channel-voi` · audit r3 (adversarial) probe: the two 1a readings compare *either* way
outside reading (II)'s regime

Not imported by the library.

`selfCheckI_le_selfCheckII` (repair round 2's push) says that *wherever both closed forms hold*
the prose's reading (II) values the button at least as much as the script's reading (I). This
probe shows the scoping is load-bearing, not cosmetic: at
`(ε, e, ρ, α, β, c, h) = (1/5, 4/5, 1/2, 1/5, 1/2, 1, 10)` reading (I) is **inside its own regime**
(both of `selfCheckI_voiGiven_closed`'s conditions discharged, value `6/25` through the closed
form) while reading (II) — outside its four conditions — values the button at **`0`** (through the
regime-free `selfCheckII_voiGiven_eq`): with four fifths of the checks compromised and a check
that says `R` half the time whatever the world, the `R` signal is too weak for the agent to
continue even on silence, so the button adds nothing; in the script's model `R` is decisive in the
right world and the silence cell after `R` is worth `6/25`. So "reading (II) ≥ reading (I)" is a
fact about the joint regime, and reverses outside it. An independent kernel-level computation
(`scan1a.py`, 234,256 grid points) found 8,602 such reversals and no disagreement between the
kernels and the package's two regime-free closed forms.
-/

namespace Cleanroom.Corrigibility.CorrChannelVoi.AuditR3Adversarial

open Finset hiding expect
open Cleanroom.Found.LitDdbFrames.Blackwell Cleanroom.Trust.TtFiniteFrames
  Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep FactoredSpaces
  Cleanroom.Corrigibility.CorrChannelVoi

noncomputable section

theorem m15 : (1/5 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := mem01 (by norm_num) (by norm_num)
theorem m45 : (4/5 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := mem01 (by norm_num) (by norm_num)
theorem m12 : (1/2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := mem01 (by norm_num) (by norm_num)

/-- Reading (I), inside its regime (`εeρh = 4/5 ≤ 4/5 = (1−ε)c`, `εeρ(1−β)h = 2/5 ≤ 16/25`):
`VOI_I(button | check) = (εeρβh − (1−ε)αc)⁺ = (2/5 − 4/25)⁺ = 6/25`. -/
theorem readingI_in_regime :
    voiGiven (relPrior (1/5) (4/5) m15 m45) (selfCheckI (1/2) m12) (relButton (1/5) (1/2) m15 m12)
      (relStakes 1 10) = 6/25 := by
  rw [selfCheckI_voiGiven_closed _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Reading (II) at the same parameters, regime-free: `VOI_II(button | check) = 0`. -/
theorem readingII_zero :
    voiGiven (relPrior (1/5) (4/5) m15 m45) (selfCheckII (1/2) m12) (relButton (1/5) (1/2) m15 m12)
      (relStakes 1 10) = 0 := by
  rw [selfCheckII_voiGiven_eq]
  norm_num

/-- The reversal: `VOI_II < VOI_I` here. -/
theorem readings_reverse :
    voiGiven (relPrior (1/5) (4/5) m15 m45) (selfCheckII (1/2) m12) (relButton (1/5) (1/2) m15 m12)
        (relStakes 1 10) <
      voiGiven (relPrior (1/5) (4/5) m15 m45) (selfCheckI (1/2) m12) (relButton (1/5) (1/2) m15 m12)
        (relStakes 1 10) := by
  rw [readingI_in_regime, readingII_zero]; norm_num

/-- Which of reading (II)'s four conditions fails here: the `R`-branch silence clause
`εeρ(1−β)h ≤ (1−ε)(1−e+eρ)(1−α)c` reads `2/5 ≤ 48/125`, false. -/
theorem readingII_hRs_fails :
    ¬ ((1/5 : ℝ) * (4/5) * (1/2) * (1 - 1/2) * 10 ≤ (1 - 1/5) * (1 - 4/5 + 4/5 * (1/2)) * (1 - 1/5) * 1) := by
  norm_num

end

end Cleanroom.Corrigibility.CorrChannelVoi.AuditR3Adversarial
