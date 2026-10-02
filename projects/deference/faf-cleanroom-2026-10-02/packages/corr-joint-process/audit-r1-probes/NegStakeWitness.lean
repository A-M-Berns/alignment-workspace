import Cleanroom.Corrigibility.CorrJointProcess.Faking

/-!
# `corr-joint-process` · audit r1 (adversarial) probe: T21(ii)'s witness does not inhabit its theorem

Not imported by the library.

The ledger's T21 row names `a3b_witness` as the witness of `dodged_of_neg_stake`. But A3b's stake
is `h = +1/100 > 0` (legitimacy-general Statement 4(b): "A3b at 19/20 (h = 1/100, c = 9/10,
threshold 90/91)"): the push is resisted because the threshold `90/91` exceeds `p = 19/20`, not
because the stake is negative. `dodged_of_neg_stake` needs `hL < 0`, and `worldIndexedStake` —
the object that "can be negative" — is defined and used nowhere. This probe supplies the missing
witness: a world-indexed stake that *is* negative, and the dodge at `p = 1` on it.
-/

namespace Cleanroom.Corrigibility.CorrJointProcess.AuditR1Adversarial

/-- A3b's stake is positive: it is not an instance of `dodged_of_neg_stake`'s `hneg`. -/
theorem a3b_stake_not_negative : ¬ ((1 / 100 : ℝ) < 0) := by norm_num

/-- A negative world-indexed stake: an authentic process that errs on content with probability
`w = 1/2`, harm-if-authentic `h = 1/100`, cost-of-error `c_err = 9/10`: `h_L = −89/200`. -/
theorem worldIndexedStake_negative :
    worldIndexedStake (1 / 2) (1 / 100) (9 / 10) = -(89 / 200) ∧ worldIndexedStake (1 / 2) (1 / 100) (9 / 10) < 0 := by
  unfold worldIndexedStake; norm_num

/-- On that stake the push is dodged at `p = 1` (with `c = 9/10`), as `dodged_of_neg_stake` says. -/
theorem dodged_at_certainty :
    0 < 1 * (-(worldIndexedStake (1 / 2) (1 / 100) (9 / 10))) + (1 - 1) * (9 / 10 : ℝ) :=
  dodged_of_neg_stake 1 (9 / 10) _ worldIndexedStake_negative.2 ⟨by norm_num, by norm_num⟩ (by norm_num)
    (by norm_num)

end Cleanroom.Corrigibility.CorrJointProcess.AuditR1Adversarial
