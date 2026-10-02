import Cleanroom.Fa.FaForcingTrader.Witnesses

/-!
# `fa-forcing-trader` · audit r3 (adversarial) · probe: T4 on a varying, undecided family

Evidence for `fa-forcing-trader-audit-r3-adversarial.md`. **Not imported by the library.**

Repair round 2 showed the T4 witness `A.hSideBridge_w2` (constant family `X ≡ 𝟙(atom k)`) has a
return that provably vanishes with no trader (`hSideBridge_w2_return_tendsto_zero`), and the
report says a witness exercising the return "needs an e.c. certificate for a varying indicator
family and an argument that the return is not Cesàro-null — neither available cheaply". The first
half is wrong: li-quote-lane's `cleanX n = 𝟙(witnessQuoted 0 n)` is a varying indicator family
**with** its certificate `cleanX_codes`, already imported by `A/Witnesses.lean` and used there
for the T3/T6/T7 same-market instances. This probe inhabits T4's full package with it on the
paper LIA (`hSideBridge_clean`), and shows the per-day return is the one-day price change of a
*fresh* sentence `ψ_n = witnessQuoted 0 n ⋏ ∼∼witnessQuoted 0 n` (`cleanX_return_eq`), which FAF's
`thm:con` (a fixed sentence's price converges) does not make vanish. Whether it does vanish for
another reason — e.g. the paper LIA pricing a not-yet-enumerated atom by a default on both days —
is **not** checked here; the probe only removes the "no certificate" obstacle and the
constant-family triviality. Grade of the new instance: N+ package, N− content with the weaker
caveat "non-vanishing not shown" (the package's round-0 grading of `w2`, now true of a varying
family).
-/

namespace Cleanroom.Fa.FaForcingTrader.AuditR3

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Cleanroom.Fa.FaForcingTrader
  Filter Topology

/-- **T4's full package on the paper LIA with the varying undecided family `cleanX`**: a real
inductor, FAF's real trader on the day-`n` meshes of `𝟙(witnessQuoted 0 n)`, lookahead `n + 1`,
schedule `2, 4, 6, …`, the bare schedule indicator as the weighting. -/
theorem hSideBridge_clean :
    WeightedApprox (fun n => (scheduleIndicator (linearSchedule 0) n).denote A.selfH)
      (fun n => (bundle cleanX n).price A.selfH (succDeferral.f n))
      (fun n => (cleanX n).expect A.selfH n) :=
  haveI := w1_inductorH
  hSideBridge cleanX_codes (paperDP_hworld 𝗜𝚺₁) (windowDisjoint_succ_linear 0)
    (scheduleIndicator_pgenerable _) (fun n hn => scheduleIndicator_supported _ _ n hn)
    (scheduleIndicator_divergent _ _)

/-- The round-trip return on `cleanX` is the one-day price change of the day-`n` sentence
`witnessQuoted 0 n ⋏ ∼∼witnessQuoted 0 n` — a different sentence each day, so `thm:con` does not
apply (contrast `bundle_indicator_return_tendsto_zero`, where the sentence is fixed). -/
theorem cleanX_return_eq (n : ℕ) :
    (bundle cleanX n).price A.selfH (succDeferral.f n) - (cleanX n).expect A.selfH n =
      A.selfH (n + 1) (witnessQuoted 0 n ⋏ ∼∼witnessQuoted 0 n) -
        A.selfH n (witnessQuoted 0 n ⋏ ∼∼witnessQuoted 0 n) := by
  show ((LUV.indicatorOf (witnessQuoted 0 n)).expectAffine (n + 1)).price A.selfH (n + 1) -
    (LUV.indicatorOf (witnessQuoted 0 n)).expect A.selfH n = _
  rw [LUV.expectAffine_priceAt, indicatorOf_expectApprox_eq _ (Nat.succ_pos n),
    indicatorOf_expect_eq]

end Cleanroom.Fa.FaForcingTrader.AuditR3
