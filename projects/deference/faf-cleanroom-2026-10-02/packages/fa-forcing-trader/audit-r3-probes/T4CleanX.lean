import Cleanroom.Fa.FaForcingTrader.A.Witnesses

/-!
# Audit r3 (fidelity) probe: T4 on a non-constant e.c. family, in the lines the package already has

Not imported by the library. The round-2 repair records (report § Repair round 2, findings R-14)
that the only witness of the load-bearing T4 `hSideBridge` is `A.hSideBridge_w2` on the constant
family `X ≡ 𝟙(atom k)`, on which the round-trip return provably vanishes with no trader
(`hSideBridge_w2_return_tendsto_zero`), and that a witness on a non-constant family was "not
attempted (needs an e.c. certificate for a varying indicator family and an argument that the
return is not Cesàro-null — neither available cheaply)". The first half is not so: the package's
own T3 witness `A.v3Theorem1_paper_self` already runs on li-quote-lane's `cleanX`
(`cleanX n = 𝟙(witnessQuoted 0 n)`, a varying family of distinct atoms) with its e.c. certificate
`cleanX_codes`. This probe instantiates `hSideBridge` on exactly that family on the paper LIA
with the bare schedule indicator as the weighting: every hypothesis discharged, no constant
family, so `bundle_indicator_return_tendsto_zero` (a *fixed* sentence's price difference) does not
apply to it. Whether the return is Cesàro-null on this instance for some other reason is not
settled here (nor claimed either way) — but "not shown trivial" is strictly more than the
current witness offers, whose conclusion is a corollary of `thm:con`.
-/

namespace Cleanroom.Fa.FaForcingTrader.AuditR3

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Cleanroom.Fa.FaForcingTrader
  Filter Topology

/-- **T4 on the paper LIA with the varying undecided family `cleanX`**, every hypothesis of
`hSideBridge` discharged: for every window-disjoint schedule `d` for `succDeferral`, the
schedule-indicator-weighted average of the round-trip return
`price^H_{n+1}(bundle(cleanX)_n) − 𝔼^H_n(cleanX_n)` tends to `0`. Same objects as
`A.v3Theorem1_paper_self` (market, family, certificate, world) and as `A.hSideBridge_w2`
(weighting); the family is not constant. -/
theorem hSideBridge_cleanX {d : DeferralFunction} (hwd : WindowDisjoint succDeferral d) :
    WeightedApprox (fun n => (scheduleIndicator d n).denote A.selfH)
      (fun n => (bundle cleanX n).price A.selfH (succDeferral.f n))
      (fun n => (cleanX n).expect A.selfH n) :=
  haveI := w1_inductorH
  _root_.Cleanroom.Fa.FaForcingTrader.A.hSideBridge cleanX_codes (paperDP_hworld 𝗜𝚺₁) hwd
    (scheduleIndicator_pgenerable d)
    (fun n hn => scheduleIndicator_supported d A.selfH n hn) (scheduleIndicator_divergent d _)

/-- The concrete schedule `2, 4, 6, …` (A's `linearSchedule 0`) closes the package: a fully
instantiated T4 on a non-constant family. -/
theorem hSideBridge_cleanX_linear :
    WeightedApprox (fun n => (scheduleIndicator (linearSchedule 0) n).denote A.selfH)
      (fun n => (bundle cleanX n).price A.selfH (succDeferral.f n))
      (fun n => (cleanX n).expect A.selfH n) :=
  hSideBridge_cleanX (windowDisjoint_succ_linear 0)

/-- `cleanX` is not a constant family: its day-`n` and day-`(n+1)` members are indicators of
distinct atoms, so the fixed-sentence argument of `Witnesses` §E does not apply to the
instance above. -/
theorem cleanX_not_const (n : ℕ) : cleanX n ≠ cleanX (n + 1) := by
  intro h
  have h' : (cleanX n).gt (1/2) = (cleanX (n + 1)).gt (1/2) := by rw [h]
  norm_num [cleanX, LUV.indicatorOf, witnessQuoted, LO.Propositional.Formula.and_inj,
    Nat.pair_eq_pair] at h'

end Cleanroom.Fa.FaForcingTrader.AuditR3
