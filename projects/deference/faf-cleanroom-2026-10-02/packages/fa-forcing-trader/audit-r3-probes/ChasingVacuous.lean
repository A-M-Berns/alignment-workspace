import Cleanroom.Fa.FaForcingTrader.A.Analysis

/-!
# `fa-forcing-trader` · audit r3 (adversarial) · probe: `ChasingSchedule` is vacuous below `w → 0`

Evidence for `fa-forcing-trader-audit-r3-adversarial.md`. **Not imported by the library.**

`ChasingSchedule f w` (the (c) of record for T10's FAF corollary, `A/Analysis.lean`) reads
`∀ θ > 0, (∃ᶠ n, θ ≤ w n) → ∃ d, WindowDisjoint f d ∧ ∃ᶠ k, θ ≤ w (d k)`. Its docstring says it is
"vacuous exactly when `w → 0`". This probe machine-checks the vacuity half: for a nonnegative
`w` tending to `0`, `ChasingSchedule f w` holds for **every** lookahead `f` with no schedule
built. Consequence recorded in the audit: at the same-market instance (`A = H`), where `cee`
makes the violation weight tend to `0` (probe `SelfMarketCee.lean`), the chasing hypothesis of
`v3Theorem1_tendsto_zero_of_chasing` is a theorem, so that headline's full package is inhabited
there — an N− inhabitant (the conclusion is the premise) that the package does not ship.
-/

namespace Cleanroom.Fa.FaForcingTrader.AuditR3

open LogicalInduction Cleanroom.Found.LiAsympCalc Cleanroom.Fa.FaForcingTrader Filter Topology

/-- A nonnegative sequence tending to `0` is chased by every lookahead, vacuously: no `θ > 0`
is reached frequently. -/
theorem chasingSchedule_of_tendsto_zero (f : DeferralFunction) {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) (h : Tendsto w atTop (𝓝 0)) : A.ChasingSchedule f w := by
  intro θ hθ hfr
  exfalso
  have hev : ∀ᶠ n in atTop, w n < θ := by
    have := (Metric.tendsto_nhds.1 h) θ hθ
    exact this.mono (fun n hn => by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hw n)] at hn
      exact hn)
  obtain ⟨n, h1, h2⟩ := (hfr.and_eventually hev).exists
  exact absurd h1 (not_le.2 h2)

/-- And conversely the chasing hypothesis is only ever *non*-vacuous when `w ↛ 0`: under it,
`tendsto_zero_of_chasing`'s conclusion is exactly what `hfin` must then rule out. (Restates the
library's `tendsto_zero_of_chasing` at a vacuous `hch`, to record that the composition is not a
squeeze: `hfin` is still consumed when `w ↛ 0`.) -/
theorem tendsto_zero_of_chasing_vacuous (f : DeferralFunction) {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) (h : Tendsto w atTop (𝓝 0))
    (hfin : ∀ d : DeferralFunction, WindowDisjoint f d →
      ¬ Tendsto (prefixSum (fun n => schedInd d n * w n)) atTop atTop) :
    Tendsto w atTop (𝓝 0) :=
  A.tendsto_zero_of_chasing hw (chasingSchedule_of_tendsto_zero f hw h) hfin

end Cleanroom.Fa.FaForcingTrader.AuditR3
