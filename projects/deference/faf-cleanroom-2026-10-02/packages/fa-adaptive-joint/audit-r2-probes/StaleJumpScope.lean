import Cleanroom.Fa.FaAdaptiveJoint.Staleness

/-!
# `fa-adaptive-joint` · audit r2 (adversarial) · probe: the no-jump (c) is not "weaker than `→ 0`"

Evidence for `fa-adaptive-joint-audit-r2-adversarial.md`. **Not imported by the library.**

The ledger row of `v3Theorem2_stale_of_noJumps_of_bridge` (after repair r1, following audit r1
fidelity N11) says its no-jump hypothesis `hjump : ∀ n, 0 < staleViol … n → h n ≤ h (n−1) + ε/2`
is "a *weaker* hypothesis than the mandate's `|h_n − h_{n−1}| → 0`". It is not: `hjump` is a
bound on **every** day of the stale support, and `|h_n − h_{n−1}| → 0` bounds only the tail. The
two are incomparable — `→ 0` gives an eventual bound of any size, `hjump` a uniform bound on all
days. Real-sequence instance: `a ≡ 1`, `h = 0, 1, 1, 1, …`, `t = ½`, `ε = ¼`, `δ = ⅛`:
`|h_n − h_{n−1}| → 0` (it is `0` from day `2`), the stale gate is `1` on day `1`, and
`h_1 = 1 > h_0 + ε/2 = ⅛`. (The gate-general theorem's `hsupp` is `∀ n`, so the eventual form
would need either a finite-modification lemma for `LegibleOn` or an eventual-support version of
`v3Theorem2_gate_of_bridge`; neither is in the package.)
-/

namespace Cleanroom.Fa.FaAdaptiveJoint.AuditR2

open LogicalInduction Cleanroom.Found.LiAsympCalc Filter Topology

theorem hjump_not_implied_by_tendsto :
    ∃ (h a : ℕ → ℝ) (t ε δ : ℚ), 0 < ε ∧ 0 < δ ∧
      Tendsto (fun n => |h n - h (n - 1)|) atTop (𝓝 0) ∧
      ¬ (∀ n, 0 < staleViol h a t ε δ n → h n ≤ h (n - 1) + (ε : ℝ) / 2) := by
  refine ⟨fun n => if n = 0 then 0 else 1, fun _ => 1, 1 / 2, 1 / 4, 1 / 8, by norm_num,
    by norm_num, ?_, ?_⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    simp [show n ≠ 0 by omega, show n - 1 ≠ 0 by omega]
  · intro H
    have hgate : 0 < staleViol (fun n => if n = 0 then (0 : ℝ) else 1) (fun _ => 1)
        (1 / 2) (1 / 4) (1 / 8) 1 := by
      show 0 < dsWeight _ _ _ 1 (if (1 - 1 : ℕ) = 0 then (0 : ℝ) else 1)
      rw [if_pos rfl, dsWeight_eq_one (by norm_num) (by norm_num) (by norm_num)]
      norm_num
    have := H 1 hgate
    norm_num at this

end Cleanroom.Fa.FaAdaptiveJoint.AuditR2
