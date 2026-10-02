import Cleanroom.Li.TtLadder

/-!
# tt-ladder audit, round 3, lens `fidelity` — probe S2

Not imported by the library. Supports remark N6 of
`run/wp/tt-ladder/tt-ladder-audit-r3-fidelity.md`.

* **S2**: the `L_cond` half of repair round 2's threshold-range fix. `tFullSeq_iff_Icc`
  (`Bounds.lean`) shows that under the sources' standing bounds `a ≤ 1`, `0 ≤ e` the all-`t`
  family `T_full` is the `[0,1]` family. The closure's other side, `lCondSeq_all_iff_dominates`,
  also quantifies over every rational `t`, and the same two observations (for `t < 0` the
  conclusion `t − c < e n` is automatic; for `t > 1` the gate event `t < a n` never happens)
  make `∀ t, L_cond(t)` the `[0,1]` family under the same bounds. So F4's refutation of
  faithful l.171 is the sources' own claim under their bounds on both sides of the `.trans`.
-/

namespace Cleanroom.Li.TtLadder.AuditR3Fidelity

open LogicalInduction Filter Topology
open Cleanroom.Found.LiAsympCalc
open Cleanroom.Li.TtLadder

/-- S2: for `a ≤ 1`, `0 ≤ e`, `L_cond(t)` at every rational `t` is `L_cond(t)` at every
`t ∈ [0,1]`. -/
theorem lCondSeq_all_iff_Icc {a e : ℕ → ℝ} (ha : ∀ n, a n ≤ 1) (he : ∀ n, 0 ≤ e n) :
    (∀ t : ℚ, LCondSeq a e t) ↔ ∀ t : ℚ, 0 ≤ t → t ≤ 1 → LCondSeq a e t := by
  constructor
  · intro h t _ _
    exact h t
  · intro h t c hc
    rcases lt_or_ge t 0 with ht | ht
    · refine Eventually.of_forall (fun n _ => ?_)
      have htR : (t : ℝ) < 0 := by exact_mod_cast ht
      linarith [he n]
    rcases le_or_gt t 1 with ht1 | ht1
    · exact h t ht ht1 c hc
    · refine Eventually.of_forall (fun n hn => ?_)
      have ht1R : (1 : ℝ) < t := by exact_mod_cast ht1
      exact absurd hn (not_lt.2 (by linarith [ha n]))

end Cleanroom.Li.TtLadder.AuditR3Fidelity
