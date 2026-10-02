import Cleanroom.Bli.BliLeak.Leak

/-!
# `bli-leak` · audit round 1 · adversarial lens · probe: the day-`0` agreement clause

**Not imported by the library.** Evidence for items of `bli-leak-audit-r1-adversarial.md`.
Elaborated against the package as committed on 2026-09-30 (twelve modules, gate PASS).

* P1 — `E1x Q P` constrains day `0` at `⊥` only: any market equal to `Q` on days `≥ 1` and at
  `(0, ⊥)` is `E1x`-related to `Q`, whatever it does on the rest of day `0`. This is the clause
  L3.0's witness inhabits; the agreement half of that witness is therefore degenerate (N−), while
  the exploitation half is FAF's real PE1 content.
* P2 — the hypothesis package of L3.3 (`leakTrader_exploits`) forces the deductive process to be
  computable, through FAF's `IsLogicalInductor.processComputable`; so at the instance of record the
  OPEN inductor certificate `leakQ_isLogicalInductor` *implies* the OPEN `leakDP_computable`
  (and rests on it in the other direction through `LIA_is_logical_inductor`): the two open
  statements are equivalent, and any inhabitant of L3.3's package carries a computable process
  deciding the family — the non-vacuity of L3.3 is T7 itself, not merely the instance's certificate.
-/

namespace Cleanroom.Bli.BliLeak.AuditR1

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound
open Cleanroom.Bli.BliLeak

/-! ## P1. Day `0` is free off `⊥` -/

/-- Any market agreeing with `Q` on days `≥ 1` and at `(0, ⊥)` is `E1x`-related to `Q`. -/
theorem e1x_of_agree_succ_and_falsum (Q P : History) (h0 : P 0 ⊥ = Q 0 ⊥)
    (hs : ∀ n, 1 ≤ n → ∀ φ, P n φ = Q n φ) : E1x Q P := by
  intro n φ hφ
  rw [mem_smallSet] at hφ
  cases n with
  | zero =>
      rw [smallOn_zero_iff] at hφ
      subst hφ
      exact h0
  | succ n => exact hs (n + 1) (by omega) φ

/-- Day `0` may be replaced by **any** valuation off `⊥` without breaking `E1x`: the
market that prices every non-`⊥` sentence on day `0` by an arbitrary `w` is `E1x`-related to
`Q`. (So L3.0's `E1x` clause holds for every day-`0` edit whatsoever; the content of L3.0 is
entirely in FAF's exploitation of the *particular* day-`0` row `cxPerturbed` chooses.) -/
theorem e1x_dayZero_arbitrary (Q : History) (w : Sentence → ℝ) :
    E1x Q (fun n φ => if n = 0 ∧ φ ≠ ⊥ then w φ else Q n φ) := by
  refine e1x_of_agree_succ_and_falsum Q _ (by simp) (fun n hn φ => ?_)
  have : n ≠ 0 := by omega
  simp [this]

/-! ## P2. L3.3's package forces a computable process -/

/-- The instance hypothesis of the abstract leak theorem carries the computability of the
process: `IsLogicalInductor.processComputable`. At the instance of record this reads
`IsLogicalInductor (leakQ T) (leakDP T) → ComputableDeductiveProcess (leakDP T)`, the converse of
`Closed.lean`'s `leakQ_isLogicalInductor`. -/
theorem package_forces_computable_process (Q : History) (DP : DeductiveProcess)
    [h : IsLogicalInductor Q DP] : ComputableDeductiveProcess DP :=
  h.processComputable

/-- ... and the computability of the market. -/
theorem package_forces_computable_market (Q : History) (DP : DeductiveProcess)
    [h : IsLogicalInductor Q DP] : ComputableMarket Q :=
  h.marketComputable

end Cleanroom.Bli.BliLeak.AuditR1
