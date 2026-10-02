import Cleanroom.Bli.UdtBliLearning.TheoremB

/-!
# Audit r3 (adversarial) probe · ScheduleZero: `Schedule K N` is inhabited at `N = 0`

`TheoremB.lean`'s docstring of `schedOfPos` (and the ledger row for `Schedule`/`schedOfPos`/
`schedule_nonempty`) says "`Schedule K N` is inhabited exactly when `0 < N < K`
(`schedule_nonempty`)". The Lean proves one direction only (`0 < N → N < K → Nonempty`), and the
"exactly" is false in the other: `Schedule 2 0` is inhabited by `t = id` (`t 0 = 0`, `0 ≤ t 1 = 1 < 2`).
The structure's fields never force `0 < N`; the theorems of `TheoremB` carry `0 < N` as a separate
hypothesis, which is why nothing rests on the claim. Presentation only.
-/

set_option autoImplicit false

namespace Cleanroom.Bli.UdtBliLearning.AuditR3

/-- `Schedule 2 0` is inhabited: `t = id`. -/
def sched20 : Schedule 2 0 where
  t := id
  strictMono := strictMono_id
  t0 := rfl
  hN := Nat.zero_le _
  hK := by decide

/-- So `Nonempty (Schedule K N)` does not imply `0 < N`: the "exactly when `0 < N < K`" is one
direction only. -/
theorem schedule_nonempty_not_iff : Nonempty (Schedule 2 0) ∧ ¬ (0 < 0) :=
  ⟨⟨sched20⟩, lt_irrefl 0⟩

end Cleanroom.Bli.UdtBliLearning.AuditR3
