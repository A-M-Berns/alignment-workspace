import Cleanroom.Lit.LitMdpCorrigible

/-!
# `lit-mdp-corrigible` · audit r2 (adversarial) probe — `RejectOptimal … 0` is vacuous

Not imported by the library. `RejectOptimal g K n` quantifies over horizons `m < n`, so at `n = 0`
it holds for every goal-in-state MDP, goal and kernel. Hence at `n = 0` the (b) hypotheses of
`transform_corrigible_of_rejectOptimal` cost nothing and the headline reduces to "immediate-reward
optimal sets at reject actions agree under `P` and `P_C`", which is `RejectBlocks` alone. The bite of
the (b) hypothesis starts at `n ≥ 1`; the package's witness `Grid.grid_readingB_mandate_form` is at
`n = 2` with a strict `9/10 > 9/100` at `m = 1`, so it is outside this regime — recorded so the
boundary is visible.
-/

open Finset FactoredSpaces

namespace Cleanroom.Lit.LitMdpCorrigible.AuditR2Adversarial

open GoalMDP

variable {Goal Env Ab : Type*} [Fintype Goal] [Fintype Env] [Fintype Ab] [Nonempty Ab]
variable [DecidableEq Goal] [DecidableEq Env]

/-- **The probe's claim:** `RejectOptimal g K 0` for every `M`, `g`, `K`. -/
theorem rejectOptimal_zero (M : GoalMDP Goal Env (Ab × Bool)) (g : Goal) (K : Kernel Goal Env (Ab × Bool)) :
    M.RejectOptimal g K 0 :=
  fun m hm _ => absurd hm (Nat.not_lt_zero m)

/-- Consequently, at `n = 0` the mandate-form headline needs only `RejectBlocks`. -/
theorem mandate_form_at_zero (M : GoalMDP Goal Env (Ab × Bool)) (hRB : M.RejectBlocks) (g : Goal)
    (SC : Finset (Goal × Env)) (s : Goal × Env) :
    FinMDP.optSet (M.qFull g M.P 0) s = FinMDP.optSet (M.qFull g (M.PC SC) 0) s :=
  M.transform_corrigible_of_rejectOptimal hRB g 0 SC (rejectOptimal_zero M g M.P)
    (rejectOptimal_zero M g (M.PC SC)) s

end Cleanroom.Lit.LitMdpCorrigible.AuditR2Adversarial
