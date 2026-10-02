import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# `corr-landscape` — `Amplify`: S10, the linear cap (T8)

P8 ([[corr-wf14-inventory]] 121): under (A-amp) `q_{t+1} ≤ q_0 + k_t` and `k_{t+1} ≤ q_{t+1}`, deployed
decision quality grows at most linearly in the unaided overseer's quality: `k_t ≤ k_0 + t q_0`.

(A-amp) is the source's (CLAUDE) modelling assumption, which Christiano's line 19 denies in the limit;
the capped quantity is decision quality, not the option set / POWER of J7 (A10.3). Nothing more is claimed.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

namespace Amplify

/-- **S10 / P8: the linear cap**: `k_{t+1} ≤ q_{t+1}` and `q_{t+1} ≤ q_0 + k_t` give `k_t ≤ k_0 + t q_0`.
Source: [[corr-wf14-inventory]] 121 / approval-final.md S10, P8
Kind: L (induction)
Fidelity: exact (the hypotheses are (A-amp), the source's own assumption, and the min-cap)
Hyps: (c) (A-amp) `q_{t+1} ≤ q_0 + k_t` is CLAUDE's modelling assumption (denied by Christiano l. 19 in
the limit); `k_{t+1} ≤ q_{t+1}` is the min-cap `k^eff = min(k^tech, q)` -/
theorem linear_cap (k q : ℕ → ℝ) (hk : ∀ t, k (t + 1) ≤ q (t + 1)) (hq : ∀ t, q (t + 1) ≤ q 0 + k t) :
    ∀ t, k t ≤ k 0 + t * q 0 := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    have := hk t
    have := hq t
    push_cast
    nlinarith

end Amplify

end Cleanroom.Corrigibility.CorrLandscape
