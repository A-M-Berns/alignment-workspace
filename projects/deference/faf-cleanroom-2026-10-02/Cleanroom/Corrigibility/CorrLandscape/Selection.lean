import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# `corr-landscape` — `Selection`: selection under RL as reweighting fixed personae (T19)

`faking-final.md` S12, P5 ([[corr-wf14b-inventory]] 051): a compliance-reinforcing step *modelled as
reweighting fixed personae by compliance* takes the faking fraction `12/100` to `102/113` and then above
`99/100` (`reweight_worked`); the scalar contraction `q_{t+1} = q_t + η(q* − q_t)m` converges to `q*` for
`0 < ηm ≤ 1` (`contract_tendsto`, geometric), with P5(a)'s two twelve-step cells.

Direction and order only: the paper's mechanism is a moving policy, not a reweighted mixture (S12's
hedge); the number `12% → 78%` is not fitted and not claimed.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open Filter Topology

namespace Selection

/-- **Reweighting fixed personae by compliance**: `f' = f(1 − r_f)/(f(1 − r_f) + (1 − f)(1 − r_n))`.
Source: [[corr-wf14b-inventory]] 051 / faking-final.md P5(b)
Kind: D
Fidelity: exact -/
noncomputable def reweight (f rf rn : ℝ) : ℝ := f * (1 - rf) / (f * (1 - rf) + (1 - f) * (1 - rn))

/-- **The worked reweighting**: `12/100 ↦ 102/113`, and once more `> 99/100`.
Source: [[corr-wf14b-inventory]] 051 / faking-final.md P5(b) ("takes `12/100` to `102/113 ≈ 0.903`, then
`≈ 0.998`")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem reweight_worked :
    reweight (12 / 100) (32 / 100) (99 / 100) = 102 / 113 ∧
      (99 / 100 : ℝ) < reweight (102 / 113) (32 / 100) (99 / 100) := by
  unfold reweight; norm_num

/-- **The scalar contraction** `q_{t+1} = q_t + η(q* − q_t)m`.
Source: [[corr-wf14b-inventory]] 051 / faking-final.md P5(a) (D1)
Kind: D
Fidelity: exact -/
noncomputable def contract (qstar η m q0 : ℝ) : ℕ → ℝ
  | 0 => q0
  | t + 1 => contract qstar η m q0 t + η * (qstar - contract qstar η m q0 t) * m

/-- The closed form `q_t − q* = (1 − ηm)^t (q_0 − q*)`.
Source: faking-final.md P5(a)
Kind: L
Fidelity: exact -/
theorem contract_closed (qstar η m q0 : ℝ) (t : ℕ) :
    contract qstar η m q0 t = qstar + (1 - η * m) ^ t * (q0 - qstar) := by
  induction t with
  | zero => simp [contract]
  | succ t ih => rw [contract, ih, pow_succ]; ring

/-- **Convergence to `q*`** for `0 < ηm ≤ 1` (geometric).
Source: [[corr-wf14b-inventory]] 051 / faking-final.md P5(a) ("converges for every `θ > 0`")
Kind: P (small)
Fidelity: exact
Hyps: (a) only -/
theorem contract_tendsto (qstar η m q0 : ℝ) (h0 : 0 < η * m) (h1 : η * m ≤ 1) :
    Tendsto (contract qstar η m q0) atTop (𝓝 qstar) := by
  have hr : Tendsto (fun t : ℕ => (1 - η * m) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have := (hr.mul_const (q0 - qstar)).const_add qstar
  rw [zero_mul, add_zero] at this
  exact this.congr fun t => (contract_closed qstar η m q0 t).symm

/-- **P5(a)'s twelve-step cells**: from `9/10` toward `1/10` with `η = 1/4`, after twelve steps
`q_12 = 1/10 + (3/4)^12 · (4/5)` (honest, `m = 1`) against `1/10 + (19/20)^12 · (4/5)` at `θ = m = 1/5`.
Source: [[corr-wf14b-inventory]] 051 / faking-final.md P5(a) ("after twelve steps `0.125` against `0.532`")
Kind: N+
Fidelity: exact (the decimals are these closed forms)
Hyps: (a) only -/
theorem contract_cells :
    contract (1 / 10) (1 / 4) 1 (9 / 10) 12 = 1 / 10 + (3 / 4 : ℝ) ^ 12 * (4 / 5) ∧
      contract (1 / 10) (1 / 4) (1 / 5) (9 / 10) 12 = 1 / 10 + (19 / 20 : ℝ) ^ 12 * (4 / 5) := by
  rw [contract_closed, contract_closed]; norm_num

end Selection

end Cleanroom.Corrigibility.CorrLandscape
