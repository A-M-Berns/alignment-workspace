import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Monotone.Basic
import Cleanroom.Found.CorrThreeStep.Setting

/-!
# `corr-trajectory` — `Sequences`: Statement 11, descent and convergence are independent (T10)

Three real sequences refute the develop's 11(c) ("monotone descent implies convergence [to the
target]"): `d ≡ 1` descends (weakly) and never reaches `0`; `d_t = 1 + 1/(t+1)` descends strictly with
limit `1`; C8's `d_t = (1 + (−1)^t/2)/(t+1)` converges to `0` and is not monotone. Reading
(ATTRIBUTION-UNVETTED on Christiano's text): `d` nonnegative, "`E[d_{t+1} ∣ s_t] ≤ d_t`" as the
deterministic `Antitone d`. Surviving neighbour: a nonnegative supermartingale converges a.s. to
*some* `d_∞ ≥ 0` (Layer M, `Martingale.ae_tendsto_of_nonneg`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open Filter Topology Finset

namespace Sequences

/-- **A5 (constant): descent without convergence to the target.** `d ≡ 1` is antitone and tends to
`1 ≠ 0`.
Source: [[corr-wf14-inventory]] 081, 2-019 / invariant.md Statement 11(c) ("monotone descent implies convergence of `d_t`"); counterexamples.py A5
Kind: N+ (refutation; constant — N− as a sequence, listed with the strict one below)
Fidelity: exact
Hyps: (a) only -/
theorem const_antitone_not_zero :
    Antitone (fun _ : ℕ => (1 : ℝ)) ∧ Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) ∧ (1 : ℝ) ≠ 0 :=
  ⟨antitone_const, tendsto_const_nhds, one_ne_zero⟩

/-- **A5 (strict): `d_t = 1 + 1/(t+1)` is strictly decreasing with limit `1 ≠ 0`.**
Source: [[corr-wf14-inventory]] 081, 2-019 / invariant-final.md Statement 11(b) ("`d_t = 1 + 1/(t+1)` descends strictly with limit `1`"); counterexamples.py A5
Kind: N+ (refutation)
Fidelity: exact
Hyps: (a) only -/
theorem strictAnti_limit_one :
    StrictAnti (fun t : ℕ => 1 + 1 / ((t : ℝ) + 1)) ∧
      Tendsto (fun t : ℕ => 1 + 1 / ((t : ℝ) + 1)) atTop (𝓝 1) := by
  constructor
  · refine strictAnti_nat_of_succ_lt fun t => ?_
    have h1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have h2 : (t : ℝ) + 1 < ((t + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
    have := one_div_lt_one_div_of_lt h1 h2
    linarith
  · have := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
    simpa using this

/-- C8's sequence `d_t = (1 + (−1)^t/2)/(t+1)`. Source: checks.py C8. Kind: D. Fidelity: exact -/
noncomputable def c8 (t : ℕ) : ℝ := (1 + (-1 : ℝ) ^ t / 2) / ((t : ℝ) + 1)

/-- **C8: convergence without descent.** `d_t → 0` while `d_1 = 1/4 < 1/2 = d_2`.
Source: [[corr-wf14-inventory]] 081, 2-019, 2-080 (C8) / invariant-final.md Statement 11(b); checks.py C8
Kind: N+ (refutation of the converse direction)
Fidelity: exact
Hyps: (a) only -/
theorem c8_tendsto_not_antitone : Tendsto c8 atTop (𝓝 0) ∧ ¬ Antitone c8 ∧ c8 1 = 1 / 4 ∧ c8 2 = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- squeeze: `0 ≤ c8 t ≤ (3/2) / (t + 1)`
    have hbound : ∀ t : ℕ, |c8 t| ≤ 3 / 2 * (1 / ((t : ℝ) + 1)) := by
      intro t
      unfold c8
      have hpos : (0 : ℝ) < (t : ℝ) + 1 := by positivity
      rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      have h1 : |(1 : ℝ) + (-1) ^ t / 2| ≤ 3 / 2 := by
        rcases neg_one_pow_eq_or ℝ t with h | h <;> rw [h] <;> norm_num
      calc |(1 : ℝ) + (-1) ^ t / 2| ≤ 3 / 2 := h1
        _ = 3 / 2 * (1 / ((t : ℝ) + 1)) * ((t : ℝ) + 1) := by field_simp
    have hlim : Tendsto (fun t : ℕ => 3 / 2 * (1 / ((t : ℝ) + 1))) atTop (𝓝 (3 / 2 * 0)) :=
      tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
    rw [mul_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (f := c8) (g := fun t : ℕ => -(3 / 2 * (1 / ((t : ℝ) + 1))))
      (h := fun t : ℕ => 3 / 2 * (1 / ((t : ℝ) + 1))) (by simpa using hlim.neg) hlim
      (fun t => (abs_le.1 (hbound t)).1) (fun t => (abs_le.1 (hbound t)).2)
  · intro h
    have := h (show (1 : ℕ) ≤ 2 by norm_num)
    unfold c8 at this
    norm_num at this
  · unfold c8; norm_num
  · unfold c8; norm_num

end Sequences

end Cleanroom.Corrigibility.CorrTrajectory
