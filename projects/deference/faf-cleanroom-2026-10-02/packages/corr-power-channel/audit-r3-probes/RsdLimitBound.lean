import Cleanroom.Corrigibility.CorrPowerChannel.Mdp

/-!
Audit r3 (adversarial) probe for `rsd` / `rsd_identity` (`Mdp.lean`, T7(b)).

`rsd π` is *defined* as four hand-written vectors, and the only Lean statement tying it to `visit`
is `rsd_identity`: `(1 − γ)·visit π γ x = rsd π x + (1 − γ)·corr π γ x`. An adversary notes that this
identity holds for *any* choice of `rsd` once `corr` is defined as the difference divided by
`(1 − γ)`; what makes it a limit statement is that `corr` stays **bounded** as `γ → 1`, which the
docstring asserts ("entries in `[−2, 1]`") but nothing in the library proves. This file proves the
bound and the quantitative limit it gives:

* `corr_abs_le_two`: `|corr π γ x| ≤ 2` for every policy, state and `γ ∈ [0, 1)`;
* `visit_rsd_bound`: `|(1 − γ)·visit π γ x − rsd π x| ≤ 2·(1 − γ)` on `[0, 1)` — so
  `(1 − γ)·visit π γ → rsd π` as `γ → 1⁻` at rate `O(1 − γ)`, with the constant explicit and no
  topology import.

With `VisitRecursion.lean` (the closed forms satisfy the visit recursion of the stated kernel), this
reduces the `(c)` on the MDP vectors to: "the kernel was read off `check_turner.py` by hand; the
recursion `f = e_s + γ Tᵀ f` has a unique solution for `γ < 1` (standard, not formalized)". The RSDs
are then pinned down by the library's identity plus this bound.

Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel.AuditR3

open Finset

noncomputable section

/-- For `0 < d`, `0 ≤ n ≤ d`: `−2 ≤ −(n/d) ≤ 2`. -/
theorem neg_div_bounds (n d : ℝ) (hd : 0 < d) (hn : 0 ≤ n) (hnd : n ≤ d) :
    -2 ≤ -(n / d) ∧ -(n / d) ≤ 2 := by
  have h1 : n / d ≤ 1 := (div_le_one hd).2 hnd
  have h0 : 0 ≤ n / d := div_nonneg hn hd.le
  constructor <;> linarith

/-- **Every entry of the correction is bounded by `2` in absolute value on `γ ∈ [0, 1)`.** The
entries are `1`, `γ`, `0`, `−1`, `−(1 + γ)`, `−1/(2(1 + γ))` and `−(2γ + 1)/(2(1 + γ))`. -/
theorem corr_abs_le_two (π : Pol) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∀ x, |corr π γ x| ≤ 2 := by
  have h4 : 0 < 2 * (1 + γ) := by linarith
  have hd1 := neg_div_bounds 1 (2 * (1 + γ)) h4 (by norm_num) (by linarith)
  have hd2 := neg_div_bounds (2 * γ + 1) (2 * (1 + γ)) h4 (by linarith) (by linarith)
  rcases π with ⟨k, a, b⟩
  cases k <;> cases a <;> cases b <;>
    simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true, corr, Matrix.cons_val_zero,
      Matrix.cons_val_succ] <;>
    (repeat' apply And.intro) <;>
    (rw [abs_le]; constructor <;> linarith [hd1.1, hd1.2, hd2.1, hd2.2])

/-- **The quantitative limit**: `|(1 − γ)·visit π γ x − rsd π x| ≤ 2·(1 − γ)` for `γ ∈ [0, 1)`. -/
theorem visit_rsd_bound (π : Pol) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (x : Fin 5) :
    |(1 - γ) * visit π γ x - rsd π x| ≤ 2 * (1 - γ) := by
  rw [rsd_identity π hγ0 hγ1 x]
  have e : rsd π x + (1 - γ) * corr π γ x - rsd π x = (1 - γ) * corr π γ x := by ring
  rw [e, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - γ), mul_comm (2 : ℝ)]
  exact mul_le_mul_of_nonneg_left (corr_abs_le_two π hγ0 hγ1 x) (by linarith)

end

end Cleanroom.Corrigibility.CorrPowerChannel.AuditR3
