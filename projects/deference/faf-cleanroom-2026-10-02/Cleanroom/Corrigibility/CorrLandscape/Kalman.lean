import Cleanroom.Corrigibility.CorrLandscape.Crossing
import Mathlib.Analysis.Real.Sqrt

/-!
# `corr-landscape` — `Kalman`: S8, the Kalman freeze (T7)

A8.2 / 2-053 ([[corr-wf14-inventory]] 120): the estimate freezes only if the agent's model excludes
target drift. Scalar steady state: for `q, R > 0` the equation `P² + qP − qR = 0` has exactly one
positive root `P_ss = (−q + √(q² + 4qR))/2` (`Pss_root`, `Pss_pos`, `Pss_unique`); the predicted-
covariance gain `K_ss = (P_ss + q)/(P_ss + q + R)` is `0` at `q = 0` (freeze) and positive at `q > 0`.
Worked `q = 1/2500`, `R = 1/400`: `P_ss ∈ (819/10⁶, 82/10⁵)` by sign change and monotonicity,
`K_ss ∈ (327/1000, 329/1000)` — a bracket, never `= 0.328`. The gain recursion
`P ↦ (P + q)R/(P + q + R)` with `K_t = (P_t + q)/(P_t + q + R)` has the one-line floor
`K_t ≥ q/(q + R) > 0` at every `t` (`Kt_ge`): the Bayesian learner with drift in its model never
freezes — against the hard-threshold correctness filter, whose gain is `0` for `t ≥ 17` (`gainVL_zero`,
through T4). Both together are the formal content of A8.2's "the correctness filter is not a Bayesian
learner".

Known issue (recorded): the inventory 2-053 writes `K_ss = P_ss/(P_ss + R)` (the *updated*-covariance
convention), which gives `≈ 0.247` (`Kss_inventory_bracket`); P6 and `s8_kalman_gain.py` use the
predicted-covariance form, which gives `0.328`. Monte Carlo errors (`0.024` vs `0.69`) are not formalized.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open Cleanroom.Corrigibility.CorrTrajectory
open Corruption (oddsIneq)

set_option linter.unusedSectionVars false

namespace Kalman

/-- **The steady-state covariance** `P_ss = (−q + √(q² + 4qR))/2`.
Source: [[corr-wf14-inventory]] 120; [[corr-wf14-2-inventory]] 2-053 / approval-final.md P6
("steady-state gain solves `P² + qP − qR = 0`"); `s8_kalman_gain.py`
Kind: D
Fidelity: exact -/
noncomputable def Pss (q R : ℝ) : ℝ := (-q + Real.sqrt (q ^ 2 + 4 * q * R)) / 2

/-- `P_ss` is a root of `P² + qP − qR` (`0 ≤ q`, `0 ≤ R`).
Source: approval-final.md P6
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem Pss_root (q R : ℝ) (hq : 0 ≤ q) (hR : 0 ≤ R) : Pss q R ^ 2 + q * Pss q R - q * R = 0 := by
  unfold Pss
  have h := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q ^ 2 + 4 * q * R)
  nlinarith [h]

/-- `P_ss > 0` for `q, R > 0`. Source: approval-final.md P6. Kind: L. Fidelity: exact -/
theorem Pss_pos (q R : ℝ) (hq : 0 < q) (hR : 0 < R) : 0 < Pss q R := by
  unfold Pss
  have : q < Real.sqrt (q ^ 2 + 4 * q * R) := by
    rw [Real.lt_sqrt hq.le]; nlinarith
  linarith

/-- **Uniqueness of the positive root**: any `P > 0` with `P² + qP − qR = 0` is `P_ss` (the other root
`−(q + P_ss)` is negative).
Source: approval-final.md P6; mandate T7 ("uniqueness by monotonicity")
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem Pss_unique (q R P : ℝ) (hq : 0 < q) (hR : 0 < R) (hP : 0 < P) (hroot : P ^ 2 + q * P - q * R = 0) :
    P = Pss q R := by
  have h1 := Pss_root q R hq.le hR.le
  have h2 := Pss_pos q R hq hR
  have hfac : (P - Pss q R) * (P + q + Pss q R) = 0 := by nlinarith
  rcases mul_eq_zero.1 hfac with h | h
  · linarith
  · linarith

/-- **The steady-state gain** `K_ss = (P_ss + q)/(P_ss + q + R)` (predicted-covariance convention, as
P6 and the script).
Source: [[corr-wf14-inventory]] 120 / approval-final.md P6; `s8_kalman_gain.py`
Kind: D
Fidelity: exact under `0 < P_ss + q + R` -/
noncomputable def Kss (q R : ℝ) : ℝ := (Pss q R + q) / (Pss q R + q + R)

/-- **The freeze**: at `q = 0` (no drift in the model) `K_ss = 0`.
Source: [[corr-wf14-inventory]] 120 / approval-final.md S8 ("the estimate freezes only if the agent's
model excludes drift")
Kind: L
Fidelity: exact -/
theorem Kss_zero (R : ℝ) (hR : 0 < R) : Kss 0 R = 0 := by
  simp [Kss, Pss, hR.ne']

/-- **No freeze with drift in the model**: `q > 0 ⟹ K_ss > 0`.
Source: [[corr-wf14-inventory]] 120 / approval-final.md S8
Kind: L
Fidelity: exact -/
theorem Kss_pos (q R : ℝ) (hq : 0 < q) (hR : 0 < R) : 0 < Kss q R := by
  have := Pss_pos q R hq hR
  unfold Kss
  positivity

/-- `P ↦ P² + qP` is monotone on `P ≥ 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma quad_mono (q x y : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x) (hxy : x ≤ y) : x ^ 2 + q * x ≤ y ^ 2 + q * y := by
  nlinarith

/-- **The worked bracket** `P_ss ∈ (819/10⁶, 82/10⁵)` at `q = 1/2500`, `R = 1/400`: sign change of
`P² + qP − qR` at the endpoints and monotonicity on `P ≥ 0`.
Source: [[corr-wf14-inventory]] 120 / approval-final.md P6 (the decimal `0.328` is downstream of this)
Kind: P (bracket, not a decimal)
Fidelity: exact
Hyps: (a) only -/
theorem Pss_bracket : Pss (1 / 2500) (1 / 400) ∈ Set.Ioo (819 / 1000000 : ℝ) (82 / 100000) := by
  have hroot := Pss_root (1 / 2500) (1 / 400) (by norm_num) (by norm_num)
  have hpos := Pss_pos (1 / 2500) (1 / 400) (by norm_num) (by norm_num)
  constructor
  · by_contra hcon
    rw [not_lt] at hcon
    have := quad_mono (1 / 2500) _ _ (by norm_num) hpos.le hcon
    norm_num at this
    linarith
  · by_contra hcon
    rw [not_lt] at hcon
    have := quad_mono (1 / 2500) _ _ (by norm_num) (by norm_num) hcon
    norm_num at this
    linarith

/-- **The worked gain bracket** `K_ss ∈ (327/1000, 329/1000)` (the source's `0.328`).
Source: [[corr-wf14-inventory]] 120 / approval-final.md P6 ("`K_ss = 0.328`")
Kind: P (bracket)
Fidelity: exact
Hyps: (a) only -/
theorem Kss_bracket : Kss (1 / 2500) (1 / 400) ∈ Set.Ioo (327 / 1000 : ℝ) (329 / 1000) := by
  obtain ⟨h1, h2⟩ := Pss_bracket
  unfold Kss
  have hden : 0 < Pss (1 / 2500) (1 / 400) + 1 / 2500 + 1 / 400 := by linarith
  constructor
  · rw [lt_div_iff₀ hden]; linarith
  · rw [div_lt_iff₀ hden]; linarith

/-- **The inventory's convention** `P_ss/(P_ss + R)` gives `≈ 0.247`, bracketed `(246/1000, 248/1000)`:
the discrepancy with P6's `0.328` is a convention, recorded in the findings.
Source: [[corr-wf14-2-inventory]] 2-053, Claim line (a) ("`K_ss = P_ss/(P_ss + R)`") against
approval-final.md P6
Kind: P (a bracket computation exhibiting the convention difference; not a non-vacuity witness —
audit r1, N11)
Fidelity: exact
Hyps: (a) only -/
theorem Kss_inventory_bracket :
    Pss (1 / 2500) (1 / 400) / (Pss (1 / 2500) (1 / 400) + 1 / 400) ∈ Set.Ioo (246 / 1000 : ℝ) (248 / 1000) := by
  obtain ⟨h1, h2⟩ := Pss_bracket
  have hden : 0 < Pss (1 / 2500) (1 / 400) + 1 / 400 := by linarith
  constructor
  · rw [lt_div_iff₀ hden]; linarith
  · rw [div_lt_iff₀ hden]; linarith

/-! ## The gain recursion never freezes with drift in the model -/

/-- **The covariance recursion** `P_{t+1} = (P_t + q) R/(P_t + q + R)` (the script's predict–update).
Source: [[corr-wf14-inventory]] 120 / `s8_kalman_gain.py` ("`P=P+q_model; K=P/(P+R); … P=(1-K)*P`")
Kind: D
Fidelity: exact -/
noncomputable def Pseq (P0 q R : ℝ) : ℕ → ℝ
  | 0 => P0
  | t + 1 => (Pseq P0 q R t + q) * R / (Pseq P0 q R t + q + R)

/-- **The gain** `K_t = (P_t + q)/(P_t + q + R)`.
Source: [[corr-wf14-inventory]] 120 / `s8_kalman_gain.py`
Kind: D
Fidelity: exact -/
noncomputable def Kt (P0 q R : ℝ) (t : ℕ) : ℝ := (Pseq P0 q R t + q) / (Pseq P0 q R t + q + R)

/-- The recursion preserves nonnegativity. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Pseq_nonneg (P0 q R : ℝ) (hP0 : 0 ≤ P0) (hq : 0 ≤ q) (hR : 0 ≤ R) : ∀ t, 0 ≤ Pseq P0 q R t := by
  intro t
  induction t with
  | zero => exact hP0
  | succ t ih => unfold Pseq; positivity

/-- **The Bayesian learner with drift never freezes**: `K_t ≥ q/(q + R) > 0` at every `t` (`q, R > 0`,
`P_0 ≥ 0`) — A8.2's "posterior variance bounded below, hence `η_t ≥ η̲ > 0`", in one line.
Source: [[corr-wf14-inventory]] 120; [[corr-wf14-2-inventory]] 2-053 / approval-adversary.md A8.2
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem Kt_ge (P0 q R : ℝ) (hP0 : 0 ≤ P0) (hq : 0 < q) (hR : 0 < R) (t : ℕ) :
    q / (q + R) ≤ Kt P0 q R t ∧ 0 < Kt P0 q R t := by
  have hP := Pseq_nonneg P0 q R hP0 hq.le hR.le t
  unfold Kt
  constructor
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_nonneg hP hR.le]
  · positivity

open Classical in
/-- **The hard-threshold correctness filter's gain**: `η` while the compliance inequality holds, `0` after.
Source: [[corr-wf14-inventory]] 120 / approval-final.md S8 ("`ρ_t = 1 − 𝟙[κ^VL_t]`")
Kind: D
Fidelity: exact -/
noncomputable def gainVL (η : ℝ) (t : ℕ) : ℝ :=
  if oddsIneq (1 / 20) (9 / 10) 20 1 (Margin.epsT t) then η else 0

/-- **The correctness filter freezes from `t* = 17`**: its gain is `0` at every `t ≥ 17` (T4), while
`Kt_ge` keeps the Bayesian gain above `q/(q + R)` — the formal content of "the correctness filter is not
a Bayesian learner" (A8.2).
Source: [[corr-wf14-inventory]] 120 / approval-final.md S8, approval-adversary.md A8.2
Kind: C (`Crossing.fails_from_17`)
Fidelity: exact
Hyps: (a) only -/
theorem gainVL_zero (η : ℝ) : ∀ t, 17 ≤ t → gainVL η t = 0 := by
  intro t ht
  rw [gainVL, if_neg (Crossing.fails_from_17 t ht)]

end Kalman

end Cleanroom.Corrigibility.CorrLandscape
