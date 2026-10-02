import Cleanroom.Decision.DpLearnerNr.Defs
import Cleanroom.Decision.DpCausalConsist.TbTheta
import Cleanroom.Decision.DpCalibration.Mugging
import Mathlib.Tactic.IntervalCases

/-!
# `dp-learner-nr` targets 5(c)–(f): the policy values in closed form

The threshold reader and XOR are *situations*, not Definition-6 trees: they are typed as
`ℚ → ℚ` value functions of the policy label (never as `Tree`s with a node that reads `q`).

* **Newcomb** (5(c)): `cfNewcomb M K f q = M·f(q) + (1−q)·K`. Label probe `f = id`: argmax `q = 1`
  (`newcomb_probe_argmax`). Threshold reader `f q = if q > ½ then r else 1 − r` with `f(½) := 1−r`
  on the grid `{k/10}`: the argmax is the smallest grid label above `½` iff
  `r > ½ + 3K/(10M)` (`newcomb_threshold_grid_iff`); the corner comparison `q = 1` vs `q = 0` gives
  the note's `½ + K/(2M)` (`newcomb_threshold_corner_iff`) — the two thresholds differ (findings,
  known issue 2); with `f(½) := r` the argmax is `½` (`newcomb_threshold_half_wins`). A
  policy-invariant box: argmax `q = 0` (`newcomb_invariant_argmax`).
* **TB(θ) at the policy level** (5(d)): `V(q) = −10θ + 10(1−θ)q` is maximized at `q = 1` for every
  `θ < 1` — "the separatrix `θ/(1−θ)` disappears" (`tb_policy_argmax`); the fallible troll's
  `cfPol cross = 10(1 − 2ζ)` is `cfMarginal_trollE_bool` (`Defs.lean`).
* **XOR** (5(e)): `cfXor p = if p < ½ then −10 − p else −10 − 99p`, derived from the two cases
  (`D ∼ Bern(1/100)`, disaster `1000`, payment `100`, `f(½) := ¬D`-side); refuse (`cfXor_argmax`).
  **Mugging**: `value (procQ p) (mug1 x y) = p(y − x)/2` (`dp-calibration`'s `mug1_value`); pay iff
  `y > x` (`mug_policy_pay_iff`).
* **The jump** (5(f)): `cfXor` is not affine in `p` (`cfXor_not_affine`): the policy value is affine
  when the environment reads the label only through draws (`tbTheta_value`, `mug1_value`) and not
  when it reads a threshold.
-/

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Found.DpCoreTree.Catalogue
  Cleanroom.Decision.DpCalibration Cleanroom.Decision.DpCausalConsist Finset

/-! ## Newcomb with a fill function of the label -/

/-- **Newcomb's policy value** against an Omega whose fill probability is `f(q)`: with `M` the big
box, `K` the small box and `q` the one-boxing label,
`cf(q) = q·M·f(q) + (1−q)·(M·f(q) + K)`.
Source: [[policy-level-fdt-learner]] §2.2 ("`cf(q) = q·M·f(q) + (1−q)(M·f(q) + K)`");
[[dp-core-2-inventory]] 030; [[dp-learner-nr-mandate]] target 5(c)
Kind: D -/
def cfNewcomb (M K : ℚ) (f : ℚ → ℚ) (q : ℚ) : ℚ := q * M * f q + (1 - q) * (M * f q + K)

/-- `cf(q) = M·f(q) + (1−q)·K`. Source: [[policy-level-fdt-learner]] §2.2. Kind: L -/
theorem cfNewcomb_eq (M K : ℚ) (f : ℚ → ℚ) (q : ℚ) :
    cfNewcomb M K f q = M * f q + (1 - q) * K := by
  unfold cfNewcomb; ring

/-- **Label probe `f = id`: the argmax over `[0, 1]` is `q = 1`** (slope `M − K > 0`), strictly
for `q < 1` — the policy-level learner one-boxes against the very Omega post 04's LIEDT two-boxes
against.
Source: [[policy-level-fdt-learner]] §2.2 ("Against a *label-probe* (`f(q) = q`): `cf = Mq +
(1−q)K`, maximized at `q = 1`"); [[dp-learner-nr-mandate]] target 5(c)
Kind: P
Fidelity: exact (argmax over `[0,1] ∩ ℚ` stated as `∀ q ∈ Icc 0 1, cf q ≤ cf 1`)
Hyps: (a) `K < M` -/
theorem newcomb_probe_argmax (M K : ℚ) (hKM : K < M) :
    (∀ q, 0 ≤ q → q ≤ 1 → cfNewcomb M K id q ≤ cfNewcomb M K id 1) ∧
    (∀ q, 0 ≤ q → q < 1 → cfNewcomb M K id q < cfNewcomb M K id 1) := by
  constructor
  · intro q _ hq1
    rw [cfNewcomb_eq, cfNewcomb_eq]; simp only [id]
    nlinarith
  · intro q _ hq1
    rw [cfNewcomb_eq, cfNewcomb_eq]; simp only [id]
    nlinarith

/-- **The threshold reader** `f(q) = r` for `q > ½`, `1 − r` otherwise — **`f(½) := 1 − r`**,
chosen explicitly (the note leaves `f(½)` undefined; known issue 2).
Source: [[policy-level-fdt-learner]] §2.2 ("threshold reader (`f = r` if `q > ½`, `1−r` if
`q < ½`)"); [[dp-learner-nr-mandate]] target 5(c) ("choose `f(½)` explicitly")
Kind: D
Fidelity: variant: `f(½)` fixed to `1 − r` -/
def thr (r q : ℚ) : ℚ := if 1 / 2 < q then r else 1 - r

/-- The grid `Π = {k/10 : k = 0, …, 10}` as labels. Source: [[policy-level-fdt-learner]] §1.1. Kind: D -/
def gridLabel (k : ℕ) : ℚ := (k : ℚ) / 10

/-- **The grid argmax of the threshold reader is `6/10` iff `r > ½ + 3K/(10M)`** (`0 < K < M`):
on the grid, every label above `½` collects `M·r + (1−q)K`, best at `6/10` with `M r + (2/5)K`;
every label at or below `½` collects `M(1−r) + (1−q)K`, best at `0` with `M(1−r) + K`; the
comparison `M r + 2K/5 > M(1−r) + K ⟺ r > ½ + 3K/(10M)`.
Source: [[policy-level-fdt-learner]] §2.2 ("the learner sits at `q = 0.6` and collects `M·r +
0.4K`"); [[dp-core-2-inventory]] 030; [[dp-learner-nr-mandate]] target 5(c)
Kind: P
Fidelity: exact (the grid comparison; the note's printed threshold `½ + K/(2M)` is the corner
comparison `newcomb_threshold_corner_iff` — findings, known issue 2)
Hyps: (a) `0 < K < M` -/
theorem newcomb_threshold_grid_iff (M K r : ℚ) (hK : 0 < K) (hKM : K < M) :
    (∀ k ∈ Finset.range 11, k ≠ 6 →
        cfNewcomb M K (thr r) (gridLabel k) < cfNewcomb M K (thr r) (gridLabel 6))
      ↔ 1 / 2 + 3 * K / (10 * M) < r := by
  have hM : 0 < M := by linarith
  have hthr : (1 / 2 + 3 * K / (10 * M) < r) ↔ 5 * M + 3 * K < 10 * M * r := by
    rw [show (1 : ℚ) / 2 + 3 * K / (10 * M) = (5 * M + 3 * K) / (10 * M) by field_simp; try ring,
      div_lt_iff₀ (by positivity)]
    constructor <;> intro h <;> linarith
  rw [hthr]
  constructor
  · intro h
    have h0 := h 0 (by simp) (by norm_num)
    simp only [cfNewcomb_eq, thr, gridLabel] at h0
    norm_num at h0
    linarith
  · intro h k hk hk6
    simp only [Finset.mem_range] at hk
    simp only [cfNewcomb_eq, thr, gridLabel]
    interval_cases k
    all_goals first
      | exact absurd rfl hk6
      | (norm_num; nlinarith)
      | norm_num

/-- **The corner comparison**: `cf(1) > cf(0)` for the threshold reader iff `r > ½ + K/(2M)` — the
note's printed one-box threshold (`0.5005` at `M = 1000, K = 1`), which is *not* the grid
threshold.
Source: [[policy-level-fdt-learner]] §2.2 ("One-box iff `r > ½ + K/2M = 0.5005`");
[[dp-learner-nr-mandate]] target 5(c) ("ship both and record the discrepancy")
Kind: P
Fidelity: exact
Hyps: (a) `0 < M` -/
theorem newcomb_threshold_corner_iff (M K r : ℚ) (hM : 0 < M) :
    cfNewcomb M K (thr r) 0 < cfNewcomb M K (thr r) 1 ↔ 1 / 2 + K / (2 * M) < r := by
  have key : (M * (1 - r) + K < M * r) ↔ 1 / 2 + K / (2 * M) < r := by
    rw [show (1 : ℚ) / 2 + K / (2 * M) = (M + K) / (2 * M) by field_simp; try ring,
      div_lt_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  rw [← key]
  simp only [cfNewcomb_eq, thr]
  have h1 : ¬ ((1 : ℚ) / 2 < 0) := by norm_num
  have h2 : (1 : ℚ) / 2 < 1 := by norm_num
  rw [if_neg h1, if_pos h2]
  constructor <;> intro h <;> linarith

/-- **Known issue 2**: with `f(½) := r` instead, the grid label `½` beats `6/10` (`K > 0`), so
`0.6` is not the grid argmax under that convention — the note's grid contains `0.5`, where its
`f` is undefined. (Only "beats `6/10`" is proved; that `½` is the grid argmax also needs it to
beat `0`, i.e. `r > ½ + K/(2M)`, which is not claimed here.)
Source: [[dp-learner-nr-mandate]] Known issue 2 ("with `f(½) = r` the argmax is `½`, not `0.6`")
Kind: N+ (a refutation of the printed `0.6` under the other convention) -/
theorem newcomb_threshold_half_wins (M K r : ℚ) (hK : 0 < K) :
    cfNewcomb M K (fun q => if 1 / 2 ≤ q then r else 1 - r) (gridLabel 6)
      < cfNewcomb M K (fun q => if 1 / 2 ≤ q then r else 1 - r) (gridLabel 5) := by
  simp only [cfNewcomb_eq, gridLabel]
  norm_num
  linarith

/-- **A policy-invariant box** (`f` constant): the argmax is `q = 0` (two-box), strictly for
`q > 0` — the case in which FDT and CDT agree because Omega is not predicting the policy.
Source: [[policy-level-fdt-learner]] §2.2 ("The partition test puts `b` in `W`, `cf(q) = M·P(b) +
(1−q)K`, and the learner two-boxes"); [[dp-learner-nr-mandate]] target 5(c)
Kind: P
Fidelity: exact
Hyps: (a) `0 < K` -/
theorem newcomb_invariant_argmax (M K c : ℚ) (hK : 0 < K) :
    (∀ q, 0 ≤ q → q ≤ 1 → cfNewcomb M K (fun _ => c) q ≤ cfNewcomb M K (fun _ => c) 0) ∧
    (∀ q, 0 < q → q ≤ 1 → cfNewcomb M K (fun _ => c) q < cfNewcomb M K (fun _ => c) 0) := by
  constructor
  · intro q hq0 _; simp only [cfNewcomb_eq]; nlinarith
  · intro q hq0 _; simp only [cfNewcomb_eq]; nlinarith

/-! ## TB(θ) at the policy level -/

/-- **TB(θ) at the policy level: the argmax is `q = 1` for every `θ < 1`**, strictly for `q < 1`
— the fixed forced mass is a constant at the policy level, so the separatrix `θ/(1−θ)` disappears
(`tbTheta_value`: `V(q) = −10θ + 10(1−θ)q`).
Source: [[policy-level-fdt-learner]] §2.6 ("`V(q) = −10θ + 10(1−θ)q`, slope positive for every
`θ < 1`, cross … so the separatrix `θ/(1−θ)` disappears"); [[dp-core-2-inventory]] 035;
[[dp-learner-nr-mandate]] target 5(d)
Kind: P
Fidelity: exact
Hyps: (a) `θ < 1` -/
theorem tb_policy_argmax (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hθ : θ < 1) :
    (∀ (q : ℚ) (q0 : 0 ≤ q) (q1 : q ≤ 1),
      value (procQ q q0 q1) (tbTheta θ h0 h1) ≤ value (procQ 1 zero_le_one le_rfl) (tbTheta θ h0 h1)) ∧
    (∀ (q : ℚ) (q0 : 0 ≤ q) (q1 : q ≤ 1), q < 1 →
      value (procQ q q0 q1) (tbTheta θ h0 h1) < value (procQ 1 zero_le_one le_rfl) (tbTheta θ h0 h1)) := by
  constructor
  · intro q _ q1
    rw [tbTheta_value, tbTheta_value]; simp [procQ]; nlinarith
  · intro q _ _ hq
    rw [tbTheta_value, tbTheta_value]; simp [procQ]; nlinarith

/-! ## XOR blackmail -/

/-- One case of XOR blackmail as a policy value: `D ∼ Bern(1/100)` (disaster `1000`), the letter
arrives iff `D` (`letterIffD = true`) or iff `¬D` (`false`), and the agent pays `100` with
probability `p` on receiving it: `−1000/100 − 100·p·P(letter)`.
Source: [[policy-level-fdt-learner]] §2.5 ("for `p < ½` the letter comes iff `D` and `cf(p) = −10
− p`; for `p > ½` it comes iff `¬D` and `cf(p) = −10 − 99p`"); [[dp-learner-nr-mandate]] target 5(e)
Kind: D -/
def cfXorCase (letterIffD : Bool) (p : ℚ) : ℚ :=
  -1000 * (1 / 100) - 100 * p * (if letterIffD then 1 / 100 else 99 / 100)

/-- **XOR blackmail with a threshold predictor** (`f(½)` on the `¬D` side): the letter comes iff
`D` when `p < ½` and iff `¬D` otherwise.
Source: [[policy-level-fdt-learner]] §2.5; [[dp-core-2-inventory]] 036; [[dp-learner-nr-mandate]] target 5(e)
Kind: D
Fidelity: variant: `f(½)` fixed to the `p ≥ ½` branch -/
def cfXor (p : ℚ) : ℚ := if p < 1 / 2 then cfXorCase true p else cfXorCase false p

/-- `cfXor p = if p < ½ then −10 − p else −10 − 99p`. Source: [[policy-level-fdt-learner]] §2.5. Kind: L -/
theorem cfXor_eq (p : ℚ) : cfXor p = if p < 1 / 2 then -10 - p else -10 - 99 * p := by
  unfold cfXor cfXorCase
  by_cases h : p < 1 / 2
  · rw [if_pos h, if_pos h]; norm_num; ring
  · rw [if_neg h, if_neg h]; norm_num; ring

/-- **XOR: refuse** — the argmax over `[0, 1]` is `p = 0`, strictly for `p > 0`.
Source: [[policy-level-fdt-learner]] §2.5 ("refuse"); [[dp-learner-nr-mandate]] target 5(e)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem cfXor_argmax :
    (∀ p, 0 ≤ p → p ≤ 1 → cfXor p ≤ cfXor 0) ∧ (∀ p, 0 < p → p ≤ 1 → cfXor p < cfXor 0) := by
  constructor
  · intro p hp0 _
    rw [cfXor_eq, cfXor_eq]
    split_ifs <;> norm_num <;> linarith
  · intro p hp0 _
    rw [cfXor_eq, cfXor_eq]
    split_ifs <;> norm_num <;> linarith

/-- **The jump** (target 5(f)): `cfXor` is not affine in the label — `cfXor (2/5) ≠ ½(cfXor 0 +
cfXor (4/5))`. The policy value is affine when the environment reads the label only through
draws (`tbTheta_value`, `mug1_value`) and not when it reads a threshold.
Source: [[policy-level-fdt-learner]] §2.5, §2.2; [[dp-learner-nr-mandate]] target 5(f)
Kind: N+ -/
theorem cfXor_not_affine : cfXor (2 / 5) ≠ (cfXor 0 + cfXor (4 / 5)) / 2 := by
  rw [cfXor_eq, cfXor_eq, cfXor_eq]; norm_num

/-! ## The mugging at the policy level -/

/-- **Counterfactual mugging as a policy value**: `V(procQ p)(mug1 x y) = p(y − x)/2`
(`dp-calibration`'s `mug1_value`); the coin is in `W`, the transfer in `R`.
Source: [[policy-level-fdt-learner]] §2.5 ("`cf(p) = ½(−xp) + ½(yp) = p(y−x)/2`");
[[decision-problems-v2]] Proposition 6; [[dp-learner-nr-mandate]] target 5(e)
Kind: L -/
theorem mug_policy_value (x y p : ℚ) (p0 : 0 ≤ p) (p1 : p ≤ 1) :
    value (procQ p p0 p1) (mug1 x y) = p * (y - x) / 2 := by
  rw [mug1_value]; simp [procQ]

/-- **Pay iff `y > x`**: the pay label beats the refuse label iff `x < y`.
Source: [[policy-level-fdt-learner]] §2.5 ("pay iff `y > x`"); [[dp-learner-nr-mandate]] target 5(e)
Kind: L -/
theorem mug_policy_pay_iff (x y : ℚ) :
    value (procQ 0 le_rfl zero_le_one) (mug1 x y) < value (procQ 1 zero_le_one le_rfl) (mug1 x y)
      ↔ x < y := by
  rw [mug_policy_value, mug_policy_value]
  constructor <;> intro h <;> linarith

end Cleanroom.Decision.DpLearnerNr
