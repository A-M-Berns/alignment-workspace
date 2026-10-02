import Cleanroom.Decision.DpDutchBook.Defs
import Cleanroom.Decision.DpCalibration.MiniDevices
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# T9: Skyrms's Nash map on the miniature — DE = MSR, the exact one-sided slopes, a 2-cycle

Skyrms (TARK 1990, lines 118–145) defines, for a state of indecision `p` over the acts, the
covetability `COV(A) = max(U(A) − U(p), 0)` and the `k`-family of Nash maps
`p'_i = (k p_i + COV(A_i)) / (k + ∑_j COV(A_j))`, `k > 0` the index of caution. On Remark 4.3's
miniature under Definition 6 and strict observation calibration the act values at the label `q`
(the probability of `a`) are `U(a) = 2(1−q)`, `U(b) = q` (`dp-calibration`'s `limitVal_mini`,
`miniState_V_a/b`; the closed forms are used from here on), the status quo is
`U(q) = 3q(1−q)`, and the map in the `a`-coordinate is `nashMap k q` below.

**Reading, disclosed (ATTRIBUTION-UNVETTED as to Skyrms):** the informational feedback
"the predictor's law is my state of indecision" is C2-6's calibrate step, *not* TARK's Updating
by Emulation, and the identification `x = C(d)` holds only at the equilibrium (where the
sampler's label is the deliberator's final state). The theorems are about the map `nashMap`
as defined here.

* `nashMap_mem`, `nashMap_fixed_iff` — the map stays in `[0, 1]` and **its fixed points are
  exactly `q = 2/3` for every `k > 0`** (TARK's "all rules that seek the good have the same fixed
  points" instantiated); `nashMap_fixed_iff_msrAtD4` — **DE = MSR on the miniature**: a fixed
  point iff `MsrAtD4` for `procQ q` (via `miniature_adviceEdt_iff`).
* `nashMap_lower`, `nashMap_upper` — the two branches; `nashMap_lower_sub`, `nashMap_upper_sub`
  — the exact factorisations `N(q) − 2/3 = (q − 2/3) · slope(q)`, whose slope factors at `2/3`
  are `(k − 1/3)/k` (from below) and `(k − 4/3)/k` (from above): **the one-sided slopes as
  algebraic statements**, named honestly (`lowerSlope_at`, `upperSlope_at`), not
  `HasDerivWithinAt`.
* `nashMap_slope_product_lt_one_iff` — **the product of the absolute slopes is `< 1` iff
  `k > 4/15`**, for every `k > 0` (the alternating regime `k < 1/3` is where the condition
  bites; for `k ≥ 1/3` the below-slope lies in `[0, 1)`, `lowerSlope_at_mem`, and the product is
  `< 1` unconditionally). Not named `locally_attracting`: no neighbourhood theorem is proved.
* `nashMap_two_cycle` — **a 2-cycle at `k = 1/5`** (over `ℝ`): `nashMap (nashMap x) − x` changes
  sign on `[23/100, 24/100]` (exact rationals, `norm_num` through the branch formulas), so by the
  intermediate value theorem some `x` there has `N(N x) = x`, and `N x ≠ x` because `x ≠ 2/3`.
  Existence, not attraction.
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

section defs

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The miniature's act value of `a` at the label `q`: `2(1 − q)`.
Source: [[decision-problems-v2]] Remark 4.3; `dp-calibration` `limitVal_mini`, `miniState_V_a`
Kind: D -/
def miniUa (q : K) : K := 2 * (1 - q)

/-- The miniature's act value of `b` at the label `q`: `q`.
Source: [[decision-problems-v2]] Remark 4.3; `dp-calibration` `limitVal_mini`, `miniState_V_b`
Kind: D -/
def miniUb (q : K) : K := q

/-- The status quo's utility `U(q) = q·U(a) + (1−q)·U(b) = 3q(1−q)`.
Source: Skyrms TARK line 118 ("the average of the expected utilities of the pure acts")
Kind: D -/
def statusQuo (q : K) : K := q * miniUa q + (1 - q) * miniUb q

/-- Covetability of `a`: `max(U(a) − U(q), 0)`. Source: Skyrms TARK line 128. Kind: D -/
def covA (q : K) : K := max (miniUa q - statusQuo q) 0

/-- Covetability of `b`. Source: Skyrms TARK line 128. Kind: D -/
def covB (q : K) : K := max (miniUb q - statusQuo q) 0

/-- **Skyrms's Nash map with caution index `k`**, in the `a`-coordinate:
`N_k(q) = (k q + COV(a)) / (k + COV(a) + COV(b))`.
Source: Skyrms TARK lines 136–141 (`p'_i = [k p_i + COV(A_i)] / [k + ∑_j COV(A_j)]`); L3-13′
Kind: D
Fidelity: variant: the informational feedback is the calibrate step (C2-6), not TARK's Updating
by Emulation; `x = C(d)` only at the equilibrium (ATTRIBUTION-UNVETTED as to Skyrms) -/
def nashMap (k q : K) : K := (k * q + covA q) / (k + covA q + covB q)

/-- `U(q) = 3q(1−q)`. Source: SE-19 (`V_B(C) = 3q(1−q)`). Kind: L -/
theorem statusQuo_eq (q : K) : statusQuo q = 3 * q * (1 - q) := by
  unfold statusQuo miniUa miniUb; ring

/-- Covetabilities are non-negative. Source: none: infrastructure. Kind: L -/
theorem covA_nonneg (q : K) : 0 ≤ covA q := le_max_right _ _

/-- Covetabilities are non-negative. Source: none: infrastructure. Kind: L -/
theorem covB_nonneg (q : K) : 0 ≤ covB q := le_max_right _ _

/-- The denominator of the Nash map is positive. Source: none: infrastructure. Kind: L -/
theorem nashDenom_pos {k : K} (hk : 0 < k) (q : K) : 0 < k + covA q + covB q := by
  linarith [covA_nonneg q, covB_nonneg q]

/-- Below `2/3` the act `a` is covetable by `(1−q)(2−3q)`. Source: none: infrastructure. Kind: L -/
theorem covA_of_le {q : K} (h : q ≤ 2 / 3) : covA q = (1 - q) * (2 - 3 * q) := by
  unfold covA
  rw [statusQuo_eq]
  have e : miniUa q - 3 * q * (1 - q) = (1 - q) * (2 - 3 * q) := by unfold miniUa; ring
  rw [e]
  exact max_eq_left (mul_nonneg (by linarith) (by linarith))

/-- Above `2/3` the act `a` is not covetable. Source: none: infrastructure. Kind: L -/
theorem covA_of_ge {q : K} (h : 2 / 3 ≤ q) (h1 : q ≤ 1) : covA q = 0 := by
  unfold covA
  rw [statusQuo_eq]
  have e : miniUa q - 3 * q * (1 - q) = (1 - q) * (2 - 3 * q) := by unfold miniUa; ring
  rw [e]
  exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))

/-- Below `2/3` the act `b` is not covetable. Source: none: infrastructure. Kind: L -/
theorem covB_of_le {q : K} (h0 : 0 ≤ q) (h : q ≤ 2 / 3) : covB q = 0 := by
  unfold covB
  rw [statusQuo_eq]
  have e : miniUb q - 3 * q * (1 - q) = q * (3 * q - 2) := by unfold miniUb; ring
  rw [e]
  exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos h0 (by linarith))

/-- Above `2/3` the act `b` is covetable by `q(3q−2)`. Source: none: infrastructure. Kind: L -/
theorem covB_of_ge {q : K} (h0 : 0 ≤ q) (h : 2 / 3 ≤ q) : covB q = q * (3 * q - 2) := by
  unfold covB
  rw [statusQuo_eq]
  have e : miniUb q - 3 * q * (1 - q) = q * (3 * q - 2) := by unfold miniUb; ring
  rw [e]
  exact max_eq_left (mul_nonneg h0 (by linarith))

/-- **The lower branch**: for `0 ≤ q ≤ 2/3`,
`N_k(q) = (k q + (1−q)(2−3q)) / (k + (1−q)(2−3q))`.
Source: L3-13′ (the exact form); mandate T9(b)
Kind: L -/
theorem nashMap_lower (k : K) {q : K} (h0 : 0 ≤ q) (h : q ≤ 2 / 3) :
    nashMap k q = (k * q + (1 - q) * (2 - 3 * q)) / (k + (1 - q) * (2 - 3 * q)) := by
  unfold nashMap
  rw [covA_of_le h, covB_of_le h0 h, add_zero]

/-- **The upper branch**: for `2/3 ≤ q ≤ 1`, `N_k(q) = k q / (k + q(3q−2))`.
Source: L3-13′; mandate T9(b)
Kind: L -/
theorem nashMap_upper (k : K) {q : K} (h : 2 / 3 ≤ q) (h1 : q ≤ 1) :
    nashMap k q = k * q / (k + q * (3 * q - 2)) := by
  unfold nashMap
  rw [covA_of_ge h h1, covB_of_ge (by linarith) h, add_zero, add_zero]

/-- **T9(a): the Nash map keeps `[0, 1]`.**
Source: Skyrms TARK line 136 (a map on the simplex); mandate T9(a)
Kind: P
Hyps: (a) `0 < k`, `0 ≤ q ≤ 1` -/
theorem nashMap_mem {k : K} (hk : 0 < k) {q : K} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    0 ≤ nashMap k q ∧ nashMap k q ≤ 1 := by
  unfold nashMap
  have hd := nashDenom_pos hk q
  constructor
  · exact div_nonneg (by nlinarith [covA_nonneg q]) hd.le
  · rw [div_le_one hd]
    nlinarith [covB_nonneg q]

/-- **T9(a): the fixed points of the Nash map are exactly `q = 2/3`, for every `k > 0`.**
At `q = 1` the act `b` is covetable, at `q = 0` the act `a` is; between, the fixed-point equation
reduces on each branch to `(1−q)²(2−3q) = 0` resp. `q²(3q−2) = 0`. TARK's "All dynamical rules
which seek the good have the same fixed points. These are the states in which the utility of
the status quo is maximal", instantiated on the miniature.
Source: Skyrms TARK lines 120–121; L3-13′; mandate T9(a)
Kind: P
Fidelity: exact
Hyps: (a) `0 < k`, `0 ≤ q ≤ 1` -/
theorem nashMap_fixed_iff {k : K} (hk : 0 < k) {q : K} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    nashMap k q = q ↔ q = 2 / 3 := by
  constructor
  · intro hfix
    rcases le_or_gt q (2 / 3) with hle | hgt
    · rw [nashMap_lower k h0 hle] at hfix
      have hd : 0 < k + (1 - q) * (2 - 3 * q) := by
        have : 0 ≤ (1 - q) * (2 - 3 * q) := mul_nonneg (by linarith) (by linarith)
        linarith
      rw [div_eq_iff hd.ne'] at hfix
      have hz : (1 - q) ^ 2 * (2 - 3 * q) = 0 := by linear_combination hfix
      rcases mul_eq_zero.mp hz with hz | hz
      · exfalso; have : 1 - q = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz; linarith
      · linarith
    · rw [nashMap_upper k hgt.le h1] at hfix
      have hd : 0 < k + q * (3 * q - 2) := by
        have : 0 ≤ q * (3 * q - 2) := mul_nonneg h0 (by linarith)
        linarith
      rw [div_eq_iff hd.ne'] at hfix
      have hz : q ^ 2 * (3 * q - 2) = 0 := by linear_combination -hfix
      rcases mul_eq_zero.mp hz with hz | hz
      · exfalso; have : q = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz; linarith
      · linarith
  · rintro rfl
    rw [nashMap_lower k (by norm_num) le_rfl]
    field_simp
    ring

/-- The slope factor of the upper branch: `(k − 2q) / (k + q(3q−2))`.
Source: mandate T9(b)
Kind: D -/
def upperSlope (k q : K) : K := (k - 2 * q) / (k + q * (3 * q - 2))

/-- The slope factor of the lower branch: `(k + q − 1) / (k + (1−q)(2−3q))`.
Source: mandate T9(b)
Kind: D -/
def lowerSlope (k q : K) : K := (k + q - 1) / (k + (1 - q) * (2 - 3 * q))

/-- **The upper branch factorised at the fixed point**: `N_k(q) − 2/3 = (q − 2/3) · upperSlope k q`
for `2/3 ≤ q ≤ 1` (an exact identity; the difference quotient *is* `upperSlope`).
Source: mandate T9(b) ("the algebraic statement … is acceptable if named honestly")
Kind: P
Hyps: (a) `0 < k`, `2/3 ≤ q ≤ 1` -/
theorem nashMap_upper_sub {k : K} (hk : 0 < k) {q : K} (h : 2 / 3 ≤ q) (h1 : q ≤ 1) :
    nashMap k q - 2 / 3 = (q - 2 / 3) * upperSlope k q := by
  rw [nashMap_upper k h h1]
  unfold upperSlope
  have hd : k + q * (3 * q - 2) ≠ 0 := by
    have : 0 ≤ q * (3 * q - 2) := mul_nonneg (by linarith) (by linarith)
    linarith
  rw [mul_div_assoc', eq_div_iff hd, sub_mul, div_mul_cancel₀ _ hd]
  ring

/-- **The lower branch factorised at the fixed point**: `N_k(q) − 2/3 = (q − 2/3) · lowerSlope k q`
for `0 ≤ q ≤ 2/3`.
Source: mandate T9(b)
Kind: P
Hyps: (a) `0 < k`, `0 ≤ q ≤ 2/3` -/
theorem nashMap_lower_sub {k : K} (hk : 0 < k) {q : K} (h0 : 0 ≤ q) (h : q ≤ 2 / 3) :
    nashMap k q - 2 / 3 = (q - 2 / 3) * lowerSlope k q := by
  rw [nashMap_lower k h0 h]
  unfold lowerSlope
  have hd : k + (1 - q) * (2 - 3 * q) ≠ 0 := by
    have : 0 ≤ (1 - q) * (2 - 3 * q) := mul_nonneg (by linarith) (by linarith)
    linarith
  rw [mul_div_assoc', eq_div_iff hd, sub_mul, div_mul_cancel₀ _ hd]
  ring

/-- **The one-sided slope from above is `(k − 4/3)/k`** (the slope factor at `2/3`).
Source: L3-13′ ("slopes"); dp-sl-2-052; mandate T9(b)
Kind: P
Hyps: (a) none -/
theorem upperSlope_at (k : K) : upperSlope k (2 / 3) = (k - 4 / 3) / k := by
  unfold upperSlope
  rw [show (2 / 3 : K) * (3 * (2 / 3) - 2) = 0 by norm_num, add_zero]
  congr 1; ring

/-- **The one-sided slope from below is `(k − 1/3)/k`.**
Source: L3-13′; dp-sl-2-052; mandate T9(b)
Kind: P
Hyps: (a) none -/
theorem lowerSlope_at (k : K) : lowerSlope k (2 / 3) = (k - 1 / 3) / k := by
  unfold lowerSlope
  rw [show (1 - 2 / 3 : K) * (2 - 3 * (2 / 3)) = 0 by norm_num, add_zero]
  congr 1; ring

/-- For `k ≥ 1/3` the below-slope lies in `[0, 1)` (the non-alternating regime).
Source: mandate T9(c)
Kind: L -/
theorem lowerSlope_at_mem {k : K} (hk : 1 / 3 ≤ k) :
    0 ≤ (k - 1 / 3) / k ∧ (k - 1 / 3) / k < 1 := by
  have hk0 : 0 < k := by linarith
  constructor
  · exact div_nonneg (by linarith) hk0.le
  · rw [div_lt_one hk0]; linarith

/-- **T9(c): the product of the absolute one-sided slopes at `2/3` is `< 1` iff `k > 4/15`**, for
every `k > 0`. In the alternating regime `k < 1/3` both slopes are negative and the condition is
`(4/3 − k)(1/3 − k) < k²`, i.e. `k > 4/15`; for `k ≥ 1/3` the product is `< 1` unconditionally.
Named for what it is — no neighbourhood-convergence theorem is proved.
Source: dp-sl-2-052 (the `4/15` threshold); L3 Open 7; mandate T9(c)
Kind: P
Fidelity: exact (the algebraic threshold; attraction itself is not claimed)
Hyps: (a) `0 < k` -/
theorem nashMap_slope_product_lt_one_iff {k : K} (hk : 0 < k) :
    |(k - 4 / 3) / k| * |(k - 1 / 3) / k| < 1 ↔ 4 / 15 < k := by
  rw [abs_div, abs_div, abs_of_pos hk, div_mul_div_comm, div_lt_one (mul_pos hk hk)]
  rcases lt_or_ge k (1 / 3) with h13 | h13
  · rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    constructor <;> intro h <;> nlinarith
  · rcases lt_or_ge k (4 / 3) with h43 | h43
    · rw [abs_of_neg (by linarith), abs_of_nonneg (by linarith)]
      constructor
      · intro _; linarith
      · intro _; nlinarith [sq_nonneg (k - 5 / 12)]
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      constructor <;> intro h <;> nlinarith

end defs

/-! ## DE = MSR on the miniature -/

section demsr

/-- `AdviceEdt` on the miniature is its clause at the single point `()`.
Source: none: infrastructure. Kind: L -/
theorem miniature_adviceEdt_iff_clause (C : Proc Unit (fun _ => Act2) ℚ) :
    AdviceEdt miniObs miniActEv C miniature ↔
      ∀ a, 0 < (C ()).w a → nuPoly C miniature (miniActEv () a ∩ miniObs ()) ≠ 0 ∧
        ∀ b, nuPoly C miniature (miniActEv () b ∩ miniObs ()) ≠ 0 →
          limitVal C miniature (miniActEv () b ∩ miniObs ()) ≤
            limitVal C miniature (miniActEv () a ∩ miniObs ()) := by
  constructor
  · intro h
    exact h () miniature_queried (miniature_nuPoly_obs_ne_zero C) ⟨.a, nuPoly_mini_live_ne_zero C .a⟩
  · intro h d _ _ _
    cases d
    exact h

/-- **`MsrAtD4` on the miniature is exactly `q = 2/3`** (every act is tremble-realizable, so
`MsrAtD4` is the `AdviceEdt` clause, and `dp-calibration`'s `miniature_adviceEdt_iff` decides it).
Source: `calibration.md` CA-13′/CA-14′ (D4 = {2/3}); `repair/C2.md` C2-7 (instance: miniature `2/3`)
Kind: C
Fidelity: exact
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem miniature_msrAtD4_iff (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    MsrAtD4 miniObs miniActEv (procQ q h0 h1) miniature () ↔ q = 2 / 3 := by
  rw [msrAtD4_iff_adviceEdt_clause miniObs miniActEv _ miniature () (nuPoly_mini_live_ne_zero _),
    ← miniature_adviceEdt_iff_clause, miniature_adviceEdt_iff]

/-- **T9(a), DE = MSR on the miniature**: `q` is a fixed point of Skyrms's Nash map (for any
caution index) iff `procQ q` is D4-approved at its own label. The general identity DE = MSR is
`dp-calib-limits` T4(f)'s and is not stated here.
Source: `repair/C2.md` C2-6 (DE = MSR); `sl-defensible-claims.md` S10; mandate T9(a)
Kind: C
Fidelity: exact on the miniature
Hyps: (a) `0 < k`, `0 ≤ q ≤ 1` -/
theorem nashMap_fixed_iff_msrAtD4 {k : ℚ} (hk : 0 < k) (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    nashMap k q = q ↔ MsrAtD4 miniObs miniActEv (procQ q h0 h1) miniature () := by
  rw [nashMap_fixed_iff hk h0 h1, miniature_msrAtD4_iff q h0 h1]

end demsr

/-! ## A 2-cycle for a small caution index (over `ℝ`) -/

section twoCycle

/-- The Nash map is continuous in `q` for `k > 0`. Source: none: infrastructure. Kind: L -/
theorem nashMap_continuous {k : ℝ} (hk : 0 < k) : Continuous (nashMap k) := by
  have hA : Continuous (covA (K := ℝ)) := by
    show Continuous (fun q : ℝ => max (2 * (1 - q) - (q * (2 * (1 - q)) + (1 - q) * q)) 0)
    exact Continuous.max (by fun_prop) continuous_const
  have hB : Continuous (covB (K := ℝ)) := by
    show Continuous (fun q : ℝ => max (q - (q * (2 * (1 - q)) + (1 - q) * q)) 0)
    exact Continuous.max (by fun_prop) continuous_const
  unfold nashMap
  exact Continuous.div ((continuous_const.mul continuous_id).add hA)
    ((continuous_const.add hA).add hB) fun q => (nashDenom_pos hk q).ne'

/-- At `k = 1/5`, `N(23/100) = 10547/12087` (lower branch, exact).
Source: none: infrastructure (T9(d) bracket). Kind: L -/
theorem nashMap_fifth_lo : nashMap (1 / 5 : ℝ) (23 / 100) = 10547 / 12087 := by
  rw [nashMap_lower _ (by norm_num) (by norm_num)]; norm_num

/-- At `k = 1/5`, `N(24/100) = 638/733` (lower branch, exact).
Source: none: infrastructure (T9(d) bracket). Kind: L -/
theorem nashMap_fifth_hi : nashMap (1 / 5 : ℝ) (24 / 100) = 638 / 733 := by
  rw [nashMap_lower _ (by norm_num) (by norm_num)]; norm_num

/-- `N(N(23/100)) − 23/100 > 0` at `k = 1/5` (upper branch at `10547/12087 ≥ 2/3`).
Source: none: infrastructure (T9(d) bracket). Kind: L -/
theorem twoCycle_sign_lo :
    0 < nashMap (1 / 5 : ℝ) (nashMap (1 / 5) (23 / 100)) - 23 / 100 := by
  rw [nashMap_fifth_lo, nashMap_upper _ (by norm_num) (by norm_num)]; norm_num

/-- `N(N(24/100)) − 24/100 < 0` at `k = 1/5` (upper branch at `638/733 ≥ 2/3`).
Source: none: infrastructure (T9(d) bracket). Kind: L -/
theorem twoCycle_sign_hi :
    nashMap (1 / 5 : ℝ) (nashMap (1 / 5) (24 / 100)) - 24 / 100 < 0 := by
  rw [nashMap_fifth_hi, nashMap_upper _ (by norm_num) (by norm_num)]; norm_num

/-- **T9(d): a 2-cycle of the Nash map at caution index `k = 1/5`**: some `x ∈ [23/100, 24/100]`
has `N(N x) = x` and `N x ≠ x` (the second iterate minus the identity changes sign on the
interval — exact rational values at the endpoints — and the only fixed point is `2/3`).
Existence by the intermediate value theorem; nothing about attraction is claimed.
Source: dp-sl-2-052 ("oscillation for small caution index"); SL-27(b)(iii); mandate T9(d) (the
`0.237` bracket, plan §0.4 rule 4)
Kind: N+
Fidelity: exact (existence on a stated rational interval)
Hyps: (a) none -/
theorem nashMap_two_cycle :
    ∃ x : ℝ, x ∈ Set.Icc (23 / 100 : ℝ) (24 / 100) ∧
      nashMap (1 / 5) (nashMap (1 / 5) x) = x ∧ nashMap (1 / 5) x ≠ x := by
  have hk : (0 : ℝ) < 1 / 5 := by norm_num
  let F : ℝ → ℝ := fun x => nashMap (1 / 5) (nashMap (1 / 5) x) - x
  have hF : Continuous F :=
    ((nashMap_continuous hk).comp (nashMap_continuous hk)).sub continuous_id
  have hmem : (0 : ℝ) ∈ Set.Icc (F (24 / 100)) (F (23 / 100)) :=
    ⟨twoCycle_sign_hi.le, twoCycle_sign_lo.le⟩
  obtain ⟨x, hx, hFx⟩ := intermediate_value_Icc' (by norm_num : (23 / 100 : ℝ) ≤ 24 / 100)
    hF.continuousOn hmem
  refine ⟨x, hx, sub_eq_zero.mp hFx, fun hfix => ?_⟩
  have h23 : x = 2 / 3 := (nashMap_fixed_iff hk (by linarith [hx.1]) (by linarith [hx.2])).mp hfix
  linarith [hx.2]

end twoCycle

end Cleanroom.Decision.DpDutchBook
