import Cleanroom.Decision.DpDevicesCatalog.Values
import Cleanroom.Decision.DpLocalOpt.Ssa
import Cleanroom.Decision.DpCalibration.Bridge

set_option autoImplicit false

/-!
# `dp-devices-catalog` — T2–T4: Transparent Newcomb (v2 §7.2)

* T2 — Proposition 9's value table (eight entries as instances of `tnV1_value`/`tnV2_value`),
  the weak dominance `(1,2) ≥ (1,1)` in V1 (strict iff `p < 1`), the pure optima with their
  boundary ties, the empty-box deviation cost `(2p−1)L − pS > 0`, and the mixed optimum
  `IsOptimal (tnProc 1 1) (tnV2 p L S)` under `(2p−1)L > S` from the full polynomial (T2s), with
  the V1 contrast: at `p = 1`, `L = 3/2`, `S = 1` a *mixed* policy strictly beats every pure one.
* T3 — Proposition 10, the event-conditioned wedge: `MyopicallySatisfiedAt` (cross-multiplied),
  `(1,1)` is not myopically satisfied at `O_E`, every myopically satisfied procedure (mixed
  included, T3s) takes `both` at `d_E` surely and has `V ≤ (1−p)L + S < pL`, and the deviation
  moves `ν(O_E)` from `1 − p` to `p`.
* T4 — Remark 7.1: `occ(d_E) = Leaves` on V2, so Theorem 2's evaluator at `d_E` *is*
  `V(C[d_E ↦ m])`; `(1,1)` is `CoherentAt … E`; ZO-9's two labellings of one tree.

Every statement is over `ℚ` (disclosed once in `Values.lean`).
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

/-! ## Infrastructure on V2: payoff at a leaf, pure labels as `box` -/

/-- The payoff at a leaf of V2. Source: none: infrastructure. Kind: L -/
theorem tnV2_payoff (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) (x y : Box) (i : Fin 2)
    (act : Box) : payoff (tnV2 p h0 h1 L S) ⟨x, y, i, act, ()⟩ = tnPay L S (decide (i = 0), act) := by
  unfold tnV2 tnReal; simp

/-- `δ_both = box 0`. Source: none: infrastructure. Kind: L -/
theorem pure_both_eq_box : (FinDistr.pure Box.both : FinDistr ℚ Box) =
    FinDistr.box 0 le_rfl zero_le_one := by
  apply FinDistr.ext'; intro x; cases x <;> simp

/-- `δ_large = box 1`. Source: none: infrastructure. Kind: L -/
theorem pure_large_eq_box : (FinDistr.pure Box.large : FinDistr ℚ Box) =
    FinDistr.box 1 zero_le_one le_rfl := by
  apply FinDistr.ext'; intro x; cases x <;> simp

section table

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)

/-! ## T2 — Proposition 9's table -/

/-- V1, `(1,1)`: `pL`. Source: [[decision-problems-v2]] §7.2 table. Kind: N+ -/
theorem tnV1_value_11 :
    value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV1 p h0 h1 L S) = p * L := by
  rw [tnV1_value]; ring

/-- V1, `(1,2)`: `pL + (1−p)S`. Source: [[decision-problems-v2]] §7.2 table. Kind: N+ -/
theorem tnV1_value_12 :
    value (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV1 p h0 h1 L S) =
      p * L + (1 - p) * S := by
  rw [tnV1_value]; ring

/-- V1, `(2,1)`: `(1−p)(L+S)`. Source: [[decision-problems-v2]] §7.2 table. Kind: N+ -/
theorem tnV1_value_21 :
    value (tnProc 0 1 le_rfl zero_le_one zero_le_one le_rfl) (tnV1 p h0 h1 L S) =
      (1 - p) * (L + S) := by
  rw [tnV1_value]; ring

/-- V1, `(2,2)`: `(1−p)(L+S) + pS`. Source: [[decision-problems-v2]] §7.2 table. Kind: N+ -/
theorem tnV1_value_22 :
    value (tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one) (tnV1 p h0 h1 L S) =
      (1 - p) * (L + S) + p * S := by
  rw [tnV1_value]; ring

/-- V2, `(1,1)`: `pL`. Source: [[decision-problems-v2]] §7.2 table. Kind: N+ -/
theorem tnV2_value_11 :
    value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV2 p h0 h1 L S) = p * L := by
  rw [tnV2_value]; ring

/-- V2, `(1,2)`: `(1−p)L + pS`. Source: [[decision-problems-v2]] §7.2 table. Kind: N+ -/
theorem tnV2_value_12 :
    value (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV2 p h0 h1 L S) =
      (1 - p) * L + p * S := by
  rw [tnV2_value]; ring

/-- V2, `(2,1)`: `(1−p)(L+S)`. Source: [[decision-problems-v2]] §7.2 table. Kind: N+ -/
theorem tnV2_value_21 :
    value (tnProc 0 1 le_rfl zero_le_one zero_le_one le_rfl) (tnV2 p h0 h1 L S) =
      (1 - p) * (L + S) := by
  rw [tnV2_value]; ring

/-- V2, `(2,2)`: `(1−p)(L+S) + pS`. Source: [[decision-problems-v2]] §7.2 table. Kind: N+ -/
theorem tnV2_value_22 :
    value (tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one) (tnV2 p h0 h1 L S) =
      (1 - p) * (L + S) + p * S := by
  rw [tnV2_value]; ring

/-- **Proposition 9, V1's dominance**: `(1,2)` weakly dominates `(1,1)`, strictly iff `p < 1`
(for `S > 0`).
Source: [[decision-problems-v2]] §7.2 Proposition 9 ("`(1,2)` weakly dominates `(1,1)`
(strictly for `p < 1`)")
Kind: P
Fidelity: exact
Hyps: (a) `0 < S` -/
theorem tnV1_12_dominates_11 (hS : 0 < S) :
    value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV1 p h0 h1 L S) ≤
      value (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV1 p h0 h1 L S) ∧
    (value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV1 p h0 h1 L S) <
      value (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV1 p h0 h1 L S) ↔ p < 1) := by
  rw [tnV1_value_11, tnV1_value_12]
  constructor
  · nlinarith
  · constructor
    · intro h; nlinarith
    · intro h; nlinarith

/-- **Proposition 9, V1's pure optimum**: `(1,2)` is a maximiser among the four pure policies iff
`(2p−1)L ≥ pS`, and `(2,2)` is one iff `(2p−1)L ≤ pS` (the boundary is a tie). v2's "the
optimum is `(1,2)` iff `(2p−1)L > pS`, else `(2,2)`" is this pair read with "optimum" = attains
the maximum. Proposition 9's `S < L` and `½ < p` are not needed (only `0 < S` is), so the
theorem is stronger than the proposition's setting; audit round 1 dropped the two unused
hypotheses.
Source: [[decision-problems-v2]] §7.2 Proposition 9 ("the optimum is `(1,2)` iff
`(2p−1)L > pS`, else `(2,2)`")
Kind: P
Fidelity: stronger: pure policies, as v2's "policy" means (the mixed optimum is
`tnV1_mixed_beats_pure`); without Proposition 9's `S < L`, `½ < p`
Hyps: (a) `0 < S`, `0 ≤ p ≤ 1` -/
theorem tnV1_pureOpt_iff (hS : 0 < S) :
    ((2 * p - 1) * L ≥ p * S ↔
      value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV1 p h0 h1 L S) ≤
        value (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV1 p h0 h1 L S) ∧
      value (tnProc 0 1 le_rfl zero_le_one zero_le_one le_rfl) (tnV1 p h0 h1 L S) ≤
        value (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV1 p h0 h1 L S) ∧
      value (tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one) (tnV1 p h0 h1 L S) ≤
        value (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV1 p h0 h1 L S)) ∧
    ((2 * p - 1) * L ≤ p * S ↔
      value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV1 p h0 h1 L S) ≤
        value (tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one) (tnV1 p h0 h1 L S) ∧
      value (tnProc 0 1 le_rfl zero_le_one zero_le_one le_rfl) (tnV1 p h0 h1 L S) ≤
        value (tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one) (tnV1 p h0 h1 L S) ∧
      value (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV1 p h0 h1 L S) ≤
        value (tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one) (tnV1 p h0 h1 L S)) := by
  rw [tnV1_value_11, tnV1_value_12, tnV1_value_21, tnV1_value_22]
  constructor
  · constructor
    · intro h; refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
    · rintro ⟨-, -, h⟩; nlinarith
  · constructor
    · intro h; refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
    · rintro ⟨-, -, h⟩; nlinarith

/-- **Proposition 9's "no optimal V1 policy one-boxes at the empty box" holds for `p < 1` and
fails at `p = 1`**: for `p < 1` both one-boxing-at-`E` policies `(1,1)`, `(2,1)` are strictly
beaten by `(1,2)` or `(2,2)`; at `p = 1` with `L > S`, `(1,1)` ties `(1,2)` at `L` and is a pure
optimum that one-boxes at the (never-seen) empty box.
Source: [[decision-problems-v2]] §7.2 Proposition 9 ("no optimal V1 policy one-boxes at the
empty box") — boundary `p = 1` refuted, findings F4
Kind: P
Fidelity: exact (the `p < 1` half) + refutation at `p = 1`
Hyps: (a) `0 < S < L`, `½ < p` -/
theorem tnV1_empty_box_one_boxers (hS : 0 < S) (hLS : S < L) (hp : 1 / 2 < p) :
    (p < 1 →
      value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV1 p h0 h1 L S) <
        value (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV1 p h0 h1 L S) ∧
      value (tnProc 0 1 le_rfl zero_le_one zero_le_one le_rfl) (tnV1 p h0 h1 L S) <
        value (tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one) (tnV1 p h0 h1 L S)) ∧
    (p = 1 →
      value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV1 p h0 h1 L S) =
        value (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV1 p h0 h1 L S) ∧
      value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV1 p h0 h1 L S) = L ∧
      value (tnProc 0 1 le_rfl zero_le_one zero_le_one le_rfl) (tnV1 p h0 h1 L S) ≤ L ∧
      value (tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one) (tnV1 p h0 h1 L S) ≤ L) := by
  rw [tnV1_value_11, tnV1_value_12, tnV1_value_21, tnV1_value_22]
  constructor
  · intro hp1; constructor <;> nlinarith
  · rintro rfl; refine ⟨by ring, by ring, by linarith, by linarith⟩

/-- **Proposition 9, V2's pure optimum**: `(1,1)` is the unique maximiser among the four pure
policies iff `(2p−1)L > S` (and a maximiser iff `≥`).
Source: [[decision-problems-v2]] §7.2 Proposition 9 ("In V2(p), the optimum is `(1,1)` iff
`(2p−1)L > S`")
Kind: P
Fidelity: exact (pure policies; the mixed statement is `tnV2_large_isOptimal`)
Hyps: (a) `0 < S`, `p ≤ 1` -/
theorem tnV2_pureOpt_iff (hS : 0 < S) :
    (2 * p - 1) * L > S ↔
      value (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV2 p h0 h1 L S) <
        value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV2 p h0 h1 L S) ∧
      value (tnProc 0 1 le_rfl zero_le_one zero_le_one le_rfl) (tnV2 p h0 h1 L S) <
        value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV2 p h0 h1 L S) ∧
      value (tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one) (tnV2 p h0 h1 L S) <
        value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV2 p h0 h1 L S) := by
  rw [tnV2_value_11, tnV2_value_12, tnV2_value_21, tnV2_value_22]
  constructor
  · intro h; refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨-, -, h⟩; nlinarith

/-- **Proposition 9's last clause**: in V2, deviating at the empty box alone costs
`V(1,1) − V(1,2) = (2p−1)L − pS`, which is positive under `(2p−1)L > S` (via
`(2p−1)L − pS > S − pS = (1−p)S ≥ 0`).
Source: [[decision-problems-v2]] §7.2 Proposition 9 ("deviating at the empty box alone then
costs `(2p−1)L − pS > 0`")
Kind: P
Fidelity: exact
Hyps: (a) `0 < S`, `p ≤ 1` -/
theorem tnV2_emptyBox_deviation_cost (hS : 0 < S) :
    value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV2 p h0 h1 L S) -
      value (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV2 p h0 h1 L S) =
      (2 * p - 1) * L - p * S ∧
    ((2 * p - 1) * L > S → 0 < (2 * p - 1) * L - p * S) := by
  rw [tnV2_value_11, tnV2_value_12]
  refine ⟨by ring, fun h => ?_⟩
  nlinarith

/-- The N+ instance `p = ¾, L = 4, S = 1`: V2 values `3, 7/4, 5/4, 2` for `(1,1), (1,2), (2,1),
(2,2)`; V1 values `3, 13/4, 5/4, 2`. (The mandate's `5/2` for V2's `(1,2)` was a slip:
`(1−p)L + pS = 1 + 3/4`.)
Source: mandate T2 (the witness, recomputed)
Kind: N+ -/
theorem tn_instance_values :
    value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) = 3 ∧
    value (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) = 7/4 ∧
    value (tnProc 0 1 le_rfl zero_le_one zero_le_one le_rfl)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) = 5/4 ∧
    value (tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) = 2 ∧
    value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl)
      (tnV1 (3/4) (by norm_num) (by norm_num) 4 1) = 3 ∧
    value (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one)
      (tnV1 (3/4) (by norm_num) (by norm_num) 4 1) = 13/4 ∧
    value (tnProc 0 1 le_rfl zero_le_one zero_le_one le_rfl)
      (tnV1 (3/4) (by norm_num) (by norm_num) 4 1) = 5/4 ∧
    value (tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one)
      (tnV1 (3/4) (by norm_num) (by norm_num) 4 1) = 2 := by
  simp only [tnV1_value, tnV2_value]; norm_num

/-! ## T2s — the mixed optimum -/

/-- The key polynomial inequality behind `tnV2_large_isOptimal`: for `x, y ∈ [0,1]`,
`½ ≤ p ≤ 1`, `(1−p)x(1−y) + py(1−x) − (2p−1)xy(y−x) ≥ 0`.
Source: none: infrastructure
Kind: L -/
theorem tnV2_mixed_key (x y : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ (1 - p) * x * (1 - y) + p * y * (1 - x) - (2 * p - 1) * x * y * (y - x) := by
  have h2p : 0 ≤ 2 * p - 1 := by linarith
  have hA : 0 ≤ (1 - p) * x * (1 - y) :=
    mul_nonneg (mul_nonneg (by linarith) hx0) (by linarith)
  -- `p(1−x) − (2p−1)x(y−x) ≥ (1−x)(1−p) ≥ 0`
  have hB : (2 * p - 1) * x * (y - x) ≤ (2 * p - 1) * x * (1 - x) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg h2p hx0); linarith
  have hC : (2 * p - 1) * x * (1 - x) ≤ (2 * p - 1) * (1 - x) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith); nlinarith
  have hD : 0 ≤ p * (1 - x) - (2 * p - 1) * x * (y - x) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hx1)]
  have hE : 0 ≤ y * (p * (1 - x) - (2 * p - 1) * x * (y - x)) := mul_nonneg hy0 hD
  nlinarith

/-- **The mixed optimum of V2 (T2s)**: under `(2p−1)L > S > 0` (so `2p − 1 > 0` when `L > 0`),
`(1,1)` is `V`-optimal among *all* procedures, not only the four pure ones: `pL − V(x,y) =
((2p−1)L − S)(1−xy) + S·[(1−p)x(1−y) + py(1−x) − (2p−1)xy(y−x)] ≥ 0`. The maximum is at a
vertex.
Source: [[decision-problems-v2]] §7.2 Proposition 9 (mixed extension); mandate T2s
Kind: P
Fidelity: stronger (`IsOptimal`, every procedure)
Hyps: (a) `0 < S`, `(2p−1)L > S`, `½ ≤ p ≤ 1` -/
theorem tnV2_large_isOptimal (hS : 0 < S) (hp : 1 / 2 ≤ p) (hopt : (2 * p - 1) * L > S) :
    IsOptimal (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV2 p h0 h1 L S) := by
  intro C'
  rw [Proc.tnPt_eq_tnProc C', tnV2_value, tnV2_value]
  set x := (C' .F).w .large with hx
  set y := (C' .E).w .large with hy
  have hx0 : 0 ≤ x := (C' .F).nonneg _
  have hx1 : x ≤ 1 := (C' .F).w_le_one _
  have hy0 : 0 ≤ y := (C' .E).nonneg _
  have hy1 : y ≤ 1 := (C' .E).w_le_one _
  have hkey := tnV2_mixed_key p x y hx0 hx1 hy0 hy1 hp h1
  have hxy : 0 ≤ 1 - x * y := by nlinarith
  have hDS : 0 ≤ ((2 * p - 1) * L - S) * (1 - x * y) := mul_nonneg (by linarith) hxy
  have hSk := mul_nonneg hS.le hkey
  nlinarith

/-- **The V1 contrast: a mixed policy beats every pure one** at `p = 1`, `L = 3/2`, `S = 1`
(`L > S > 0`, `(2p−1)L > pS`): `V1(9/10, 0) = 77/50 > 3/2 = max{V1(1,1), V1(1,2), V1(2,1),
V1(2,2)}`. Proposition 9's "optimum" is over pure policies and does not extend to mixed ones
in V1, unlike V2 (`tnV2_large_isOptimal`).
Source: mandate T2 (the trap "v2's optimum ranges over pure policies"); findings F5
Kind: N+
Fidelity: exact -/
theorem tnV1_mixed_beats_pure :
    value (tnProc (9/10) 0 (by norm_num) (by norm_num) le_rfl zero_le_one)
        (tnV1 1 zero_le_one le_rfl (3/2) 1) = 77/50 ∧
    value (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV1 1 zero_le_one le_rfl (3/2) 1) = 3/2 ∧
    value (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV1 1 zero_le_one le_rfl (3/2) 1) = 3/2 ∧
    value (tnProc 0 1 le_rfl zero_le_one zero_le_one le_rfl) (tnV1 1 zero_le_one le_rfl (3/2) 1) = 0 ∧
    value (tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one) (tnV1 1 zero_le_one le_rfl (3/2) 1) = 1 ∧
    (3/2 : ℚ) < 77/50 := by
  simp only [tnV1_value]; norm_num

/-- **V1's one-boxer is not optimal** for `p < 1`, `S > 0`: `(1,2)` beats it (and at `p = 1`,
`L < 2S`, a mixed policy does, `tnV1_mixed_beats_pure`).
Source: mandate T2s ("a `¬ IsOptimal` witness for V1's one-boxer")
Kind: N+
Hyps: (a) `p < 1`, `0 < S` -/
theorem tnV1_large_not_isOptimal (hp : p < 1) (hS : 0 < S) :
    ¬ IsOptimal (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV1 p h0 h1 L S) := by
  intro h
  have := h (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one)
  rw [tnV1_value_11, tnV1_value_12] at this
  nlinarith

end table

/-! ## T3 — Proposition 10: the event-conditioned wedge -/

/-- **Myopic satisfaction at `d`** (v2 Proposition 10's predicate): `ν_{B,C}(O_d) > 0` and, for
every act `a`, `𝔼_{μ_{B,C}}[r ∣ O_d] ≥ 𝔼_{μ_{B,C[d↦a]}}[r ∣ O_d]`, written cross-multiplied and
division-free: `paySum_{C[d↦a]}(O_d) · ν_C(O_d) ≤ paySum_C(O_d) · ν_{C[d↦a]}(O_d)`. When both
`ν`'s are positive this is exactly the conditional inequality; when `ν_{C[d↦a]}(O_d) = 0` the
right conditional is undefined in v2 and the clause here reads `paySum_{C[d↦a]}(O_d) ≤ 0`
(`paySum` of a null event is `0`, so the clause holds) — on V2 with `p > 0` every deviation
realizes `O_E` (`tnV2_nu_E`), so the reading is never exercised there.
Source: [[decision-problems-v2]] §7.2 Proposition 10 ("say `C` is *myopically satisfied at*
`O_E` if …")
Kind: D
Fidelity: exact (cross-multiplied; the null-deviation clause is disclosed above) -/
def MyopicallySatisfiedAt {Ω ι : Type} [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
    [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] (obs : ι → Finset Ω)
    (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (d : ι) : Prop :=
  0 < nu C B (obs d) ∧
    ∀ a, paySum (C.deviatePure d a) B (obs d) * nu C B (obs d) ≤
      paySum C B (obs d) * nu (C.deviatePure d a) B (obs d)

section wedge

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) (x y : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
  (hy0 : 0 ≤ y) (hy1 : y ≤ 1)

/-- `ν_{(x,y)}(O_E) = xy(1−p) + (1−xy)p` on V2. Source: none: infrastructure. Kind: L -/
theorem tnV2_nu_E :
    nu (tnProc x y hx0 hx1 hy0 hy1) (tnV2 p h0 h1 L S) (tnObs .E) =
      x * y * (1 - p) + (1 - x * y) * p := by
  rw [nu_eq_sum, tnV2_sum]
  simp only [tnV2_world, tnV2_leafLaw]
  simp [Box.sum_univ, Fin.sum_univ_two, tnObs]
  ring

/-- `𝔼[r 1_{O_E}] = ν(O_E) · (1−y) S` on V2 (the empty branch pays `S` iff the real answer at
`d_E` is `both`). Source: none: infrastructure. Kind: L -/
theorem tnV2_paySum_E :
    paySum (tnProc x y hx0 hx1 hy0 hy1) (tnV2 p h0 h1 L S) (tnObs .E) =
      (x * y * (1 - p) + (1 - x * y) * p) * ((1 - y) * S) := by
  rw [paySum_eq_sum_ite, tnV2_sum]
  simp only [tnV2_world, tnV2_leafLaw, tnV2_payoff]
  simp [Box.sum_univ, Fin.sum_univ_two, tnObs, tnPay]
  ring

/-- `C[d_E ↦ both] = tnProc x 0`. Source: none: infrastructure. Kind: L -/
theorem tnProc_deviatePure_E_both :
    (tnProc x y hx0 hx1 hy0 hy1).deviatePure .E .both = tnProc x 0 hx0 hx1 le_rfl zero_le_one := by
  unfold Proc.deviatePure; rw [pure_both_eq_box, tnProc_deviate_E]

/-- `C[d_E ↦ large] = tnProc x 1`. Source: none: infrastructure. Kind: L -/
theorem tnProc_deviatePure_E_large :
    (tnProc x y hx0 hx1 hy0 hy1).deviatePure .E .large = tnProc x 1 hx0 hx1 zero_le_one le_rfl := by
  unfold Proc.deviatePure; rw [pure_large_eq_box, tnProc_deviate_E]

/-- **Proposition 10 (iii)**: `ν_{(1,1)}(O_E) = 1 − p` and `ν_{(1,2)}(O_E) = p` — the
deviation at `d_E` moves the probability of the very event conditioned on.
Source: [[decision-problems-v2]] §7.2 Proposition 10 ("`ν_{B,(1,1)}(O_E) = 1−p` while
`ν_{B,(1,2)}(O_E) = p`")
Kind: P
Fidelity: exact -/
theorem tnV2_nu_E_11_12 :
    nu (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV2 p h0 h1 L S) (tnObs .E) = 1 - p ∧
    nu (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV2 p h0 h1 L S) (tnObs .E) = p := by
  rw [tnV2_nu_E, tnV2_nu_E]; constructor <;> ring

/-- The two conditional payoff masses at `O_E`: under `(1,1)` it is `0`, under `(1,2)` it is
`S · ν_{(1,2)}(O_E)` — i.e. the conditional values `0` and `S`, cross-multiplied.
Source: [[decision-problems-v2]] §7.2 Proposition 10 ("conditional value `0` against the
deviation's `S`")
Kind: P
Fidelity: exact (cross-multiplied) -/
theorem tnV2_paySum_E_11_12 :
    paySum (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV2 p h0 h1 L S) (tnObs .E) = 0 ∧
    paySum (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV2 p h0 h1 L S) (tnObs .E) =
      S * nu (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one) (tnV2 p h0 h1 L S) (tnObs .E) := by
  rw [tnV2_paySum_E, tnV2_paySum_E, tnV2_nu_E]; constructor <;> ring

/-- **Proposition 10 (i)**: the `V`-optimal `(1,1)` is not myopically satisfied at `O_E` (for
`0 < p < 1`, `S > 0`): its `O_E`-conditional value is `0`, the deviation `d_E ↦ both`'s is `S`.
Source: [[decision-problems-v2]] §7.2 Proposition 10 ("The `V`-optimal `(1,1)` is not
myopically satisfied at `O_E`")
Kind: P
Fidelity: exact
Hyps: (a) `0 < p < 1`, `0 < S` -/
theorem tnV2_large_not_myopic (hp0 : 0 < p) (hp1 : p < 1) (hS : 0 < S) :
    ¬ MyopicallySatisfiedAt tnObs (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl)
      (tnV2 p h0 h1 L S) .E := by
  rintro ⟨-, h⟩
  have := h .both
  rw [tnProc_deviatePure_E_both, tnV2_paySum_E, tnV2_paySum_E, tnV2_nu_E, tnV2_nu_E] at this
  norm_num at this
  nlinarith [mul_pos (mul_pos hp0 hS) (sub_pos.2 hp1)]

/-- **Proposition 10 (ii), for every procedure (T3s)**: a myopically satisfied `(x, y)` takes
`both` at `d_E` surely (`y = 0`): the deviation to `both` realizes `O_E` with probability `p`
and pays `S` there, so the cross-multiplied clause forces `1 ≤ 1 − y`.
Source: [[decision-problems-v2]] §7.2 Proposition 10 ("every myopically satisfied policy takes
both there"); mandate T3s (mixed `y`: the `O_E`-conditional is affine in `y`)
Kind: P
Fidelity: stronger (every procedure, not only the four pure policies)
Hyps: (a) `0 < p`, `0 < S` -/
theorem tnV2_myopic_imp_both (hp0 : 0 < p) (hS : 0 < S)
    (h : MyopicallySatisfiedAt tnObs (tnProc x y hx0 hx1 hy0 hy1) (tnV2 p h0 h1 L S) .E) :
    y = 0 := by
  obtain ⟨hpos, hcl⟩ := h
  have := hcl .both
  rw [tnProc_deviatePure_E_both, tnV2_paySum_E, tnV2_paySum_E, tnV2_nu_E, tnV2_nu_E] at this
  rw [tnV2_nu_E] at hpos
  -- `p S ν ≤ ν (1−y) S p` with `ν, p, S > 0` gives `1 ≤ 1 − y`
  have hν : 0 < x * y * (1 - p) + (1 - x * y) * p := hpos
  have hpS : 0 < p * S * (x * y * (1 - p) + (1 - x * y) * p) := by positivity
  have hle : p * S * (x * y * (1 - p) + (1 - x * y) * p) * 1 ≤
      p * S * (x * y * (1 - p) + (1 - x * y) * p) * (1 - y) := by nlinarith
  have := le_of_mul_le_mul_left hle hpS
  linarith

/-- **Proposition 10 (ii), the value bound, for every procedure**: a procedure taking `both`
surely at `d_E` has `V ≤ (1−p)L + S`, and `(1−p)L + S < pL` iff `(2p−1)L > S`.
Source: [[decision-problems-v2]] §7.2 Proposition 10 ("has `V ≤ (1−p)L + S < pL`")
Kind: P
Fidelity: stronger (every `x`)
Hyps: (a) `0 ≤ S`, `p ≤ 1` -/
theorem tnV2_both_value_le (hS : 0 ≤ S) :
    value (tnProc x 0 hx0 hx1 le_rfl zero_le_one) (tnV2 p h0 h1 L S) ≤ (1 - p) * L + S ∧
    ((1 - p) * L + S < p * L ↔ (2 * p - 1) * L > S) := by
  rw [tnV2_value]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (mul_nonneg hx0 hS)]
  · constructor <;> intro h <;> linarith

/-- **Proposition 10 (ii) as v2 states it (pure policies)**: every myopically satisfied pure
policy `(x, y) ∈ {0,1}²` takes `both` at `d_E` and has `V ≤ (1−p)L + S < pL` under
`(2p−1)L > S`.
Source: [[decision-problems-v2]] §7.2 Proposition 10
Kind: C (composition of `tnV2_myopic_imp_both` and `tnV2_both_value_le`)
Fidelity: exact
Hyps: (a) `0 < p ≤ 1`, `0 < S`, `(2p−1)L > S` -/
theorem tnV2_myopic_pure (hp0 : 0 < p) (hS : 0 < S) (hopt : (2 * p - 1) * L > S)
    (_hx : x = 0 ∨ x = 1) (_hy : y = 0 ∨ y = 1)
    (h : MyopicallySatisfiedAt tnObs (tnProc x y hx0 hx1 hy0 hy1) (tnV2 p h0 h1 L S) .E) :
    y = 0 ∧ value (tnProc x y hx0 hx1 hy0 hy1) (tnV2 p h0 h1 L S) ≤ (1 - p) * L + S ∧
      (1 - p) * L + S < p * L := by
  have hy0' := tnV2_myopic_imp_both p h0 h1 L S x y hx0 hx1 hy0 hy1 hp0 hS h
  subst hy0'
  obtain ⟨hle, hiff⟩ := tnV2_both_value_le p h0 h1 L S x hx0 hx1 hS.le
  exact ⟨rfl, hle, hiff.mpr hopt⟩

/-- The N+ instance at `(¾, 4, 1)`: `(1,1)` is not myopically satisfied at `O_E`, its
conditional payoff mass is `0`, the deviation's is `S ν = 3/4`; `ν_{(1,1)}(O_E) = 1/4`,
`ν_{(1,2)}(O_E) = 3/4`; and `(1−p)L + S = 2 < 3 = pL`.
Source: mandate T3 (`N+` at `(¾, 4, 1)`)
Kind: N+ -/
theorem tnV2_wedge_instance :
    ¬ MyopicallySatisfiedAt tnObs (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) .E ∧
    nu (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) (tnObs .E) = 1/4 ∧
    nu (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) (tnObs .E) = 3/4 ∧
    paySum (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) (tnObs .E) = 3/4 ∧
    ((1 : ℚ) - 3/4) * 4 + 1 < 3/4 * 4 := by
  refine ⟨tnV2_large_not_myopic _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num), ?_, ?_, ?_,
    by norm_num⟩
  · rw [tnV2_nu_E]; norm_num
  · rw [tnV2_nu_E]; norm_num
  · rw [tnV2_paySum_E]; norm_num

end wedge

/-! ## T4 — Remark 7.1: occurrence-conditioning at `d_E` is the global evaluation -/

section remark71

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)

/-- **`occ(d_E) = Leaves` on V2**: the hypothetical query of `d_E` lies on every run.
Source: [[decision-problems-v2]] §7.2 Remark 7.1 ("in V2 the hypothetical query of `d_E` lies
on every run, so `occ(d_E) = Leaves`")
Kind: P
Fidelity: exact -/
theorem tnV2_occ_E : occ .E (tnV2 p h0 h1 L S) = Finset.univ := by
  ext ℓ
  unfold tnV2 at ℓ ⊢
  rcases ℓ with ⟨x, y, i, act, _⟩
  simp [count_decision]

/-- `μ_C(occ(d_E)) = 1` for every `C` on V2. Source: Remark 7.1. Kind: L -/
theorem tnV2_mass_occ_E (C : Proc TnPt (fun _ => Box) ℚ) :
    mass C (tnV2 p h0 h1 L S) (occ .E (tnV2 p h0 h1 L S)) = 1 := by
  rw [tnV2_occ_E, mass_univ]

/-- The off-occurrence payoff mass at `d_E` vanishes on V2 (no leaf is off `occ(d_E)`).
Source: Remark 7.1. Kind: L -/
theorem tnV2_offOcc_E (C : Proc TnPt (fun _ => Box) ℚ) :
    offOcc C (tnV2 p h0 h1 L S) .E = 0 := by
  unfold offOcc
  rw [tnV2_occ_E]
  simp

/-- **Remark 7.1**: on V2, Theorem 2's occurrence-conditioned evaluator at `d_E` *is* the global
evaluation: `ssaValue C B d_E m = V_B(C[d_E ↦ m])` for every procedure `C` and mixed `m`.
Composed from `ssaValue_eq_div` (dp-local-opt), `μ(occ(d_E)) = 1`, and Theorem 2's decomposition
`V(C[d↦m]) = ssaNum + offOcc` with `offOcc = 0`.
Source: [[decision-problems-v2]] §7.2 Remark 7.1 ("the occurrence-conditioned local evaluation
of Theorem 2 just *is* the global evaluation"); `zoo.md` ZO-9
Kind: C
Fidelity: exact
Hyps: none -/
theorem tnV2_ssaValue_E (C : Proc TnPt (fun _ => Box) ℚ) (m : FinDistr ℚ Box) :
    ssaValue C (tnV2 p h0 h1 L S) .E m = value (C.deviate .E m) (tnV2 p h0 h1 L S) := by
  rw [ssaValue_eq_div, tnV2_mass_occ_E, div_one, value_deviate_eq_ssaNum_add_offOcc,
    tnV2_offOcc_E, add_zero]

/-- **The one-boxer is Definition-22-coherent at the empty box** under `(2p−1)L > S`: for every
mixed deviation `y` at `d_E`, `V(1, y) ≤ V(1, 1) = pL` (via `pL − V(1,y) = (1−y)[(2p−1)L − pS +
y(2p−1)S] ≥ 0`). By `coherentAt_iff_ssa` this is Theorem 2's evaluator at `d_E` selecting
`large`, and by `tnV2_ssaValue_E` that evaluator is `V(C[d_E ↦ ·])` itself: the anthropic lens
recovers updatelessness at the empty box.
Source: [[decision-problems-v2]] §7.2 Remark 7.1 ("recovers updatelessness exactly"); mandate T4
Kind: P
Fidelity: exact (mixed Definition 22, A30)
Hyps: (a) `0 < S`, `½ ≤ p ≤ 1`, `(2p−1)L > S` -/
theorem tnV2_large_coherentAt_E (hS : 0 < S) (hp : 1 / 2 ≤ p) (hopt : (2 * p - 1) * L > S) :
    CoherentAt (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl) (tnV2 p h0 h1 L S) .E := by
  intro m
  rw [FinDistr.eq_box m, tnProc_deviate_E, tnV2_value, tnV2_value]
  set y := m.w .large
  have hy0 : 0 ≤ y := m.nonneg _
  have hy1 : y ≤ 1 := m.w_le_one _
  have h2p : 0 ≤ 2 * p - 1 := by linarith
  have hA : 0 ≤ (1 - y) * ((2 * p - 1) * L - p * S + y * (2 * p - 1) * S) := by
    apply mul_nonneg (by linarith)
    nlinarith [mul_nonneg (mul_nonneg hy0 h2p) hS.le, mul_nonneg (sub_nonneg.2 h1) hS.le]
  nlinarith

/-! ### ZO-9: one tree, two calibrated labellings, opposite verdicts -/

/-- ZO-9's procedure `C = (large; ½ large + ½ both)` at `(p, L, S) = (¾, 4, 1)`.
Source: `zoo.md` ZO-9
Kind: D -/
def zo9Proc : Proc TnPt (fun _ => Box) ℚ :=
  tnProc 1 (1/2) zero_le_one le_rfl (by norm_num) (by norm_num)

/-- ZO-9's tree. Source: `zoo.md` ZO-9. Kind: D -/
def zo9Tree : Tree TnW TnPt (fun _ => Box) ℚ := tnV2 (3/4) (by norm_num) (by norm_num) 4 1

/-- **The per-run-SSC-calibrated state at `d_E`** (`occ(d_E)` is every run, so it is the
prior-calibrated state): masses `(1, large) ↦ ½`, `(0, large) ↦ ¼`, `(0, both) ↦ ¼`.
Source: `zoo.md` ZO-9 (recomputed)
Kind: D -/
noncomputable def zo9PerRunState : State TnW ℚ :=
  calibratedState zo9Proc zo9Tree Finset.univ (nu_univ_pos _ _)

/-- `ν(O_E) = ½ > 0` under ZO-9's procedure. Source: none: infrastructure. Kind: L -/
theorem zo9_nu_E_pos : 0 < nu zo9Proc zo9Tree (tnObs .E) := by
  unfold zo9Proc zo9Tree; rw [tnV2_nu_E]; norm_num

/-- **The masked-OC labelling at `d_E`** (self-model `m = C(d_E)`, already full support):
`ν_C(· ∣ O_E)`.
Source: `zoo.md` ZO-9
Kind: D -/
noncomputable def zo9MaskedState : State TnW ℚ :=
  calibratedState zo9Proc zo9Tree (tnObs .E) zo9_nu_E_pos

/-- The per-run state is per-run SSC at `d_E`, with the three world masses `½, ¼, ¼`.
Source: `zoo.md` ZO-9
Kind: N+ -/
theorem zo9_perRunSSCAt :
    PerRunSSCAt (fun _ => zo9PerRunState) zo9Proc zo9Tree .E ∧
    zo9PerRunState.pr {(true, .large)} = 1/2 ∧
    zo9PerRunState.pr {(false, .large)} = 1/4 ∧
    zo9PerRunState.pr {(false, .both)} = 1/4 := by
  refine ⟨fun _ => perRunClausesAt_of_priorCalibrated_of_occ_univ zo9Proc zo9Tree _
    (tnV2_occ_E _ _ _ _ _) (priorCalibrated_calibratedState_univ _ _ _), ?_, ?_, ?_⟩ <;>
  · simp only [zo9PerRunState, calibratedState_pr, Finset.inter_univ, nu_univ, div_one]
    unfold zo9Proc zo9Tree
    rw [nu_eq_sum, tnV2_sum]
    simp only [tnV2_world, tnV2_leafLaw]
    simp [Box.sum_univ, Fin.sum_univ_two]
    try norm_num

/-- **ZO-9's verdicts**: at the per-run state the act values are `large ↦ 8/3`, `both ↦ 1`
(one-box); at the masked state they are `large ↦ 0`, `both ↦ 1` (two-box). The two labellings
are *states*, not procedures — the tree and the run law are the same object under both — so the
content is the two value pairs, kind `T`.
Source: `zoo.md` ZO-9 ("one tree, two calibrated labelings, equal laws, opposite EDT verdicts")
Kind: T
Fidelity: exact -/
theorem zo9_act_values :
    zo9PerRunState.V (tnActEv .E .large) = 8/3 ∧ zo9PerRunState.V (tnActEv .E .both) = 1 ∧
    zo9MaskedState.V (tnActEv .E .large) = 0 ∧ zo9MaskedState.V (tnActEv .E .both) = 1 := by
  simp only [zo9PerRunState, zo9MaskedState, calibratedState_V, Finset.inter_univ]
  unfold zo9Proc zo9Tree
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [paySum_eq_sum_ite, nu_eq_sum, tnV2_sum, tnV2_sum]
    simp only [tnV2_world, tnV2_leafLaw, tnV2_payoff]
    simp [Box.sum_univ, Fin.sum_univ_two, tnActEv, tnObs, tnPay]
    try norm_num

/-- The masked labelling is a masked-OC witness at `d_E` (self-model `m = C(d_E)`).
Source: `zoo.md` ZO-9
Kind: L -/
theorem zo9_maskedOCAt : MaskedOCAt (fun _ => zo9MaskedState) tnObs zo9Proc zo9Tree .E := by
  have hself : zo9Proc.deviate .E (zo9Proc .E) = zo9Proc := by
    funext d; by_cases hd : d = .E
    · subst hd; simp
    · simp [Proc.deviate_ne _ _ hd]
  refine Or.inl ⟨zo9Proc, ⟨zo9Proc .E, ?_, hself.symm⟩, zo9_nu_E_pos, ?_⟩
  · intro a; cases a <;> (simp [zo9Proc]; try norm_num)
  · exact strictClausesAt_calibratedState tnObs zo9Proc zo9Tree _ .E zo9_nu_E_pos rfl

end remark71

end Cleanroom.Decision.DpDevicesCatalog
