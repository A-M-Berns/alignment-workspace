import Cleanroom.Found.LiAsympCalc.Ramp

/-!
# `def-self-trust` — target 6a: ramp arithmetic

Pure real-number facts about FAF's continuous threshold indicator
`ctsInd δ x t = min 1 (max 0 ((x − t)/δ))` that the corpus's Lemma C / Theorem B
([[route-transitivity]] §4, §6.1) and the gate sandwich (vq-wiki-2-008) use and that neither
FAF nor `li-asymp-calc` provides (verified by grep on 2026-09-30): the `1/δ`-Lipschitz bound,
monotonicity in each argument, the two-sided sandwich on `η`-good days, and the signed products
`(x − t)·ctsInd δ x t ≥ 0`, `(x − t)·ctsInd δ t x ≤ 0` ("no false positives") that carry the
world-value step of `est` (target 2).

Every width carries `0 < δ` (mandate design decision 5: `ctsInd 0 x y = 0` since `x / 0 = 0`).
-/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology
open Cleanroom.Found.LiAsympCalc

/-- The clamp `u ↦ min 1 (max 0 u)` is 1-Lipschitz.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma abs_clamp_sub_clamp_le (a b : ℝ) :
    |min 1 (max 0 a) - min 1 (max 0 b)| ≤ |a - b| := by
  calc |min 1 (max 0 a) - min 1 (max 0 b)|
      ≤ max |(1 : ℝ) - 1| |max 0 a - max 0 b| := abs_min_sub_min_le_max 1 (max 0 a) 1 (max 0 b)
    _ = |max 0 a - max 0 b| := by simp
    _ = |max a 0 - max b 0| := by rw [max_comm 0 a, max_comm 0 b]
    _ ≤ |a - b| := abs_max_sub_max_le_abs a b 0

/-- **The ramp is `1/δ`-Lipschitz in its first argument, and bounded by `1`:**
`|ctsInd δ x t − ctsInd δ y t| ≤ min 1 (|x − y| / δ)` for `0 < δ`.
Source: vq-wiki-2-008 ([[route-transitivity]] §6.1 line 205: "the ramp is `1/δ`-Lipschitz");
vq-wiki-063 (Lemma C: `|û_n − β_n| ≤ e_n`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_lipschitz {δ : ℚ} (hδ : 0 < δ) (x y t : ℝ) :
    |ctsInd δ x t - ctsInd δ y t| ≤ min 1 (|x - y| / (δ : ℝ)) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  refine le_min ?_ ?_
  · rw [abs_le]
    have h1 := ctsInd_mem_Icc δ x t
    have h2 := ctsInd_mem_Icc δ y t
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · unfold ctsInd
    calc |min 1 (max 0 ((x - t) / (δ : ℝ))) - min 1 (max 0 ((y - t) / (δ : ℝ)))|
        ≤ |(x - t) / (δ : ℝ) - (y - t) / (δ : ℝ)| := abs_clamp_sub_clamp_le _ _
      _ = |x - y| / (δ : ℝ) := by
          rw [← sub_div, abs_div, abs_of_pos hδR]
          congr 2; ring

/-- The ramp is `1/δ`-Lipschitz in its threshold argument as well.
Source: vq-wiki-2-008
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_lipschitz_right {δ : ℚ} (hδ : 0 < δ) (x t t' : ℝ) :
    |ctsInd δ x t - ctsInd δ x t'| ≤ |t - t'| / (δ : ℝ) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold ctsInd
  calc |min 1 (max 0 ((x - t) / (δ : ℝ))) - min 1 (max 0 ((x - t') / (δ : ℝ)))|
      ≤ |(x - t) / (δ : ℝ) - (x - t') / (δ : ℝ)| := abs_clamp_sub_clamp_le _ _
    _ = |t - t'| / (δ : ℝ) := by
        rw [← sub_div, abs_div, abs_of_pos hδR, show x - t - (x - t') = -(t - t') by ring,
          abs_neg]

/-- The ramp is monotone in its first argument (for `0 < δ`).
Source: vq-wiki-2-008 ("`1/δ`-Lipschitz and monotone")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_mono_left {δ : ℚ} (hδ : 0 < δ) {x y : ℝ} (hxy : x ≤ y) (t : ℝ) :
    ctsInd δ x t ≤ ctsInd δ y t := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold ctsInd
  apply min_le_min_left
  apply max_le_max_left
  exact div_le_div_of_nonneg_right (by linarith) hδR.le

/-- The ramp is antitone in its threshold argument (for `0 < δ`).
Source: vq-wiki-2-008
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_anti_right {δ : ℚ} (hδ : 0 < δ) (x : ℝ) {t t' : ℝ} (htt : t ≤ t') :
    ctsInd δ x t' ≤ ctsInd δ x t := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold ctsInd
  apply min_le_min_left
  apply max_le_max_left
  exact div_le_div_of_nonneg_right (by linarith) hδR.le

/-- **The gate sandwich on `η`-good days** (vq-wiki-2-008): if `|c − y| ≤ η` then
`Ind_δ(y > t + η) ≤ Ind_δ(c > t) ≤ Ind_δ(y > t − η)`.
Source: vq-wiki-2-008 ([[route-transitivity]] §6.1 line 205)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_sandwich_of_abs_le {δ : ℚ} (hδ : 0 < δ) {c y η : ℝ} (h : |c - y| ≤ η) (t : ℝ) :
    ctsInd δ y (t + η) ≤ ctsInd δ c t ∧ ctsInd δ c t ≤ ctsInd δ y (t - η) := by
  rw [abs_le] at h
  constructor
  · calc ctsInd δ y (t + η) = ctsInd δ (y - η) t := by
          unfold ctsInd; congr 2; ring
      _ ≤ ctsInd δ c t := ctsInd_mono_left hδ (by linarith) t
  · calc ctsInd δ c t ≤ ctsInd δ (y + η) t := ctsInd_mono_left hδ (by linarith) t
      _ = ctsInd δ y (t - η) := by
          unfold ctsInd; congr 2; ring

/-- On an `η`-good day the two gates differ by at most `η/δ`.
Source: vq-wiki-2-008 ("`|û_n − β_n| ≤ η/δ`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem abs_ctsInd_sub_le_of_abs_le {δ : ℚ} (hδ : 0 < δ) {c y η : ℝ} (h : |c - y| ≤ η)
    (t : ℝ) : |ctsInd δ c t - ctsInd δ y t| ≤ η / (δ : ℝ) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  calc |ctsInd δ c t - ctsInd δ y t| ≤ min 1 (|c - y| / (δ : ℝ)) := ctsInd_lipschitz hδ c y t
    _ ≤ |c - y| / (δ : ℝ) := min_le_right _ _
    _ ≤ η / (δ : ℝ) := div_le_div_of_nonneg_right h hδR.le

/-- **No false positives, product form:** `(x − t) · Ind_δ(x > t) ≥ 0` — the up-ramp is `0`
at or below the threshold and positive only strictly above it.
Source: vq-wiki-061 ("no false positives gives `W(⌜E_{f(n)}(X_n)v_n⌝ − p⌜v_n⌝) ≥ 0`");
`li-asymp-calc` `ctsInd_eq_zero_iff`, `ctsInd_pos_iff`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem sub_mul_ctsInd_nonneg {δ : ℚ} (hδ : 0 < δ) (x t : ℝ) :
    0 ≤ (x - t) * ctsInd δ x t := by
  rcases le_or_gt x t with hxt | hxt
  · rw [(ctsInd_eq_zero_iff hδ x t).2 hxt, mul_zero]
  · exact mul_nonneg (by linarith) (ctsInd_nonneg δ x t)

/-- **No false positives, down-ramp:** `(x − t) · Ind_δ(x < t) ≤ 0` — the down-ramp
`ctsInd δ t x` is `0` at or above the threshold and positive only strictly below it.
Source: vq-wiki-061 (the dual face); trust-lab-2-020 ("and the dual `≲` with `< t`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem sub_mul_ctsInd_nonpos {δ : ℚ} (hδ : 0 < δ) (x t : ℝ) :
    (x - t) * ctsInd δ t x ≤ 0 := by
  rcases le_or_gt t x with htx | htx
  · rw [(ctsInd_eq_zero_iff hδ t x).2 htx, mul_zero]
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (ctsInd_nonneg δ t x)

/-- The truncated error `min 1 (|c − y| / δ)` lies in `[0, 1]` (it is a LUV value).
Source: vq-wiki-063 (`e_n := min(1, |ā_n − Y_n|/δ)`); mandate target 6 traps
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem truncErr_mem_Icc {δ : ℚ} (hδ : 0 < δ) (c y : ℝ) :
    0 ≤ min 1 (|c - y| / (δ : ℝ)) ∧ min 1 (|c - y| / (δ : ℝ)) ≤ 1 := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  exact ⟨le_min zero_le_one (div_nonneg (abs_nonneg _) hδR.le), min_le_left _ _⟩

end Cleanroom.Deference.DefSelfTrust
