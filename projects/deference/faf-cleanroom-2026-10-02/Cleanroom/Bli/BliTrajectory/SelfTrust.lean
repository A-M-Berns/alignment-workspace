import Cleanroom.Bli.BliTrajectory.Defs
import LogicalInduction.Properties.SelfTrust

/-!
# `bli-trajectory` · SelfTrust: interval faith gives δ-smoothed self-trust in sum form (M10, T6)

bli-slides-042's `Ind_δ` is FAF's `ctsInd δ x y = min 1 (max 0 ((x − y)/δ))`. Over the state
partition, `E2i ε` gives the smoothed self-trust inequality
`∑_q 𝐏_n(φ ⋏ σ_q) · Ind_δ(Q̂_q[φ] > p) ≥ (p − ε_m) · ∑_q 𝐏_n(σ_q) · Ind_δ(Q̂_q[φ] > p)`
(`e2i_smoothed_self_trust`), exact (`ε = 0`) under `E2x` (`e2x_smoothed_self_trust`). Contrast
row, no theorem: FAF's `lic_self_trust` is asymptotic over e.c. sequences; exact-from-day-one
enforcement is `bli-exactness` X6's (bli-soto-b-027).
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

open Classical

/-- `ctsInd` is nonnegative.
Source: FAF `ctsInd_mem_Icc`
Kind: L
Fidelity: n/a -/
lemma ctsInd_nonneg (δ : ℚ) (x y : ℝ) : 0 ≤ ctsInd δ x y := (ctsInd_mem_Icc δ x y).1

/-- Where the smoothed indicator is positive, the threshold is exceeded (`0 < δ`).
Source: FAF `def:ctsind` (bli-slides-042's `Ind_δ`)
Kind: L
Fidelity: n/a -/
lemma lt_of_ctsInd_pos {δ : ℚ} (hδ : 0 < δ) {x y : ℝ} (h : 0 < ctsInd δ x y) : y < x := by
  unfold ctsInd at h
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  by_contra hxy
  push_neg at hxy
  have : (x - y) / (δ : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ'.le
  have h2 : max 0 ((x - y) / (δ : ℝ)) = 0 := max_eq_left this
  rw [h2, min_eq_right zero_le_one] at h
  exact lt_irrefl _ h

/-- `x · Ind_δ(x > p) ≥ p · Ind_δ(x > p)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mul_ctsInd_ge {δ : ℚ} (hδ : 0 < δ) (x p : ℝ) : p * ctsInd δ x p ≤ x * ctsInd δ x p := by
  rcases (ctsInd_nonneg δ x p).lt_or_eq with h | h
  · exact mul_le_mul_of_nonneg_right (lt_of_ctsInd_pos hδ h).le h.le
  · rw [← h]; simp

/-- **`e2i_smoothed_self_trust` — interval faith gives δ-smoothed self-trust in sum form over
the state partition**: from `E2i ε S P`, for `n < m`, `φ ∈ Sminus m m`, `0 < δ` and any
threshold `p`, `∑_q P_n(φ ⋏ σ_q) Ind_δ(Q̂_q[φ] > p) ≥ p · ∑_q P_n(σ_q) Ind_δ(…) − ε_m · ∑_q P_n(σ_q) Ind_δ(…)`.
Termwise: constraint 2 up to `ε_m P_n(σ_q)`, then `Q̂_q[φ] · Ind ≥ p · Ind`.
Source: bli-slides-042 (`Ind_δ`); mandate M10
Kind: C
Fidelity: variant: state-partition sums in place of the LUV expectation `𝔼_n`, and the state's
table value `Q̂_q[φ]` in place of the LUV `P_m(φ)` (bli-slides-042's inequality is over LUV
expectations; the (c)-flavoured identification is the one disclosed for `marginalMass`), with
`bli-found`'s `E2i` and FAF's `ctsInd`
Hyps: (a) `E2i ε S P`; (a) `0 ≤ P_n(σ_q)` (explicit) -/
theorem e2i_smoothed_self_trust {ε : ℕ → ℝ} {S : StateSystem} {P : History} (h : E2i ε S P)
    {δ : ℚ} (hδ : 0 < δ) {n m : ℕ} (hnm : n < m) {φ : Sentence} (hφ : φ ∈ Sminus m m) (p : ℝ)
    (hP : ∀ q ∈ S.states m, 0 ≤ P n (stateAtom m q)) :
    p * ∑ q ∈ S.states m, P n (stateAtom m q) * ctsInd δ (S.val m q φ) p -
        ε m * ∑ q ∈ S.states m, P n (stateAtom m q) * ctsInd δ (S.val m q φ) p ≤
      ∑ q ∈ S.states m, P n (φ ⋏ stateAtom m q) * ctsInd δ (S.val m q φ) p := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun q hq => ?_
  have h1 := h n m hnm q hq φ hφ
  obtain ⟨hl, -⟩ := abs_le.mp h1
  have hI := ctsInd_nonneg δ (S.val m q φ) p
  have hv := mul_ctsInd_ge hδ (S.val m q φ) p
  have hPq := hP q hq
  -- P n (φ ⋏ σ) ≥ (val − ε) P n σ, times Ind ≥ 0
  have key : (S.val m q φ * P n (stateAtom m q) - ε m * P n (stateAtom m q)) *
      ctsInd δ (S.val m q φ) p ≤ P n (φ ⋏ stateAtom m q) * ctsInd δ (S.val m q φ) p :=
    mul_le_mul_of_nonneg_right (by linarith) hI
  nlinarith [key, hv, hPq, hI, mul_nonneg hPq hI]

/-- **Exact smoothed self-trust under `E2x`** (`ε = 0`).
Source: bli-slides-042; mandate M10
Kind: C
Fidelity: exact
Hyps: (a) `E2x S P`; (a) nonnegative superbeliefs (explicit) -/
theorem e2x_smoothed_self_trust {S : StateSystem} {P : History} (h : E2x S P) {δ : ℚ} (hδ : 0 < δ)
    {n m : ℕ} (hnm : n < m) {φ : Sentence} (hφ : φ ∈ Sminus m m) (p : ℝ)
    (hP : ∀ q ∈ S.states m, 0 ≤ P n (stateAtom m q)) :
    p * ∑ q ∈ S.states m, P n (stateAtom m q) * ctsInd δ (S.val m q φ) p ≤
      ∑ q ∈ S.states m, P n (φ ⋏ stateAtom m q) * ctsInd δ (S.val m q φ) p := by
  have h' : E2i (fun _ => 0) S P := by
    intro n m hnm q hq φ hφ
    rw [h n m hnm q hq φ hφ, sub_self, abs_zero, zero_mul]
  have := e2i_smoothed_self_trust h' hδ hnm hφ p hP
  simpa using this

end Cleanroom.Bli.BliTrajectory
