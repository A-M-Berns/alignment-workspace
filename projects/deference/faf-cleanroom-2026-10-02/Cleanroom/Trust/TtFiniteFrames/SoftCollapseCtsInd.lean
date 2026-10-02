import Cleanroom.Trust.TtFiniteFrames.SoftCollapse
import LogicalInduction.Properties.SelfTrust

/-!
# The soft collapse with FAF's continuous threshold indicator

Package `tt-finite-frames`, Target I2, instantiation. The ramp of record is FAF's
`LogicalInduction.ctsInd (δ : ℚ) (x y : ℝ) := min 1 (max 0 ((x − y)/δ))`
(`Ind_δ(x > y)`): `0` for `x ≤ y`, linear on `(y, y + δ]`, `1` beyond. This file is the package's
only FAF import and is kept to one theorem so that a slice kill costs one small file; the
abstract theorem is `SoftCollapse.lean`.

The soft conditional-martingale identity here is stated with `ctsInd δ (E_w X) t`, for all `X`,
all real thresholds `t` and all positive rational widths `δ` below the spectral gap of `X` — the
corpus's hypothesis with FAF's own ramp.
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- FAF's `ctsInd` vanishes at or below its threshold (re-proved here; FAF proves it in
`LogicalInduction.Construction.Quotation.DeferralFibre`, which this file does not import).
Source: FAF `ctsInd_eq_zero_of_le` (DeferralFibre.lean l. 186); none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ctsInd_eq_zero_of_le' (δ : ℚ) (x y : ℝ) (hδ : 0 < δ) (hxy : x ≤ y) :
    LogicalInduction.ctsInd δ x y = 0 := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold LogicalInduction.ctsInd
  have hratio : (x - y) / (δ : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hδR.le
  rw [max_eq_left hratio, min_eq_right zero_le_one]

/-- **I2 with FAF's ramp.** If the soft conditional-martingale identity
`∑ w, π w · X w · ctsInd δ (E_w X) t = ∑ w, π w · E_w X · ctsInd δ (E_w X) t` holds for every
`X`, every real threshold `t` and every positive rational width `δ` below the spectral gap of
`X`, then the expert is immodest at every world of positive prior probability.
Source: trust-lab-005; root-deference-011; [[deference-in-logical-induction-v6]] §2.2; FAF
`LogicalInduction.ctsInd` (`def:ctsind`)
Kind: C (the abstract theorem at FAF's ramp)
Fidelity: exact (FAF's `ctsInd` in place of the abstract ramp; rational widths as FAF's `δ : ℚ`)
Hyps: (a) `hsoft` only; no full support — conclusion on the support -/
theorem softCM_immodest_ctsInd {π : W → ℝ} {F : Frame W}
    (hsoft : ∀ (X : W → ℝ) (t : ℝ) (δ : ℚ), 0 < δ → (δ : ℝ) < Frame.gap F X →
      ∑ w, π w * X w * LogicalInduction.ctsInd δ (E (F.P w) X) t =
        ∑ w, π w * E (F.P w) X * LogicalInduction.ctsInd δ (E (F.P w) X) t) :
    ∀ w, 0 < π w → F.selfMass (F.P w) = 1 :=
  softCM_immodest_rat (ι := fun δ t x => LogicalInduction.ctsInd δ x t)
    (fun δ t x hδ hx => ctsInd_eq_zero_of_le' δ x t hδ hx)
    (fun δ t x hδ hx =>
      LogicalInduction.ctsInd_eq_one_of_le_sub δ x t hδ (by linarith))
    hsoft

end

end Cleanroom.Trust.TtFiniteFrames
