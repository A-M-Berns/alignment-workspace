import Cleanroom.Corrigibility.CorrLegitModif.Collapse
import Cleanroom.Lit.LitDdbAccuracyMm.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# corr-legit-modif — T3(a): the layer-cake bound `E_π[U R] ≥ ½ E_π[R²]`

[[approval-adversary]] A2.3: "TT gives `E_P[U | R ≥ t] ≥ t` for all `t`; integrating over `t`
yields `E_P[U R] ≥ ½ E_P[R²]`, not `E_P U ≥ E_P R`." Formalized by the integral route: the
above-threshold inequality of `TotalTrustOn U π F` says `g(t) := ∑ w, π w (U w − t) 𝟙[t ≤ R w]
≥ 0` for every `t`; for `R` valued in `[0, 1]`, `∫₀¹ g = ∑ w, π w ∫₀^{R w} (U w − t) dt
= ∑ w, π w (U w R w − R w²/2)`, so the sum is nonnegative. The range hypothesis is load-bearing
(off `[0, 1]` the integral does not see the whole threshold family); for an indicator `U` it is
automatic (`rating_ind_mem_Icc`). The finite route (sorting the attained values of `R`, telescoping
affine pieces) was not needed: Mathlib's `intervalIntegral.integral_indicator` does the one
non-trivial step.
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Lit.LitDdbAccuracyMm MeasureTheory
  intervalIntegral

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The rating of an indicator lies in `[0, 1]` (rows are distributions).
Source: none: infrastructure (the range hypothesis of `layer_cake_bound`, derived for indicators)
Kind: L
Fidelity: n/a -/
theorem rating_ind_mem_Icc (F : Frame W) (q : Finset W) (w : W) :
    0 ≤ rating F (ind q) w ∧ rating F (ind q) w ≤ 1 := by
  unfold rating
  rw [E_ind]
  exact ⟨mass_nonneg (F.P_mem w).1 q, mass_le_one (F.P_mem w) q⟩

/-- The threshold integrand of one world: `(U w − t) 𝟙[t ≤ R w]` is the indicator of `{t ≤ R w}`
applied to `t ↦ U w − t`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem threshold_eq_indicator (u r t : ℝ) :
    (u - t) * (if t ≤ r then 1 else 0) = Set.indicator {x | x ≤ r} (fun t => u - t) t := by
  rw [Set.indicator_apply]
  simp only [Set.mem_setOf_eq]
  split_ifs <;> ring

/-- `∫₀¹ (u − t) 𝟙[t ≤ r] dt = u r − r²/2` for `r ∈ [0, 1]`.
Source: none: infrastructure (the one-world integral)
Kind: L
Fidelity: n/a -/
theorem integral_threshold (u r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ∫ t in (0 : ℝ)..1, Set.indicator {x | x ≤ r} (fun t => u - t) t = u * r - r ^ 2 / 2 := by
  rw [integral_indicator hr]
  rw [integral_sub (continuous_const.intervalIntegrable _ _) (continuous_id'.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const, integral_id]
  simp; ring

/-- The one-world integrand is interval-integrable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem threshold_intervalIntegrable (c u r : ℝ) :
    IntervalIntegrable (fun t => c * Set.indicator {x | x ≤ r} (fun t => u - t) t) volume 0 1 := by
  apply IntervalIntegrable.const_mul
  rw [intervalIntegrable_iff]
  exact (intervalIntegrable_iff.1 ((continuous_const.sub continuous_id).intervalIntegrable 0 1)).indicator
    measurableSet_Iic

/-- **The layer-cake bound** (`layer_cake_bound`): for `π ≥ 0`, `U` with rating `R := R(U)` valued
in `[0, 1]`, Total Trust on the single variable `U` (the above-threshold family alone is used)
gives `0 ≤ ∑ w, π w (U w R w − R w²/2)`, i.e. `E_π[U R] ≥ ½ E_π[R²]`. Route: integrate the
threshold inequality over `t ∈ [0, 1]` (`integral_nonneg`, `integral_finsetSum`,
`integral_indicator`). The range hypothesis is needed and is automatic for indicator-valued `U`
(`rating_ind_mem_Icc`); witness `p2_layer_cake_numbers` (`31/100 ≥ 13/100`).
Source: [[approval-adversary]] A2.3 l. 29; corr-wf14-2-048
Kind: P
Fidelity: exact (`TotalTrustOn U`, weaker than `TotalTrust`; `R ∈ [0, 1]`; no sign condition on `π`)
Hyps: (a) `∀ w, R w ∈ [0, 1]`, `TotalTrustOn U π F` -/
theorem layer_cake_bound {π U : W → ℝ} {F : Frame W}
    (hR : ∀ w, 0 ≤ rating F U w ∧ rating F U w ≤ 1) (h : TotalTrustOn U π F) :
    0 ≤ ∑ w, π w * (U w * rating F U w - rating F U w ^ 2 / 2) := by
  have hg : ∀ t, 0 ≤ ∑ w, π w * Set.indicator {x | x ≤ rating F U w} (fun t => U w - t) t := by
    intro t
    have := h.1 t
    convert this using 2 with w
    rw [mul_assoc, threshold_eq_indicator]
    rfl
  have hI : 0 ≤ ∫ t in (0 : ℝ)..1,
      ∑ w, π w * Set.indicator {x | x ≤ rating F U w} (fun t => U w - t) t :=
    integral_nonneg zero_le_one (fun t _ => hg t)
  rw [integral_finsetSum (fun w _ => threshold_intervalIntegrable (π w) (U w) (rating F U w))] at hI
  have hcomp : ∀ w, ∫ t in (0 : ℝ)..1,
      π w * Set.indicator {x | x ≤ rating F U w} (fun t => U w - t) t =
        π w * (U w * rating F U w - rating F U w ^ 2 / 2) := by
    intro w
    rw [intervalIntegral.integral_const_mul, integral_threshold _ _ (hR w)]
  simp only [hcomp] at hI
  exact hI

/-- The layer-cake bound for an indicator: no range hypothesis.
Source: [[approval-adversary]] A2.3 l. 29
Kind: C
Fidelity: exact
Hyps: (a) `TotalTrustOn (ind q) π F` -/
theorem layer_cake_bound_ind {π : W → ℝ} {F : Frame W} (q : Finset W)
    (h : TotalTrustOn (ind q) π F) :
    0 ≤ ∑ w, π w * (ind q w * rating F (ind q) w - rating F (ind q) w ^ 2 / 2) :=
  layer_cake_bound (rating_ind_mem_Icc F q) h

end

end Cleanroom.Corrigibility.CorrLegitModif
