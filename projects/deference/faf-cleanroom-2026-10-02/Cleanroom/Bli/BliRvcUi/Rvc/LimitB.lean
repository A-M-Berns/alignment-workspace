import Cleanroom.Bli.BliRvcUi.Rvc.Antitone
import Cleanroom.Bli.BliRvcUi.Limit

/-!
# `bli-rvc-ui` · Rvc/LimitB: real-value coherence (B) holds for every logical inductor in the limit (T2.3)

**The claim.** For any `[IsLogicalInductor P DP]` with FAF's `hworld`, and any LUV that every
completed-theory world values, the limiting belief `limitingBelief P` is `RVC_B` on every
threshold set avoiding the boundary threshold `1`. Route: the antitone characterization —
`P∞ ∈ [0,1]` (Gaifman), antitone across thresholds because a completed world holding `X.gt r`
values `X` at or above `r` and so holds `X.gt r'` for `r' < r` (`limitingBelief_le_of_theory_imp`),
`1` below `0` and `0` above `1` (`limitingBelief_eq_one/zero_of_theory`).

**Why `1 ∉ R`.** FAF's `ValuesAt` decides `X.gt r` only for `r ≠ x`; a completed world valuing `X`
at exactly `1` may hold `X.gt 1`, so `P∞(X.gt 1)` is not forced to `0` — while `RVC_B` forces it
(point values lie in `[0,1]`). Findings F-12. Every other threshold is fine.

The `paperDP T` instance for `bli-found`'s quote LUVs is `Rvc/Paper.lean` (grade (a) by
`quoteLuv_valuesAt`).
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO.Propositional Finset

/-- **T2.3 — `RVC_B` of the limiting belief**, for any logical inductor and any LUV every
completed-theory world values, on thresholds avoiding `1`.
Source: mandate T2.3; [[bli-program]] M8 (limit form); [[bli-program-desiderata]] D-RVC(B)
Kind: C
Fidelity: exact (with `1 ∉ R`, see the module header)
Hyps: (a) `hval` is the LUV's own representation (discharged for quote LUVs by
`quoteLuv_valuesAt`, for FAF's `PaperLUV` by `source_valued`) -/
theorem rvcB_limit {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) {X : LUV}
    (hval : ∀ v : PCWorld, v.ConsistentWithTheory DP → ∃ x, v.ValuesAt X x)
    {R : Finset ℚ} (h1 : (1 : ℚ) ∉ R) : RVC_B (limitingBelief P) X R := by
  refine rvcB_iff_antitone.mpr ⟨fun r _ => limitingBelief_mem_Icc hworld _,
    fun r _ r' _ hlt => ?_, fun r _ hlt => ?_, fun r hr hle => ?_⟩
  · refine limitingBelief_le_of_theory_imp hworld fun v hv hgt => ?_
    obtain ⟨x, hx⟩ := hval v hv
    have hle : (r : ℝ) ≤ x := le_of_holds_gt_of_valuesAt hx hgt
    exact holds_gt_of_valuesAt hx (lt_of_lt_of_le (by exact_mod_cast hlt) hle)
  · refine limitingBelief_eq_one_of_theory hworld fun v hv => ?_
    obtain ⟨x, hx⟩ := hval v hv
    exact holds_gt_of_valuesAt hx (lt_of_lt_of_le (by exact_mod_cast hlt) hx.1)
  · refine limitingBelief_eq_zero_of_theory hworld fun v hv => ?_
    obtain ⟨x, hx⟩ := hval v hv
    have hne : r ≠ 1 := fun heq => h1 (heq ▸ hr)
    have hgt : (1 : ℚ) < r := lt_of_le_of_ne hle (Ne.symm hne)
    exact not_holds_gt_of_valuesAt hx (lt_of_le_of_lt hx.2.1 (by exact_mod_cast hgt))

end Cleanroom.Bli.BliRvcUi
