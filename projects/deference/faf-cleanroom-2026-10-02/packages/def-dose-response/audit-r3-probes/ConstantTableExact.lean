import Cleanroom.Deference.DefDoseResponse.Advisor

/-!
# Audit r3 (fidelity) probe — the "mesh rounding" of F6 is the package's table, not the mesh

F6 says the day-`n` expectation "is the `1/(n+1)` mesh" and that for the committed stream to
carry `a_n(u) = v` on every steering day `v` must be mesh-exact. But FAF's `def:e` mesh is in the
*thresholds* `i/(n+1)`, not in the attainable values: `𝔼_n(X) = (n+1)⁻¹ ∑_{i≤n} P_n(X > i/(n+1))`
is `v` whenever every threshold sentence is priced at `v`. Lemma 4.3's finite-support reading
(`prescribe_finiteSupport`) accepts any `[0,1]`-valued table, so the steered advisor built from
the **constant-`v` table** at the same coordinates (`steeredSet N`) is an inductor exactly and
quotes exactly `v` on every day `< N`, for every rational `v ∈ [0,1]` — `v = ½` on day `2`
included, where the package's indicator table gives `2/3` (`steeredAdvisor_half_day_two`). The
rounding F6 reports is a property of `steeredTable`'s `0/1` prescription, not of the design.

Not imported by the library. Elaborate with `scripts/lean-check`.
-/

namespace Cleanroom.Deference.DefDoseResponse.AuditR3

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Li.LiProjection
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Deference.DefDoseResponse

/-- The constant-`v` table. -/
noncomputable def constTable (v : ℚ) : ℕ → Sentence → ℚ := fun _ _ => v

/-- The steered advisor with every mesh threshold of the `u`-column on days `< N` priced at `v`. -/
noncomputable def steeredAdvisorConst (A : History) (v : ℚ) (N : ℕ) : History :=
  patch A (steeredSet N) (constTable v)

/-- It is an inductor exactly, for every `v ∈ [0,1]` (`prescribe_finiteSupport`). -/
theorem steeredAdvisorConst_isLogicalInductor (A : History) (DP : DeductiveProcess)
    [IsLogicalInductor A DP] {v : ℚ} (hv : 0 ≤ v ∧ v ≤ 1) (N : ℕ) :
    IsLogicalInductor (steeredAdvisorConst A v N) DP :=
  prescribe_finiteSupport A DP (steeredSet N) (constTable v) (fun _ _ => hv)

/-- Its quote on every steering day is exactly `v` — no mesh condition. -/
theorem steeredAdvisorConst_quote (A : History) (v : ℚ) {N n : ℕ} (hn : n < N) :
    quoteStreamR (steeredAdvisorConst A v N) n = (v : ℝ) := by
  unfold quoteStreamR
  simp only [LUV.expect, LUV.expectApprox]
  have hmem : ∀ i ∈ Finset.range (n + 1),
      steeredAdvisorConst A v N n ((quoteLuv n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))) = (v : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hcast : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
    rw [hcast]
    unfold steeredAdvisorConst
    rw [patch_mem _ _ _ (by
      unfold steeredSet
      rw [Finset.mem_biUnion]
      exact ⟨n, Finset.mem_range.mpr hn, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩⟩)]
    rfl
  rw [Finset.sum_congr rfl hmem, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hpos : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [inv_mul_cancel_left₀ hpos]

/-- The contrast with `steeredAdvisor_half_day_two` (`2/3`): the constant table hits `½` on day `2`. -/
theorem steeredAdvisorConst_half_day_two (A : History) :
    quoteStreamR (steeredAdvisorConst A (1 / 2) 3) 2 = 1 / 2 := by
  rw [steeredAdvisorConst_quote A (1 / 2) (by norm_num : 2 < 3)]
  norm_num

end Cleanroom.Deference.DefDoseResponse.AuditR3
