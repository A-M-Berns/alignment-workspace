import Cleanroom.Corrigibility.CorrCautionPower.CautionRule

/-!
Audit r2 (adversarial) probe for `corr-caution-power` load-bearing 4, the repaired S5(b) harm
bound `realizedHarm_le_known_cost` (`H ≤ k + 2δ + max{η, R̂}`). Degenerate model: a posterior
that is a point mass on the target (`P = δ_{ω*}`, the dogmatic-and-right agent). Then the proxy is
the truth, every action is `0`-covered, the corrected predicate holds at `δ = 0`, and the
"knowingly accepted cost" `k` is the *entire* realized harm — so the theorem reads
`H ≤ H + 0 + max{η, R̂}`. This is not a defect of the theorem (it is the source's own bound): it
locates the bound's content in the uncovered mass and the `2δ` slack, and it makes F-18's point
concrete — `k` absorbs whatever harm coverage makes visible, and coverage is not the agent's to
see. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrCautionPower.AuditR2

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect expect_const

variable {A Ω : Type*} [Fintype A] [Fintype Ω] [DecidableEq Ω] (S : CautionState A Ω)

/-- At a point-mass posterior on the target the proxy is the truth. -/
lemma proxy_eq_V_of_delta (h : S.P = Distr.delta S.target) (a : A) :
    S.proxy a = S.V S.target a := by
  unfold CautionState.proxy; rw [h, expect_delta]

/-- Every action is `0`-covered, so the corrected predicate holds at `δ = 0`. -/
theorem nullCovered_zero_of_delta (h : S.P = Distr.delta S.target) :
    S.NullCoveredKnownUncovered 0 := by
  have hc : ∀ a, S.Covered 0 a := fun a => by
    unfold CautionState.Covered CautionState.err
    rw [proxy_eq_V_of_delta S h, sub_self, abs_zero]
  exact ⟨hc _, fun a _ => Or.inl (hc a)⟩

/-- The knowingly accepted cost `k` (at `δ = 0`) is the whole realized harm. -/
theorem known_cost_eq_realizedHarm (h : S.P = Distr.delta S.target) (π : Distr A) :
    (∑ a ∈ S.coveredSet 0, π.mass a * S.proxyHarm a) = S.realizedHarm π := by
  have hcov : S.coveredSet 0 = univ := by
    ext a
    simp only [CautionState.mem_coveredSet, mem_univ, iff_true]
    unfold CautionState.Covered CautionState.err
    rw [proxy_eq_V_of_delta S h, sub_self, abs_zero]
  have hph : ∀ a, S.proxyHarm a = S.trueHarm a := fun a => by
    unfold CautionState.proxyHarm CautionState.trueHarm CautionState.harm harmOf
    rw [proxy_eq_V_of_delta S h, proxy_eq_V_of_delta S h]
  rw [hcov]
  unfold CautionState.realizedHarm expect
  exact sum_congr rfl fun a _ => by rw [hph]

/-- So on the dogmatic-and-right agent the repaired harm bound is `H ≤ H + 2·0 + max{η, R̂}`. -/
theorem known_cost_bound_at_delta [LinearOrder A] (h : S.P = Distr.delta S.target) {η q : ℝ}
    (hη : 0 < η)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hq : min 1 (S.estBaseHarm / η) ≤ q) :
    S.realizedHarm (quantilize S.γ q hq0 hq1)
      ≤ S.realizedHarm (quantilize S.γ q hq0 hq1) + 2 * 0 + max η S.estBaseHarm := by
  have := S.realizedHarm_le_known_cost (nullCovered_zero_of_delta S h) hη hq0 hq1 hq
  rwa [known_cost_eq_realizedHarm S h] at this

end Cleanroom.Corrigibility.CorrCautionPower.AuditR2
