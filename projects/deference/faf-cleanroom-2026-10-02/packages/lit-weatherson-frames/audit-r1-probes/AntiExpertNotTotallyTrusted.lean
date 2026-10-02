import Cleanroom.Lit.LitWeathersonFrames.CFrame

/-!
Audit round 1, adversarial lens — probe: the conclusions `TotalTrustC` and `ValueBdd` have
content (they are not automatically true of every `CFrame`).

`CFrame` is over any carrier, so a two-world anti-expert frame (at `w` the expert is certain of
`!w`) with the uniform prior is a frame in the package's sense. It is **not** totally trusted:
with `X = 𝟙[true]` and `t = 1` the threshold event is `{false}` and the product-form sum is
`½ · (0 − 1) < 0`. By the contrapositive of `value_imp_totalTrust` it is not Valued either. So the
conclusion of T4, and the Total Trust conclusions of T8 (ray frames) and T10 (Bentham), are
genuine. Not imported by the library.
-/

namespace Cleanroom.Lit.LitWeathersonFrames.AuditR1Adv

open Cleanroom.Lit.LitWeathersonFrames

noncomputable section

/-- The anti-expert rows on `Bool`: at `w`, the expert is certain of `!w`. -/
def antiP (w v : Bool) : ℝ := if v = !w then 1 else 0

theorem antiP_sum (w : Bool) : ∑ v, antiP w v = 1 := by
  cases w <;> simp [antiP]

/-- The anti-expert frame. -/
def antiFrame : CFrame Bool where
  P := antiP
  P_nonneg := fun w v => by unfold antiP; split_ifs <;> norm_num
  P_hasSum := fun w => by
    have h := hasSum_fintype (antiP w)
    rwa [antiP_sum] at h

/-- The uniform prior on `Bool`. -/
def halfπ : Bool → ℝ := fun _ => 1/2

theorem halfπ_isDist : IsDist halfπ := by
  refine ⟨fun _ => by norm_num [halfπ], ?_⟩
  have h := hasSum_fintype halfπ
  have hs : ∑ b, halfπ b = 1 := by norm_num [halfπ]
  rwa [hs] at h

/-- The uniform prior does not totally trust the anti-expert frame. -/
theorem antiFrame_not_totalTrustC : ¬ TotalTrustC halfπ antiFrame := by
  intro h
  have := h (fun w => if w then 1 else 0) ⟨1, fun w => by cases w <;> norm_num⟩ 1
  norm_num [antiFrame, Eℕ, tsum_fintype, Fintype.sum_bool, antiP, halfπ] at this

/-- Hence it does not Value it either (contrapositive of T4, `value_imp_totalTrust`). -/
theorem antiFrame_not_valueBdd : ¬ ValueBdd halfπ antiFrame :=
  fun hV => antiFrame_not_totalTrustC (value_imp_totalTrust halfπ_isDist hV)

end

end Cleanroom.Lit.LitWeathersonFrames.AuditR1Adv
