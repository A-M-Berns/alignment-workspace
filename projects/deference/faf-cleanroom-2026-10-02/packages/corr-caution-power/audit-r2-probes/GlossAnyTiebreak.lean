import Cleanroom.Corrigibility.CorrCautionPower.Witnesses

/-!
Audit r2 (adversarial) probe for `corr-caution-power` T3, the round-1 repair `gloss_refuted`.
The theorem quantilizes under the *natural* order on `Fin (n+4)` and proves it proxy-compatible.
D8 ranks by the proxy, and the proxy has ties (the two decoys at `3/10`; `∅` and the `n` further
actions at `13/20`), so other compatible tie-breaks exist. Check: under **every** linear order
compatible with the proxy, `a°` has nothing above it (it is the unique proxy maximum), so the
D8 slice at `q = 1/(Nη)` still puts mass exactly `η` on it — the refutation does not depend on
the tie-break. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrCautionPower.AuditR2

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect expect_const

/-- Under any proxy-compatible order, nothing is above `a° = last`. -/
theorem gloss_above_last_any_order (n : ℕ) (o : LinearOrder (Fin (n + 4)))
    (hU : @Compatible _ o (glossState n).proxy) :
    @above _ _ o (glossState n).γ (Fin.last (n + 3)) = 0 := by
  letI := o
  unfold above
  refine sum_eq_zero fun b hb => ?_
  simp only [mem_filter, mem_univ, true_and] at hb
  have h1 := hU _ _ hb
  -- `Fin (n+4)` has its own global order instances, which instance search reaches before the
  -- local `o` for the weaker classes; take irreflexivity from `o`'s own field instead.
  have hb_ne : b ≠ Fin.last (n + 3) := by
    intro h
    rw [h] at hb
    exact @lt_irrefl _ o.toPartialOrder.toPreorder _ hb
  rw [glossState_proxy, glossState_proxy, if_pos rfl, if_neg hb_ne] at h1
  split_ifs at h1 <;> norm_num at h1

/-- Under any proxy-compatible order, the D8 quantilizer of the gloss state puts mass `η` on `a°`
(same hypotheses as `gloss_refuted`). -/
theorem gloss_mass_any_order (n : ℕ) (o : LinearOrder (Fin (n + 4)))
    (hU : @Compatible _ o (glossState n).proxy) {η : ℝ} (hη1 : η ≤ 1)
    (hNη : 1 < ((n : ℝ) + 4) * η) :
    ∃ (hq : 0 < qRule η (glossState n).estBaseHarm)
      (hq1 : qRule η (glossState n).estBaseHarm ≤ 1),
      (@quantilize _ _ o (glossState n).γ (qRule η _) hq hq1).mass (Fin.last (n + 3)) = η := by
  letI := o
  obtain ⟨-, hRh⟩ := glossState_baseHarm n
  have hN : (0 : ℝ) < (n : ℝ) + 4 := by positivity
  have hη : 0 < η := by
    by_contra h; have h' := not_lt.mp h; nlinarith
  have hq : 0 < qRule η (glossState n).estBaseHarm := qRule_pos hη (by rw [hRh]; positivity)
  have hqval : qRule η (glossState n).estBaseHarm = (((n : ℝ) + 4) * η)⁻¹ := by
    have hle : ((n : ℝ) + 4)⁻¹ / η ≤ 1 := by
      rw [div_le_one hη, inv_le_iff_one_le_mul₀ hN]; nlinarith
    unfold qRule; rw [hRh, min_eq_right hle, div_eq_mul_inv, ← mul_inv]
  refine ⟨hq, qRule_le_one _ _, ?_⟩
  have hg : (glossState n).γ.mass (Fin.last (n + 3)) = ((n : ℝ) + 4)⁻¹ := by
    show (Distr.uniform : Distr (Fin (n + 4))).mass _ = _
    rw [uniform_mass_fin]; push_cast; ring
  rw [quantilize_mass, (glossState n).qmass_top hq (gloss_above_last_any_order n o hU), hg,
    hqval, min_eq_right]
  · field_simp
  · rw [inv_le_inv₀ hN (mul_pos hN hη)]
    exact mul_le_of_le_one_right hN.le hη1

end Cleanroom.Corrigibility.CorrCautionPower.AuditR2
