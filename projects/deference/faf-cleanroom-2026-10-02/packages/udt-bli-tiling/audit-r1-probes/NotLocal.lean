import Cleanroom.Bli.UdtBliTiling.Refreeze

/-!
# Audit r1 (adversarial) probe · NotLocal: `LocalUtility` fails on the single-coin model

The report and `SingleCoin.lean`'s docstring say "`LocalUtility` fails here (cross-round terms)"
without a Lean declaration. This probe proves `¬ (scPrior p).LocalUtility` for every `K ≥ 1`
under the natural positivity (`q < 1`, `w j > 0`, `V ≠ 0`, `γ j ≠ 0`): the branch `Rec_j` reads
the `Ask_j` point (the mugging's own cross-branch term, core F-13), so two policies agreeing at
`Rec_j` and differing at `Ask_j` have different cell values there. So the model is outside T1's
package for the same reason the mugging is — the cross-*branch* term, before any cross-*round*
term enters — which sharpens the report's parenthetical. Not imported by the library.
-/

namespace Cleanroom.Bli.UdtBliTiling.AuditR1

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist Finset
open Cleanroom.Bli.UdtBliSist.Iter SingleCoin

variable {K : ℕ} (p : Params K)

lemma baseState_eq_recT_iff (j : Fin K) (ω₀ : Base K) :
    baseState ω₀ = recT K j ↔ ω₀ = (false, j) := by
  constructor
  · intro h
    have := st_injective K h
    simpa using this
  · rintro rfl; rfl

lemma massOf_state_rec (j : Fin K) :
    massOf (baseMass p) (fun ω₀ : Base K => baseState ω₀ = recT K j) = baseMass p (false, j) := by
  unfold massOf
  simp only [baseState_eq_recT_iff]
  rw [Finset.sum_ite_eq']
  simp

/-- The cell value at `Rec_j` is the utility of the coin-false world: `V · roundSum π + r₀ false`. -/
lemma cellEU_rec (j : Fin K) (π : Policy (iterTables K) Bool) (hpos : 0 < baseMass p (false, j)) :
    (scPrior p).cellEU (recT K j) π = p.V * roundSum p.γ π + p.r₀ false := by
  unfold scPrior FiniteBLIPrior.cellEU condExp
  change (scData p).toPrior.cellUtil _ π / (scData p).toPrior.cellMass _ π = _
  rw [(scData p).cellUtil_toPrior, (scData p).cellMass_toPrior]
  change (∑ ω₀ : Base K, if baseState ω₀ = recT K j then
      baseMass p ω₀ * ((scData p).ν π * scU p ω₀ π) else 0) /
    (massOf (baseMass p) (fun ω₀ : Base K => baseState ω₀ = recT K j) * (scData p).ν π) = _
  rw [massOf_state_rec]
  simp only [baseState_eq_recT_iff]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [mul_div_mul_left _ _ (ne_of_gt hpos), mul_div_cancel_left₀ _ (ne_of_gt (ν_pos p π))]
  simp [scU, payoff]

/-- **`LocalUtility` fails on the single-coin model** at `Rec_j`, for every `K ≥ 1`: `payAll` and
`payAll[Ask_j ↦ refuse]` agree at `Rec_j`, both cells are positive, and the values differ by
`V · γ_j`. -/
theorem not_localUtility (j : Fin K) (hw : 0 < p.w j) (hq : p.q < 1) (hV : p.V ≠ 0)
    (hγ : p.γ j ≠ 0) : ¬ (scPrior p).LocalUtility := by
  intro h
  have hpos : 0 < baseMass p (false, j) := by
    unfold baseMass
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact mul_pos (by linarith) hw
  have hcm : ∀ π : Policy (iterTables K) Bool, 0 < (scPrior p).cellMass (recT K j) π := by
    intro π
    unfold scPrior
    rw [(scData p).cellMass_toPrior]
    change 0 < massOf (baseMass p) (fun ω₀ : Base K => baseState ω₀ = recT K j) * (scData p).ν π
    rw [massOf_state_rec]
    exact mul_pos hpos (ν_pos p π)
  have hagree : payAll (recT K j) = Function.update payAll (askT K j) false (recT K j) := by
    rw [Function.update_of_ne (askT_ne_recT j j).symm]
  have hval := h (recT K j) payAll (Function.update payAll (askT K j) false) hagree (hcm _) (hcm _)
  rw [cellEU_rec p j _ hpos, cellEU_rec p j _ hpos, roundSum_update] at hval
  simp only [payAll, ind_true, ind_false] at hval
  have : p.V * p.γ j = 0 := by linarith
  exact mul_ne_zero hV hγ this

end Cleanroom.Bli.UdtBliTiling.AuditR1
