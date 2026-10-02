import Cleanroom.Corrigibility.CorrLegitModif.Plumbing

/-!
# corr-legit-modif — T12: reach equals the anticipated set; the accuracy reversal

[[channel-final]] S1 l. 65: under function-form endorsement "a datum 'believe `ρ`' lands on `ρ`
iff `ρ` is anticipated; for an unanticipated target `P_t(E_ρ) = 0` and there is no conditional to
land on". Over DDB frames: `Reflects π F` says exactly that for every anticipated row `ρ`
(`0 < π(P = ρ)`) conditioning on `E_ρ = [P = ρ]` lands on `ρ` — `restrict π (cell ρ) = π(cell ρ) • ρ`
(`lands_iff_anticipated`); for a row nobody anticipates the restriction is the zero deferrer
(`restrict_cell_eq_zero_of_not_cand`): the junk value made explicit, there is no conditional. The
barycentre `∑_{ρ ∈ C_π} π(cell ρ) • ρ = π` under Reflection is `barycentre_of_reflects` (the
`corr-general-object` form is `Endorse.barycentre_of_reflectiveFor`, cited). An external write to a
row outside `C_π` is not an event of the frame — recorded; the "credulous BLI" worry is Reflection
with every row anticipated. ATTRIBUTION-UNVETTED as to Eisenstat (channel-final Q5).

The accuracy reversal (bli-soto-b-061) is `corr-general-object`'s `Faking.brier_faked_le_honest`
and `Faking.humans_side`, cited (a) and not restated.
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **`lands_iff_anticipated`**: Reflection is "conditioning on `E_ρ` lands on `ρ` for every
anticipated `ρ`": `restrict π (cell ρ) = π(cell ρ) • ρ` for every candidate.
Source: [[channel-final]] S1 l. 65; bli-soto-b-060
Kind: L
Fidelity: exact (Reflection's product form read as an identity of deferrers)
Hyps: (a) none -/
theorem lands_iff_anticipated (π : W → ℝ) (F : Frame W) :
    Reflects π F ↔ ∀ ρ ∈ F.cands π, restrict π (F.cell ρ) = mass π (F.cell ρ) • ρ := by
  unfold Reflects
  apply forall_congr'; intro ρ; apply imp_congr_right; intro _
  rw [funext_iff]
  apply forall_congr'; intro w
  simp only [Pi.smul_apply, smul_eq_mul]
  exact Iff.rfl

/-- **An unanticipated row has no conditional to land on**: for `ρ ∉ C_π` the restriction of
`π` to `[P = ρ]` is the zero deferrer.
Source: [[channel-final]] S1 l. 65 ("for an unanticipated target `P_t(E_ρ) = 0` and there is no
conditional to land on")
Kind: L
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` -/
theorem restrict_cell_eq_zero_of_not_cand {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    {ρ : W → ℝ} (h : ρ ∉ F.cands π) : restrict π (F.cell ρ) = 0 := by
  funext w
  rw [restrict_apply]
  split_ifs with hw
  · rw [Frame.mem_cell] at hw
    rcases (hπ w).lt_or_eq with hpos | hzero
    · exact absurd (hw ▸ F.P_mem_cands hpos) h
    · exact hzero.symm
  · rfl

/-- The candidates' cells cover the support: `∑_{ρ ∈ C_π} 𝟙[P_w = ρ] = 1` at every positive world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_ind_cells_eq_one {π : W → ℝ} {F : Frame W} {w : W} (hw : 0 < π w) :
    ∑ ρ ∈ F.cands π, ind (F.cell ρ) w = 1 := by
  simp only [ind_cell_apply]
  rw [sum_ite_eq, if_pos (F.P_mem_cands hw)]

/-- **The barycentre identity**: under Reflection `∑_{ρ ∈ C_π} π(cell ρ) • ρ = π` — the deferrer is
the mixture of its anticipated rows with the cell masses as weights (the `corr-general-object`
form is `Endorse.barycentre_of_reflectiveFor`).
Source: [[channel-final]] S1 l. 65 ("`∑_ρ P_t(E_ρ) ρ = P_t`"); bli-soto-b-060
Kind: L
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, `Reflects π F` -/
theorem barycentre_of_reflects {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : Reflects π F) : ∑ ρ ∈ F.cands π, mass π (F.cell ρ) • ρ = π := by
  rw [lands_iff_anticipated] at h
  funext w
  rw [Finset.sum_apply]
  have e : ∀ ρ ∈ F.cands π, (mass π (F.cell ρ) • ρ) w = π w * ind (F.cell ρ) w := by
    intro ρ hρ; rw [← h ρ hρ]; rfl
  rw [sum_congr rfl e, ← mul_sum]
  rcases (hπ w).lt_or_eq with hw | hw
  · rw [sum_ind_cells_eq_one hw, mul_one]
  · rw [← hw]; ring

end

end Cleanroom.Corrigibility.CorrLegitModif
