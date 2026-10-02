import Cleanroom.Corrigibility.CorrLegitModif.Y1Legit

/-!
# Audit probe (corr-legit-modif, round 2, adversarial): the `L`-conditioned label is earned by
every `L`-conditioned refinement, at every `λ`

`y1FrameL_legitimizingTT` proves `LegitimizingTT (y1 λ) (y1FrameL λ) Lset` for the three-cell
frame `refineFrame (restrict (y1 λ) Lset) f3`. The proof is `refineFrame_totalTrust`, and nothing
in it uses `f3`: every Bayesian refinement of the `L`-restricted prior along *any* map earns the
label at every `λ ∈ [0, 1]` — the round-1 probe's `any_refinement_is_legit` was the `λ = 1` case.
So the global `L`-conditioned label does not distinguish between `L`-conditioned successors
(three cells, two cells, one cell, sixteen cells); what it rules out at `λ < 1` is only a row that
is not certain of `L` (`legitimizingTT_certain_of_legit`, the mechanism of
`y1Frame_not_legitimizingTT`). Not a defect of the Lean — it is DDB Theorem 4.1's hull condition
on a partition frame — but it is the content behind F2's "which successor frame": lgf l. 170's
literal `P_{t₁}(· | σ, L)` with `σ` the verdict (two cells) passes exactly as the mandate's
three-cell frame does (`verdict_only_L_frame_is_legit`).
-/

namespace AuditProbe

open Cleanroom.Corrigibility.CorrLegitModif Cleanroom.Found.LitDdbFrames
  Cleanroom.Corrigibility.CorrReflectFrames

theorem any_L_refinement_is_legit {S : Type} [DecidableEq S] (f : Y1W → S) (lam : ℝ)
    (hl : 0 ≤ lam ∧ lam ≤ 1) :
    LegitimizingTT (y1 lam)
      (refineFrame (restrict (y1 lam) Lset) (restrict_nonneg (y1Pol_nonneg hl false) Lset) f)
      Lset := by
  unfold LegitimizingTT
  exact refineFrame_totalTrust _ f

/-- The two-cell frame along the verdict alone (keep rows `π(· | L ∩ keep)`, ignoring `σ_A`) —
the literal reading of lgf l. 170's `P_{t₁}(· | σ, L)` — passes the label at every `λ` too. -/
theorem verdict_only_L_frame_is_legit (lam : ℝ) (hl : 0 ≤ lam ∧ lam ≤ 1) :
    LegitimizingTT (y1 lam)
      (refineFrame (restrict (y1 lam) Lset) (restrict_nonneg (y1Pol_nonneg hl false) Lset)
        (fun w => w.2.2.2))
      Lset :=
  any_L_refinement_is_legit _ lam hl

end AuditProbe
