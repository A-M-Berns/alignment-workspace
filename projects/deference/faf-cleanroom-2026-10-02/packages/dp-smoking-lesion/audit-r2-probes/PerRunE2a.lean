import Cleanroom.Decision.DpSmokingLesion.Prop14E2a
import Cleanroom.Decision.DpCalibration.Bridge

/-!
# dp-smoking-lesion — audit round 2, adversarial lens: probe `PerRunE2a`

Not imported by the library. `prop14_e2a_screened_perRun` and `prop14_e2a_screened_perOcc`
are universals over states (`PerRunSSCAt s C e2a₀ () → ¬ S2 (s ())`), and the ledger's witness
column for them names mass values (`e2a_mass_occ_values`), not a state inhabiting the
hypothesis. This probe exhibits the per-run state on E2a for every procedure — the pushdown of
`dp-calibration`'s lifted state, which satisfies the per-run clauses by
`pushdown_liftState_agree_iff_perRun` — and checks that at `C(d) = ½` it has both act
probabilities equal to `½ > 0`, so the package's `¬ S2` there is by the flatness clause and not
by (S2)'s positivity guards: the screening universals are inhabited non-degenerately (N+).
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

/-- The per-run state on E2a for `C`: the pushdown of the lifted state at `occ(d)`. -/
noncomputable def e2aPerRunState (C : Proc Unit (fun _ => Bool) ℚ) : Unit → State TickleW ℚ :=
  fun _ => pushdown e2a₀ (liftState C e2a₀ ())

/-- `μ(occ(d)) = 1/10 > 0` on E2a. -/
theorem e2a_mass_occ_pos (C : Proc Unit (fun _ => Bool) ℚ) : 0 < mass C e2a₀ (occ () e2a₀) := by
  rw [e2a_mass_occ_univ]; norm_num

/-- The per-run clauses hold for the per-run state, for every `C`. -/
theorem e2aPerRunState_perRunClauses (C : Proc Unit (fun _ => Bool) ℚ) :
    PerRunClausesAt (e2aPerRunState C) C e2a₀ () :=
  (pushdown_liftState_agree_iff_perRun C e2a₀ (e2aPerRunState C) (e2a_mass_occ_pos C)).mp
    ⟨rfl, fun _ _ => rfl⟩

/-- Hence the hypothesis of `prop14_e2a_screened_perRun` is inhabited for every `C`. -/
theorem e2aPerRunState_perRunSSC (C : Proc Unit (fun _ => Bool) ℚ) :
    PerRunSSCAt (e2aPerRunState C) C e2a₀ () :=
  fun _ => e2aPerRunState_perRunClauses C

/-- The per-run state's act probabilities are the label: `P(m=1) = C(d)(smoke)`,
`P(m=0) = 1 − C(d)(smoke)` (the reference class is conditioned away). -/
theorem e2aPerRunState_pr (C : Proc Unit (fun _ => Bool) ℚ) :
    (e2aPerRunState C ()).pr (evM true) = (C ()).w true ∧
    (e2aPerRunState C ()).pr (evM false) = 1 - (C ()).w true := by
  have h1 := (e2aPerRunState_perRunClauses C).1
  have hocc := e2a_mass_occ_univ C
  obtain ⟨hv1, -, hv3, -⟩ := e2a_mass_occ_values C
  have a := h1 (evM true)
  rw [hocc, hv1] at a
  have b := h1 (evM false)
  rw [hocc, hv3] at b
  constructor <;> linarith

/-- **N+ for the screening**: at `C(d) = ½` the per-run state has `P(m=1) = P(m=0) = ½ > 0`
and violates (S2) — the violation is the equality of the cross-products, not a positivity
failure. -/
theorem e2aPerRunState_half :
    (e2aPerRunState e2aHalf ()).pr (evM true) = 1/2 ∧
    (e2aPerRunState e2aHalf ()).pr (evM false) = 1/2 ∧
    ¬ S2 (e2aPerRunState e2aHalf ()) := by
  obtain ⟨h1, h2⟩ := e2aPerRunState_pr e2aHalf
  refine ⟨?_, ?_, prop14_e2a_screened_perRun e2aHalf _ (e2aPerRunState_perRunSSC e2aHalf)⟩
  · rw [h1]; simp [e2aHalf, procBool]
  · rw [h2]; simp [e2aHalf, procBool]; norm_num

end Cleanroom.Decision.DpSmokingLesion
