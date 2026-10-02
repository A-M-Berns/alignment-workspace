import Cleanroom.Decision.DpEdtUdtFair.LimitState
import Cleanroom.Decision.DpCalibration.Corollaries

/-!
# `dp-edt-udt-fair` · audit round 2 (adversarial) · probe P2: D1's approval of `(a, y)` is not a feature of the null point

Evidence file for `dp-edt-udt-fair-audit-r2-adversarial.md`. **Not imported by the library.**

The D1 clauses of T7(i) and T8 (`outY_limitStateEdt`, `threat_outY_limitState`) prove that
limit-state EDT approves the dominated profile `(a, y)` on the threat tree "by the `A_d^+`
collapse at the pinned null-observation state" (critique C9). This probe checks that the
approval has nothing to do with the null point: D1 also approves the *worst* deterministic
profile `(in, y)` (`profHH = proc2 0 0`, `V = 0 < 2`), at which **both** observations are
realized (`ν(O₁) = ν(O₂) = 1`), with the limit states pinned to the strictly calibrated ones
(`δ_{inY}` at both points): the unplayed act has probability `0` in the pinned state, so
`A_d^+ = supp C(d)` and `T_EDT` holds for free. This is `calibration.md` CA-17′ ("D1 is
content-free where it matters: at recorded on-path points the Definition-10 state has
`A_d^+ = supp C(d)`"), which lies inside the mandate's cited window (l. 72–90) but is cited by
none of the package's D1 rows.
-/

namespace Cleanroom.Decision.DpEdtUdtFair.AuditR2

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

/-- Under `(in, y)` on the threat tree, `ν(X) = [inY ∈ X]`. -/
theorem profHH_nu_threat (X : Finset TwoW) :
    nu profHH threat X = if TwoW.inY ∈ X then 1 else 0 := by
  show nu (proc2 0 0 _ _ _ _) (twoPoint 1 2 0) X = _
  rw [twoPoint_nu]
  split_ifs <;> simp

/-- Under `(in, y)` on the threat tree, `𝔼[r 1_X] = 0` (the played leaf pays `0`). -/
theorem profHH_paySum_threat (X : Finset TwoW) : paySum profHH threat X = 0 := by
  show paySum (proc2 0 0 _ _ _ _) (twoPoint 1 2 0) X = _
  rw [twoPoint_paySum]
  split_ifs <;> simp

/-- The state `δ_{inY}` (desirability `0`) is strictly calibrated for `(in, y)` at both points of
the threat tree. -/
theorem profHH_strictOCAt (d : Pt2) :
    StrictOCAt (fun _ => State.dirac TwoW.inY 0) twoObs profHH threat d := by
  intro _
  refine ⟨fun X => ?_, fun X _ _ => ?_⟩
  · show (State.dirac TwoW.inY 0).pr X * nu profHH threat (twoObs d) =
      nu profHH threat (X ∩ twoObs d)
    rw [State.dirac_pr, profHH_nu_threat, profHH_nu_threat]
    cases d <;> simp [twoObs]
  · show (State.dirac TwoW.inY 0).V X * nu profHH threat (X ∩ twoObs d) =
      paySum profHH threat (X ∩ twoObs d)
    rw [State.dirac_V, profHH_paySum_threat, zero_mul]

/-- Both observations are realized under `(in, y)`: `ν(O₁) = ν(O₂) = 1`. -/
theorem profHH_nu_obs_pos (d : Pt2) : 0 < nu profHH threat (twoObs d) := by
  rw [profHH_nu_threat]
  cases d <;> simp [twoObs]

/-- **D1 approves the worst deterministic profile `(in, y)` on the threat tree**, with the limit
states pinned to `δ_{inY}` at both (realized) points: the limit state is the strict one
(`limitOCAt_of_strictOCAt_of_pos`), `A_d^+ = {in}` at `p1` and `{y}` at `p2`, and `T_EDT`
holds by the `A_d^+` collapse — exactly as for `(a, y)`, with no null point in sight. -/
theorem profHH_limitStateEdt_threat :
    LimitStateEdt twoObs twoActEv profHH threat (fun _ => State.dirac TwoW.inY 0) ∧
    value profHH threat = 0 ∧ ¬ IsOptimal profHH threat := by
  refine ⟨⟨fun d _ => ?_, fun d _ _ a ha => ?_⟩, ?_, fun h => ?_⟩
  · exact limitOCAt_of_strictOCAt_of_pos _ _ _ _ d (profHH_nu_obs_pos d) (profHH_strictOCAt d)
  · rw [mem_argmaxPlus]
    cases d <;> cases a <;> simp [profHH, proc2, FinDistr.act2] at ha <;>
      simp [APlus, State.dirac_pr, State.dirac_V, twoActEv]
  · show value (proc2 0 0 _ _ _ _) (twoPoint 1 2 0) = 0
    rw [twoPoint_value]; norm_num
  · have := h inX
    unfold inX profHH threat at this
    rw [twoPoint_value, twoPoint_value] at this
    norm_num at this

end Cleanroom.Decision.DpEdtUdtFair.AuditR2
