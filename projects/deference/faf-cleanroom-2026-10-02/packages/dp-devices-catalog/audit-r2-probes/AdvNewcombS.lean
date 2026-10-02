import Cleanroom.Decision.DpDevicesCatalog.TableNewcomb

set_option autoImplicit false

/-!
# `dp-devices-catalog` · audit round 2 (adversarial) · probe III: the TN-V2 device cells' `0 < S`

Evidence file for `dp-devices-catalog-audit-r2-adversarial.md`. **Not imported by the library.**

* Q7 — `tnV2_eventTremble_iff` and `tnV2_adviceEdt_iff` (D2 and D4 approve exactly `(2,2)`)
  carry `0 < S`, and it is load-bearing: at `S = 0` the two act-conditional values tie at both
  boxes (`L` vs `L`, `0` vs `0`), so **every** procedure is D2-consistent and D4-consistent on
  V2. The cells are therefore not true for a trivial reason, and the headline
  `tnV2_optimum_d2_inconsistent` genuinely needs the small box to be worth something.
-/

namespace Cleanroom.Decision.DpDevicesCatalog.AuditR2

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpDevicesCatalog

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L : ℚ)

/-- Q7(a): at `S = 0` every procedure is D2-consistent on V2. -/
theorem Q7_eventTremble_S_zero (hp0 : 0 < p) (hp1 : p < 1) (C : Proc TnPt (fun _ => Box) ℚ) :
    EventTrembleEdtConsistent tnObs tnActEv C (tnV2 p h0 h1 L 0) := by
  refine ⟨1, one_pos, fun ε e0 e1 _ d _ _ _ a _ => ?_⟩
  have hfs := tremble_fullSupport C ε e0 e1
  cases d
  · refine ⟨(tnV2_nu_actObs_pos p h0 h1 L 0 hfs hp0 hp1 a).1, fun b _ => ?_⟩
    rw [(tnV2_tremble_condExp p h0 h1 L 0 C hp0 hp1 ε e0 e1 b).1,
      (tnV2_tremble_condExp p h0 h1 L 0 C hp0 hp1 ε e0 e1 a).1]
    cases a <;> cases b <;> simp
  · refine ⟨(tnV2_nu_actObs_pos p h0 h1 L 0 hfs hp0 hp1 a).2, fun b _ => ?_⟩
    rw [(tnV2_tremble_condExp p h0 h1 L 0 C hp0 hp1 ε e0 e1 b).2,
      (tnV2_tremble_condExp p h0 h1 L 0 C hp0 hp1 ε e0 e1 a).2]
    cases a <;> cases b <;> simp

/-- Q7(b): at `S = 0` every procedure is D4-consistent on V2. -/
theorem Q7_adviceEdt_S_zero (hp0 : 0 < p) (hp1 : p < 1) (C : Proc TnPt (fun _ => Box) ℚ) :
    AdviceEdt tnObs tnActEv C (tnV2 p h0 h1 L 0) := by
  intro d _ _ _ a _
  cases d
  · refine ⟨(tnV2_nuPoly_actObs_ne_zero p h0 h1 L 0 C hp0 hp1 a).1, fun b _ => ?_⟩
    rw [(tnV2_limitVal p h0 h1 L 0 C hp0 hp1 b).1, (tnV2_limitVal p h0 h1 L 0 C hp0 hp1 a).1]
    cases a <;> cases b <;> simp
  · refine ⟨(tnV2_nuPoly_actObs_ne_zero p h0 h1 L 0 C hp0 hp1 a).2, fun b _ => ?_⟩
    rw [(tnV2_limitVal p h0 h1 L 0 C hp0 hp1 b).2, (tnV2_limitVal p h0 h1 L 0 C hp0 hp1 a).2]
    cases a <;> cases b <;> simp

end Cleanroom.Decision.DpDevicesCatalog.AuditR2
