import Cleanroom.Decision.DpFirstpersonSc.WitnessesAn3
import Cleanroom.Decision.DpFirstpersonSc.Lift

/-!
Audit r3 (adversarial) probe for `AuditPassAt`'s `V`-clause: every failing audit witness in the
package (`mug1_tailsCertain_fails_audit'`, `tys_five_fails_audit_uniform'`, `coverFail_stamped_fails'`,
`stagePostState_fails_audit`) fails on the `P`-clause, so a reader could suspect the `V`-clause is
idle. It is not: on the instance-blind tree (`blindTree`, T3(c)) the strict-OC state at `⊤` passes
per-run clause 1 (its `P` is the per-run state's, `blind_P_agree`) and fails per-run clause 2 at
`X = ⊤` (`V = ½` against the per-run `1`), hence fails `PerRunClausesAt` — which by T1(a) is the
stamped audit verdict at `d`. The package's `blind_V_criterion_fails` carries the same fact through
T3(b)'s criterion; this probe states it as the two clauses directly. Not imported by the library.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree hiding mass mass_mono mass_union mass_univ mass_nonneg
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Finset

/-- The strict state at `⊤` on the instance-blind tree. -/
noncomputable abbrev probeBlindStrict : State Bool ℚ :=
  calibratedState cfProcA blindTree Finset.univ (nu_univ_pos _ _)

/-- Per-run clause 1 holds for the strict state (its `P` is the per-run state's). -/
theorem probe_blind_strict_clause1 :
    PerRunClause1At (fun _ => probeBlindStrict) cfProcA blindTree .d :=
  (P_eq_occState_iff_perRunClause1At cfProcA blindTree .d (fun _ => probeBlindStrict)
    blind_occ_pos).mp blind_P_agree.symm

/-- Per-run clause 2 fails for the strict state at `X = ⊤`: `½ · ½ ≠ ½`. -/
theorem probe_blind_strict_not_clause2 :
    ¬ PerRunClause2At (fun _ => probeBlindStrict) cfProcA blindTree .d := by
  intro h
  have h1 : 0 < probeBlindStrict.pr Finset.univ := by
    show 0 < probOf _ Finset.univ
    rw [probOf_univ]; exact one_pos
  have h2 : 0 < Tree.mass cfProcA blindTree (worldEv blindTree Finset.univ ∩ occ .d blindTree) := by
    change 0 < Tree.mass cfProcA blindTree (occEv blindTree .d Finset.univ)
    rw [blind_mass_occEv]; simp
  have := h Finset.univ h1 h2
  change probeBlindStrict.V Finset.univ * Tree.mass cfProcA blindTree (occEv blindTree .d Finset.univ) =
    occPay cfProcA blindTree .d Finset.univ at this
  rw [blind_mass_occEv, blind_occPay, blind_V_strict] at this
  simp at this

/-- **The `V`-clause separates**: the strict state passes clause 1 and fails the per-run
clauses, i.e. (T1(a)) fails the stamped audit at `d` on its `V`-clause alone. -/
theorem probe_blind_audit_V_separates :
    PerRunClause1At (fun _ => probeBlindStrict) cfProcA blindTree .d ∧
      ¬ PerRunClausesAt (fun _ => probeBlindStrict) cfProcA blindTree .d :=
  ⟨probe_blind_strict_clause1, fun h => probe_blind_strict_not_clause2 h.2⟩

end Cleanroom.Decision.DpFirstpersonSc
