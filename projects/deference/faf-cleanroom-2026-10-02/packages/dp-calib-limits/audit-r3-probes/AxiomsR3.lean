import Cleanroom.Decision.DpCalibLimits

/-!
# Audit r3 (adversarial) probe — axioms of the headlines added in repair round 2, plus the core
headlines

Round 2's `Axioms.lean` covered 50 headlines before `WitnessesR2`, `Curve` and `MugPerRun`
existed. This file prints the axioms of every bold declaration in those three modules and of the
core headlines, so that "nothing rests on `testSeq_exists_open`" is machine-checked for the
current package, not inferred from the gate's aggregate line.
-/

namespace Cleanroom.Decision.DpCalibLimits

-- Repair round 2: Curve.lean (T7(e))
#print axioms miniature_nu_eq
#print axioms miniature_manifold_iff
#print axioms manifold_equal_marginals
#print axioms prodState_half_third_not_mem_manifold
#print axioms prodState_half_third_not_in_hull
#print axioms miniature_hull_exceeds_manifold

-- Repair round 2: MugPerRun.lean (T12(c))
#print axioms mug1_perRunClauses_iff_strict
#print axioms mug1_perRunMasked_iff_maskedOC

-- Repair round 2: WitnessesR2.lean
#print axioms cqPay_condExp_deviate_nontrivial
#print axioms tb_flip_below
#print axioms tb_flip_above
#print axioms coinQuery_twoAct_instance
#print axioms t1_msr17_instance

-- Core headlines (re-check)
#print axioms popperLimit_isPopper
#print axioms limitCond_eq_lps
#print axioms limitCondRay_eq_of_pos
#print axioms limitOCRayAt_imp_strictOCAt
#print axioms twoRoute_values
#print axioms threeAct_ray_dependent
#print axioms twoAct_single_point_ray_independent
#print axioms nonnegNear0_iff_eventually
#print axioms eventTremble_iff_nonnegNear0
#print axioms miniature_testSeq
#print axioms miniature_ff_strict_ts
#print axioms msrAt_of_ts_of_realized
#print axioms ts_not_msr
#print axioms tsTr_epsFP
#print axioms msr17At_of_msrAt_recorded
#print axioms t1_msr17_not_msr
#print axioms ts_of_epsFP_limit
#print axioms fantasy541_letter_empty
#print axioms appendixB_verdict
#print axioms zo1_separation
#print axioms cancellation
#print axioms condExp_deviate_eq
#print axioms nu_deviate_actEv_eq_self
#print axioms zero_survives_iff
#print axioms opaque_accuracy
#print axioms sigmaPi_not_consistent
#print axioms chicken_no_fixed_point_of_unique_max
#print axioms ratifiability_lemma
#print axioms miniature_masked_weak_all
#print axioms tb_perRunMasked_rejects
#print axioms tb_masked_flip
#print axioms advice_silent_on_trap
#print axioms chanceTwin_refutes
#print axioms popperLimit_twin_leaves
#print axioms levi_vacuity

end Cleanroom.Decision.DpCalibLimits
