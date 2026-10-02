import Cleanroom.Corrigibility.CorrLegitGeneral

/-! Audit r4 (adversarial) probe: `#print axioms` on every declaration repair round 3 added or
re-kinded, plus the headlines they replace or complete. Expected: `propext`, `Classical.choice`,
`Quot.sound` only — no `sorryAx` anywhere (the package's open list is empty). -/

open Cleanroom.Corrigibility.CorrLegitGeneral

-- ThreeCellRefuted
#print axioms localTotalTrust_imp_weakLocalValue_refuted
#print axioms localTotalTrust_imp_localValue_hdet_refuted
#print axioms weakLocalValue_open_statement_false
#print axioms F7_totalTrustWrt
#print axioms F7_not_weakValuesWrt
#print axioms F7_not_valuesWrt
#print axioms F7_hdet
#print axioms S7_recommended_eq
#print axioms scores7
-- ThreeCellRefutedFull
#print axioms localTotalTrust_imp_weakLocalValue_refuted_fullSupport
#print axioms F7F_totalTrustWrt
#print axioms F7F_not_weakValuesWrt
#print axioms F7F_rows_pos
-- ThreeCell (the surviving true part)
#print axioms localTotalTrust_imp_localValue_refuted
#print axioms totalTrust_imp_weakValuesWrt_id
#print axioms weakValuesWrt_questionOf_of_simpleTrustOn
#print axioms valuesWrt_questionOf_of_simpleTrustOn
-- WitnessesFn50
#print axioms fn50_single_score_not_local_tt
#print axioms fn50_not_totalTrustWrt
#print axioms fn50_brier_q
-- WitnessesMutualSmall
#print axioms mA_mH_witness
#print axioms mA_mH'_witness
#print axioms mutual_totalTrust_eq
#print axioms mutual_totalTrust_of_eq
-- WitnessesReflectVisible
#print axioms rv3_visible_witness
#print axioms rv3_not_legitReflectsWrt_ae
#print axioms legitReflectsWrt_unsat_of_visible
#print axioms legitReflectsWrt_unsat_of_visible_ae
-- rows whose Fidelity/Hyps text changed in repair round 3
#print axioms compose_global
#print axioms twoState_press_covariance
#print axioms s6_headline
#print axioms valuesWrt_questionOf_core
