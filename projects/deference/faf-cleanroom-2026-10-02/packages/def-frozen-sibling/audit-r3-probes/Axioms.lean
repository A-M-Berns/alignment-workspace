import Cleanroom.Deference.DefFrozenSibling

/-!
# Audit round 3 (adversarial) probe — axioms of every headline and of every round-2 addition

`#print axioms` on the ledger headlines, the §E instantiations, and the declarations added in
repair round 2. Expected: `sorryAx` only in the five listed OPEN names (`frozenSystem_exists`,
`timely_cofinite_const`, `timely_not_mono_open`) and the three `li-projection`-dependent rows
(`projection_pair_offG_atom`, `projection_pair_daySet`, `projection_pair_undecidable_contract`).
Not imported by the library.
-/

open Cleanroom.Deference.DefFrozenSibling

-- headlines
#print axioms tracking
#print axioms tracking_exact
#print axioms tracking_ofTendsto
#print axioms metaTrust
#print axioms metaTrust_expect
#print axioms gated_pin
#print axioms gated_three_ge
#print axioms engineA
#print axioms engineA_quote
#print axioms engineA_ofCert
#print axioms engineA_truth
#print axioms engineA_truth_ofPattern
#print axioms condTower_onG
#print axioms condTower_onG_weighted
#print axioms condTower_onG_ofCert
#print axioms valueTwoOption_onG
#print axioms thresholdAbove_onG
#print axioms valueConst_onG
#print axioms tsFails_offG
#print axioms limit_agree_onG
#print axioms limit_agree_onG_sib_Hplus
#print axioms projection_pair_offG_atom
#print axioms projection_pair_daySet
#print axioms ratio_asympGE_of_denom_bdd
#print axioms ratio_fails_of_denom_tendsto_zero
#print axioms decidedBy_mono
#print axioms timely_not_horizon_only
#print axioms timely_computable
#print axioms calibration_onG_degenerate
#print axioms ledgerLiteral_not_mem_of_tagFree
#print axioms twoPoint_indicator_breaks_inequality
-- OPEN rows
#print axioms frozenSystem_exists
#print axioms timely_cofinite_const
#print axioms timely_not_mono_open
-- repair round 2 additions
#print axioms exists_tol_iff
#print axioms timely_all_of_diagonal
#print axioms limit_agree_of_decidedBy
#print axioms limit_pinned_of_decidedAt
#print axioms undecidable_of_atomFree
#print axioms projection_pair_undecidable_contract
#print axioms offG_not_timely_any
#print axioms hz_offG
#print axioms a5_asymp
#print axioms evenContract_price_one
#print axioms pointwise_deference_fails_offG
#print axioms pinnedContract_tag
#print axioms halting_atom_mem_paperDP
#print axioms anti_gap
#print axioms anti_timely_iff
#print axioms pinned_base0_decided
#print axioms pinned_base0_decided'
#print axioms cofinite_const_iff
#print axioms notMono_tol_iff
#print axioms engineA_of_diagonal
#print axioms hpat₁_onG
#print axioms hpat₀_onG
#print axioms engineA_truth_onG_noHz
-- the §E instantiations
#print axioms engineA_onG
#print axioms limit_agree_onG_onG
#print axioms hz_onG
#print axioms tracking_onG
#print axioms metaTrust_onG
#print axioms metaTrust_expect_onG
#print axioms engineA_truth_onG
#print axioms condTower_onG_onG
#print axioms valueTwoOption_onG_onG
#print axioms thresholdAbove_onG_onG
#print axioms valueConst_onG_onG
#print axioms calibration_onG_degenerate_onG
