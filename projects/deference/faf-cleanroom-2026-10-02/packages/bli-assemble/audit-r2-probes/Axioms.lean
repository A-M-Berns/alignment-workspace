import Cleanroom.Bli.BliAssemble

/-!
# Audit probe (bli-assemble, round 2, adversarial): axioms of each row of record after repair round 1

Round 1's `Axioms.lean` listed 19 rows; this one adds every declaration repair round 1 landed or
regraded (`SmallList.lean`, `bliHistory_ne_lia_from`, `bliHistory_stateAtom_tendsto_one_of_stateLearns`,
the `C`-regraded conditionals, the N+ conjunct suppliers of `bli_hypotheses_paperDP`) so that a
`sorryAx` hiding behind `bli-overlay`'s `firm_support_subset_smallSet` or anywhere in the new
material would show. Expected: every row below `[propext, Classical.choice, Quot.sound]`; the six
listed open rows carry `sorryAx`.
-/

open Cleanroom.Bli.BliAssemble

-- rows of record from round 0 (re-checked)
#print axioms bliHistory_eq_overlay
#print axioms tentMap
#print axioms tentMap_fires_two_chain
#print axioms chainProbH_singleton_eq_lastMarg
#print axioms chainProbH_restart
#print axioms denoteRat_chainExpr
#print axioms writeOutCoding
#print axioms writeOutCode_injOn
#print axioms writeOutCode_large
#print axioms writeOutCode_card_le_log
#print axioms tentRunAgrees
#print axioms bliHistory_isLogicalInductor_of
#print axioms bliHistory_tent_package
#print axioms bliHistory_tent_LI_and_BLI
#print axioms bliHistory_isLogicalInductor_denominator
#print axioms bliHistory_isLogicalInductor_bliDP
#print axioms bliDP_settles_states
#print axioms bliHistory_pastStateAtom
#print axioms liaStates_eq_of_eq_prefix
#print axioms actualFix_spec
#print axioms exists_stateLearns_fixpoint
#print axioms exists_stateLearns_fixpoint_paperDP
#print axioms bliHistory_eventually_eq_on_machineSentenceCodes
#print axioms bliHistory_asympEq_base
#print axioms limitingBelief_bliHistory_eq
#print axioms bliHistory_provind_iff_base
#print axioms lic_provind_true_bliHistory_of_base
#print axioms exists_mem_faceProd
#print axioms not_machineSentenceCodes_nextStateAtoms
#print axioms bliHistory_pos_on_face
#print axioms bliHistory_ne_base_on_stateAtoms_dichotomy
#print axioms bliHistory_ne_base_on_stateAtoms_of_zero
#print axioms liaBase_isLogicalInductor
#print axioms tentExprMap_fires_every_day
#print axioms stateReader_ec
#print axioms stateReader_splice_ne
#print axioms bliHistory_ne_lia_of_offSupport
#print axioms bli_hypotheses_paperDP

-- landed or regraded in repair round 1
#print axioms smallList
#print axioms mem_sentencesUpTo_of_tokenSize_le
#print axioms smallList_toFinset
#print axioms smallList_nodup
#print axioms smallList_pairwise
#print axioms smallList_length
#print axioms smallSorted_map_val
#print axioms writeOutDigits_eq_smallList
#print axioms bliHistory_ne_lia_from
#print axioms bliHistory_stateAtom_tendsto_one_of_stateLearns

-- the dependency fact the new N+ rests on (bli-overlay T2)
#print axioms Cleanroom.Bli.BliOverlay.firm_support_subset_smallSet

-- the open rows (expected: sorryAx present)
#print axioms tentOracle_exists
#print axioms tentCertificate
#print axioms bliOv_computableTable
#print axioms bliHistory_isLogicalInductor_of_certificate
#print axioms bliHistory_isLogicalInductor
#print axioms bli_package_paperDP
