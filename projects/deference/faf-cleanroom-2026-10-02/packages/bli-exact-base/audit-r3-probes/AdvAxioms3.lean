import Cleanroom.Bli.BliExactBase

/-!
# Audit round 3 (adversarial) — probe: axioms of the repair-round-2 declarations

`#print axioms` on the declarations added or restated in repair round 2, on the five judged
items, and on the six OPEN rows. Expected: `sorryAx` on the six OPEN rows only; every other line
lists at most `propext`, `Classical.choice`, `Quot.sound`.
-/

open Cleanroom.Bli.BliExactBase

-- repair round 2: Open / Live (the quotation guard)
#print axioms Live.ownQuoteLane_reflectsRounded
#print axioms Live.ownQuoteLane_literal_fresh
#print axioms Live.ownQuoteLane_stageFresh
#print axioms Live.ownQuoteLane_literal_undecided
#print axioms Live.spliceCF_ownQuoteLane
#print axioms Live.quoteLane_clause_inhabited
#print axioms Live.D_NNUcell_own_pointwise
#print axioms Live.not_ownQuoteLane_of_constant
#print axioms Live.certFamily_reflects
#print axioms Live.certFamily_live
#print axioms Live.certFamily_reflects_live
#print axioms Live.certFamily_not_ownQuoteLane
#print axioms Live.certFamily_identity
#print axioms Live.certFamily_dogmatic
-- repair round 2: QuoteLane / Kernel / Segment (the code as a parameter)
#print axioms spliceCellSentenceQ_reflected
#print axioms spliceCellSentenceQ_eventually_small
#print axioms pinned_eventually_spliceQ
#print axioms stageFresh_spliceQ
#print axioms Kernel.spliceCFq_litAtoms
#print axioms Segment.linkedCF_eq_q
#print axioms Segment.hf_any
#print axioms Segment.linked_pinned_eventually_q
#print axioms Segment.segment_package_inhabited_q
#print axioms Segment.linked_nnu_day_q
#print axioms Segment.segment_D_NNUcell_on_q
#print axioms Segment.segment_D_NNUcell_on_of_le
#print axioms Segment.kernel_identity_q
#print axioms Segment.linked_literal_dogmatic_q
#print axioms Segment.linked_not_D_ND_on_q
#print axioms Segment.linked_actual_state_charged_q
#print axioms Segment.linked_boundary_q
#print axioms Segment.trilemma_sharp_segment_q
-- repair round 2: Uncharged
#print axioms Uncharged.tent_actual_next_zero_mesh
#print axioms Uncharged.tent_actual_next_zero_denominator
-- the five judged items
#print axioms splice_isLogicalInductor
#print axioms segment_D_PCsmall_on
#print axioms segment_D_ND_on
#print axioms Segment.segment_D_NNUcell_on
#print axioms Segment.segment_package_inhabited
#print axioms Obstruction.obstruction
#print axioms Convex.selfTrustSet_convex
#print axioms Bundle.BundleMarket.bundleMarket_not_acceptable
-- the six OPEN rows (sorryAx expected here and nowhere else)
#print axioms exactlyEnforceable_allDays
#print axioms worldMarket_exists
#print axioms bundleMarket_LI_exists
#print axioms weakening_exists
#print axioms Segment.linked_segment_day_exists
#print axioms Skel.segmentBli_isLogicalInductor
