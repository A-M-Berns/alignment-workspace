import Cleanroom.Decision.DpEdtUdtFair.Assignment
import Cleanroom.Decision.DpEdtUdtFair.DfTheorem
import Cleanroom.Decision.DpEdtUdtFair.Ca3
import Cleanroom.Decision.DpEdtUdtFair.LimitState
import Cleanroom.Decision.DpEdtUdtFair.PermWitness
import Cleanroom.Decision.DpEdtUdtFair.GradedWitnesses
import Cleanroom.Decision.DpEdtUdtFair.Records
import Cleanroom.Decision.DpEdtUdtFair.Newcomblike
import Cleanroom.Decision.DpEdtUdtFair.Necessity

/-!
# `dp-edt-udt-fair` · audit round 2 (fidelity) · probe A1: axioms of the repair-round-1 headlines

Evidence file for `dp-edt-udt-fair-audit-r2-fidelity.md`. **Not imported by the library.**
(`Axioms.lean` in this directory is the adversarial lens's probe; the two were written
concurrently and overlap by design.)

A1 — `#print axioms` of every declaration repair round 1 added or re-stated (T5, T12(b),
CA-3′ and the DF self-models, the D1 clauses, `permPay`, the pinned mugging witness, T16(b), the
ZO-2 chain, `N3 ↔ N1`, the a1Node device rows). Expected: `propext`, `Classical.choice`,
`Quot.sound` only — no `sorryAx` (the one `Open.lean` row and `dp-calibration`'s
`testSeq_exists_open` must be off every path). Read the printed lines in the `lean-check` output.
-/

namespace Cleanroom.Decision.DpEdtUdtFair.AuditR2Fidelity

-- T5
#print axioms Cleanroom.Decision.DpEdtUdtFair.exists_pointwise_best
#print axioms Cleanroom.Decision.DpEdtUdtFair.stronglyFair_assignment
#print axioms Cleanroom.Decision.DpEdtUdtFair.stronglyFair_assignment_max
#print axioms Cleanroom.Decision.DpEdtUdtFair.dupPay_assignment_witness
-- T12(b)
#print axioms Cleanroom.Decision.DpEdtUdtFair.FairClass.condExp_eq_Q'
#print axioms Cleanroom.Decision.DpEdtUdtFair.FairClass.dfMasked_at
#print axioms Cleanroom.Decision.DpEdtUdtFair.FairClass.dfMasked_tEdt_iff
#print axioms Cleanroom.Decision.DpEdtUdtFair.fairClass_dfMasked_isOptimal
#print axioms Cleanroom.Decision.DpEdtUdtFair.dupPay_dfMasked_witness
-- CA-3′ and DF self-models
#print axioms Cleanroom.Decision.DpEdtUdtFair.stronglyFair_size_lt_of_strictlyBelow
#print axioms Cleanroom.Decision.DpEdtUdtFair.FairClass.exists_dfMasked
#print axioms Cleanroom.Decision.DpEdtUdtFair.FairClass.exists_dfMasked_tEdt_ofFun
#print axioms Cleanroom.Decision.DpEdtUdtFair.FairClass.dfMasked_tEdt_of_eventTremble
#print axioms Cleanroom.Decision.DpEdtUdtFair.fr12_outY_isOptimal_not_dfMasked_tEdt
-- D1 clauses
#print axioms Cleanroom.Decision.DpEdtUdtFair.outY_limitStateEdt
#print axioms Cleanroom.Decision.DpEdtUdtFair.threat_outY_untrembled_all
#print axioms Cleanroom.Decision.DpEdtUdtFair.fantasy_outY_untrembled_all
-- witnesses and refutation rows
#print axioms Cleanroom.Decision.DpEdtUdtFair.permPay_theorem3_witness
#print axioms Cleanroom.Decision.DpEdtUdtFair.mug1_graded_witness_13
#print axioms Cleanroom.Decision.DpEdtUdtFair.frec_not_subtreeVeridical_refuted
#print axioms Cleanroom.Decision.DpEdtUdtFair.claim32_refuted
#print axioms Cleanroom.Decision.DpEdtUdtFair.a1Node_fr11_device
#print axioms Cleanroom.Decision.DpEdtUdtFair.a1Node_not_occTremble
-- compositions
#print axioms Cleanroom.Decision.DpEdtUdtFair.FairClass.zo2_chain
#print axioms Cleanroom.Decision.DpEdtUdtFair.almostFair_N3_iff_N1

end Cleanroom.Decision.DpEdtUdtFair.AuditR2Fidelity
