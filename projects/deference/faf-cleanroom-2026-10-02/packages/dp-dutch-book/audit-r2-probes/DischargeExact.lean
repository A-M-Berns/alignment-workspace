import Cleanroom.Decision.DpDutchBook

/-!
Audit round 2, adversarial lens — probe 1: is the repaired discharge *exactly* the OPEN row?

Round 1 (fidelity B1 = adversarial B2) found `testSeq_exists_open_discharged` carried an extra
`[Fintype ι]`. The repair claims the two statements are now identical "up to names". A `#check`
comparison is read by eye; this probe makes the kernel compare: the OPEN row's type is written
out once, verbatim from `Devices.lean:75` (instance binders in its `variable` order, the
theorem's own `[∀ d, Nonempty (acts d)]` last, explicit arguments `(obs) (actEv) (B) (_hpruned)`),
and both declarations are ascribed to it. Binder *order* is part of the type, so if either
`example` fails to elaborate the signatures differ. The `#print axioms` lines re-run round 1's
axiom check after the repair (no `sorryAx` expected on anything but the OPEN row itself).
Not imported by the library.
-/

namespace Cleanroom.Decision.DpDutchBook.AuditR2Adv

open Cleanroom.Found.DpCoreTree Cleanroom.Decision.DpCalibration

/-- The OPEN row's statement, written out. -/
abbrev OpenRowType : Prop :=
  ∀ {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
    [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]
    (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω) (B : Tree Ω ι acts ℝ),
    (∀ ℓ, 0 < B.chanceWeight ℓ) → ∃ C : Proc ι acts ℝ, TestSeqTrembleEdtConsistent obs actEv C B

/-- The OPEN row has this type (sanity: the transcription is the row). -/
example : OpenRowType := @Cleanroom.Decision.DpCalibration.testSeq_exists_open

/-- The discharge has the same type: no `Fintype ι`, same binder order. -/
theorem discharge_has_open_row_type : OpenRowType :=
  @Cleanroom.Decision.DpDutchBook.testSeq_exists_open_discharged

#print axioms discharge_has_open_row_type
#print axioms Cleanroom.Decision.DpDutchBook.testSeq_exists_open_discharged
#print axioms Cleanroom.Decision.DpDutchBook.testSeq_exists
#print axioms Cleanroom.Decision.DpDutchBook.d2At_exists
#print axioms Cleanroom.Decision.DpDutchBook.fpFace_hasClosedGraphOn
#print axioms Cleanroom.Decision.DpDutchBook.miniR_d2At_qStar
#print axioms Cleanroom.Decision.DpDutchBook.miniR_testSeq
#print axioms Cleanroom.Decision.DpDutchBook.msrAtD4_exists
#print axioms Cleanroom.Decision.DpDutchBook.miniR_msrAtD4_exists_witness
#print axioms Cleanroom.Decision.DpDutchBook.yankees_no_msrAtD4
#print axioms Cleanroom.Decision.DpDutchBook.nashMap_fixed_iff_msrAtD4
#print axioms Cleanroom.Decision.DpDutchBook.nashMap_two_cycle
#print axioms Cleanroom.Decision.DpDutchBook.opaque_inversion
#print axioms Cleanroom.Decision.DpDutchBook.opaque_bookable_and_approved
#print axioms Cleanroom.Decision.DpDutchBook.regardless_buys_iff
#print axioms Cleanroom.Decision.DpDutchBook.mug1_hybrid_approved_and_bookable
#print axioms Cleanroom.Decision.DpDutchBook.mug1_regardless_buys_iff
#print axioms Cleanroom.Decision.DpDutchBook.didHyp_makesInconsistent
#print axioms Cleanroom.Decision.DpDutchBook.bundle_2140_seed
#print axioms Cleanroom.Decision.DpDutchBook.xor_fiberForced_sub
#print axioms Cleanroom.Decision.DpDutchBook.majE'_values

end Cleanroom.Decision.DpDutchBook.AuditR2Adv
