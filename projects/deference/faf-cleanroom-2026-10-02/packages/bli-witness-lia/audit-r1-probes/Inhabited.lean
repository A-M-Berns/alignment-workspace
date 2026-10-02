import Cleanroom.Bli.BliWitnessLia

/-!
# Audit round 1 (adversarial) — probe: the full hypothesis package is inhabited, and axioms

Every core headline of `bli-witness-lia` takes `(hK : ∀ n < H, k₀ n + 1 ≤ K) (hn : n < H)
(h2 : 2 ≤ n)` (plus stakes). This probe instantiates them all at the instance of record the
report names — `H = 4`, `n = 2`, `K = segmentK 4`, `(c, V) = (10, 100)` — and at `n = 3`, so a
`pass` on non-vacuity means the hypotheses are jointly satisfiable and every headline actually
produces a closed statement about a concrete prior. It also instantiates T3 at a concrete cell
quote code (`spliceCellQuote`, FAF's `ofComputable` at the splice's cell truth), and T4 at
`n + 1 = 3 < 4`, and T9 at `n = 2`.

Then `#print axioms` on every headline and on the dependency theorem the whole package rests on
(`Segment.linkedSplice_isLogicalInductor`). Expected: `propext`, `Classical.choice`, `Quot.sound`
only — no `sorryAx` (nothing here may rest on an OPEN row).
-/

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliExactBase Cleanroom.Bli.BliExactBase.Skel
open Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist
open Cleanroom.Bli.BliWitnessLia

namespace AuditR1Inhabited

noncomputable section

/-- The `K` of record and its bound. -/
abbrev hK4 : ∀ n < 4, Segment.k₀ n + 1 ≤ segmentK 4 := fun n hn => k₀_add_one_le_segmentK hn

/-- A concrete cell quote code of the linked splice's cell truth at `H = 4`. -/
def q4 : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth 4 Segment.linkedPrice halfRound) :=
  spliceCellQuote 4 Segment.linkedPrice halfRound halfRound_computable

-- T1 at (H, n) = (4, 2) and (4, 3)
#check @stateMass_ask_rec 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 10 100
#check @stateMass_ask_rec 4 (segmentK 4) hK4 3 (by norm_num) (by norm_num) 10 100
#check @coin_price 4 2 (by norm_num) (by norm_num)
#check @baseTable_eq_actual 4 2 (by norm_num)
#check @classMass_other 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 10 100
-- T2
#check @verdict 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 10 100
#check fun r₀ => @instance_pay 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) r₀
#check fun r₀ => @instance_rules 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) r₀
#check fun r₀ => @not_classInert 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 10 100 r₀ (by norm_num)
#check fun r₀ => @hUnif 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 10 100 r₀
#check fun r₀ => @ndpol 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 10 100 r₀
-- T3 at the concrete code
#check fun r₀ => @segment_predicate_check 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 10 100 r₀ q4
#check @not_D_PC_on 4 (by norm_num)
#check @not_nonDegenerate_twoPointLaw 4 (segmentK 4) 2 hK4 (by norm_num) (by norm_num)
#check fun r₀ => @shadows 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 10 100 r₀
-- T4 at n = 2, n + 1 = 3 < 4
#check fun r₀ => @stateMass_realized_zero 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 10 100 r₀
#check fun r₀ => @witness_is_not_realized 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 10 100 r₀ q4
#check @realized_pattern_charged 4 2 (by norm_num) (by norm_num) q4
-- T5
#check fun r₀ => @not_noCrossBranch 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 10 100 r₀ (by norm_num)
#check fun r₀ => @reflective 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 10 100 r₀
#check fun r₀ => @instance_refuse 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 100 10 r₀ (by norm_num)
#check fun r₀ => @charged_distinct 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 10 100 r₀
#check day_two_first
-- T9 at n = 2
#check fun r₀ => @rules₂ 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 10 100 r₀
#check fun r₀ Qh => @classMass_other₂ 4 (segmentK 4) hK4 2 (by norm_num) (by norm_num) 10 100 r₀ Qh

/-! ## Axioms -/

-- the dependency fact the package rests on
#print axioms Segment.linkedSplice_isLogicalInductor
#print axioms Segment.segment_package_inhabited_q
#print axioms Segment.segment_D_NNUcell_on_q
#print axioms segmentBli_isBLI_scoped
-- T1
#print axioms segmentSist
#print axioms stateMass_ask_rec
#print axioms stateMass_other_zero
#print axioms classMass_ask
#print axioms classMass_rec
#print axioms classMass_other
#print axioms baseTable_eq_actual
#print axioms coin_price
#print axioms askC_askTable
#print axioms askTable_ne_recTable
-- T2
#print axioms verdict
#print axioms isOneStepChoice_pay
#print axioms isUpdatefulChoice_refuse
#print axioms not_classInert
#print axioms hUnif
#print axioms faith
#print axioms ndpol
#print axioms instance_pay
#print axioms instance_rules
-- T3
#print axioms segment_predicate_check
#print axioms not_D_PC_on
#print axioms not_D_ND_on_of_pinned
#print axioms not_nonDegenerate_twoPointLaw
#print axioms shadows
-- T4
#print axioms stateMass_realized_zero
#print axioms realized_pattern_charged
#print axioms witness_is_not_realized
#print axioms realized_not_ask
-- T5
#print axioms not_noCrossBranch
#print axioms reflective
#print axioms instance_refuse
#print axioms charged_distinct
#print axioms freshCoord_not_small_one
#print axioms day_two_first
-- T9
#print axioms stateMass_sistSkel_h1
#print axioms stateMass₂_eq
#print axioms classMass_ask₂
#print axioms classMass_rec₂
#print axioms classMass_other₂
#print axioms verdict₂
#print axioms stateMass₂_askTable₂_pos
#print axioms rules₂

end

end AuditR1Inhabited
