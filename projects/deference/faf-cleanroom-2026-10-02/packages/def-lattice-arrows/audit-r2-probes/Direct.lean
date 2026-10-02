import Cleanroom.Deference.DefLatticeArrows.Witness

/-!
# Audit r2 (adversarial) probe: the T6 witness's conclusion without the arrow

Repair round 1 regraded `Witness.transfer_witness` / `expert_bound_transfer_witness(_succ)` from
N+ to N− with the reason "the source is valued `1` in every world, so the conclusion is
`lic_provind_true` on `ψ ∘ f` directly". This probe machine-checks that reason: the statement of
`expert_bound_transfer_witness_succ` is proved here from `lic_provind_true` and
`literalIndicator_expect` alone — no `WeightQuote`, no TT instance, no `transfer_instance`,
no T0. So the arrow does no work on that instance, which is exactly what N− records.

Not imported by the library. Audit evidence only.
-/

namespace Cleanroom.Deference.DefLatticeArrows.AuditR2

open LogicalInduction Filter Topology Cleanroom.Found.DefLattice
open Cleanroom.Deference.DefLatticeArrows Cleanroom.Deference.DefLatticeArrows.Witness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- The statement of `Witness.expert_bound_transfer_witness_succ`, by provability induction on
the shifted tautology family alone. -/
theorem succ_witness_direct :
    (fun n => (literalIndicator (tautFamily (succDeferral n))).expect (liaHistory (paperDP T)) n)
      ≳ₙ (fun _ => ((1 : ℚ) : ℝ)) := by
  have h := lic_provind_true (liaHistory (paperDP T)) (paperDP T)
    (fun n => tautFamily (succDeferral n)) (deferredTaut_codes succDeferral succDeferral_ruler)
    (fun m v _ => tautFamily_holds v (succDeferral m)) (paperDP_hworld T)
  have heq : (fun n => (literalIndicator (tautFamily (succDeferral n))).expect
      (liaHistory (paperDP T)) n) =
      fun n => liaHistory (paperDP T) n (tautFamily (succDeferral n)) := by
    funext n
    exact literalIndicator_expect _ _ _
  rw [heq]
  push_cast
  exact h.asympGE

/-- The same for the general-ruler form `Witness.expert_bound_transfer_witness`. -/
theorem ruler_witness_direct (f : DeferralFunction) (hf : UnaryRuler f.f) :
    (fun n => (literalIndicator (tautFamily (f n))).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun _ => ((1 : ℚ) : ℝ)) := by
  have h := lic_provind_true (liaHistory (paperDP T)) (paperDP T)
    (fun n => tautFamily (f n)) (deferredTaut_codes f hf)
    (fun m v _ => tautFamily_holds v (f m)) (paperDP_hworld T)
  have heq : (fun n => (literalIndicator (tautFamily (f n))).expect (liaHistory (paperDP T)) n) =
      fun n => liaHistory (paperDP T) n (tautFamily (f n)) := by
    funext n
    exact literalIndicator_expect _ _ _
  rw [heq]
  push_cast
  exact h.asympGE

end

end Cleanroom.Deference.DefLatticeArrows.AuditR2
