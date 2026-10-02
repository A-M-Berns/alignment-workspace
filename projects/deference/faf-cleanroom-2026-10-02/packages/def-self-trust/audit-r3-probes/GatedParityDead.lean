import Cleanroom.Deference.DefSelfTrust.Witness

/-!
# Audit probe (def-self-trust, round 3, adversarial): the product gate of `gatedSelfTrust_parity_instance` is `0` infinitely often

`Witness.lean` proves `gatedParity_gate_live` (the product gate
`Ind_{1/4}(E_{f n}(X_n) > 1/2) · parityGate (f n)` is `1` infinitely often) and *says* — in the
docstrings of `parityGate` and `gatedSelfTrust_parity_instance`, the module header, and the
ledger row of `gatedSelfTrust_productForm` — that it is `0` on all large odd days, with no Lean
statement behind that half. This file checks that the unproved half is true: the mirror of
`gatedParity_gate_live` from `estWitness_gate_dead`. So the gate of the shipped instance is
genuinely non-constant in both directions, as claimed. Not imported by the library.
-/

namespace Cleanroom.AuditProbe.DefSelfTrust.GatedParityDead

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc Cleanroom.Deference.DefSelfTrust
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- The product gate at `w := parityGate` is `0` infinitely often (it is the square of the
witness gate, which is `0` on all large odd days). -/
theorem gatedParity_gate_dead (f : DeferralFunction) (hinj : Function.Injective f.f) :
    ∃ᶠ n in atTop,
      ((gatedWeight T f (fun n => literalIndicator (parityFamily n)) (1 / 4) (1 / 2)
        (parityGate T f) (f n) : ℚ) : ℝ) = 0 := by
  refine (estWitness_gate_dead T f hinj).mono (fun n hn => ?_)
  unfold witnessGate at hn
  simp only [gatedWeight_at_cast T f hinj, parityGate, estWeight_at_cast T f hinj,
    literalIndicator_expect, hn]
  norm_num

end

end Cleanroom.AuditProbe.DefSelfTrust.GatedParityDead
