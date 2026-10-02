import Cleanroom.Udt.UdtEndorsePolicy.Flat

/-!
# Audit r2 (adversarial) probe: `RespectsPairs` is pairwise — a three-way interaction respects
no graph, even the complete one

The ledger's Fidelity column for `cellwise_optimal_of_flat` and the `RespectsPairs` docstring say
"pairwise (not clique) coupling: a three-way interaction respects no graph, even the complete one".
That is a mathematical claim with no Lean behind it. Checked here: the parity utility
`xor3 π = [π 0 + π 1 + π 2 = 1]` on `Fin 3 → Fin 2` is not `RespectsPairs (fun _ _ => True)`.
Proof: the alternating sum `∑_π (−1)^{|π|} U π` is `−4` for `xor3` and `0` for every pair term
(the free coordinate cancels), so no pair decomposition exists; `linarith` finds the combination
from the eight instances. Not imported by the library.
-/

namespace Cleanroom.Udt.UdtEndorsePolicy.AuditR2

open Cleanroom.Udt.UdtPolicyCalc Finset

/-- The three-way parity interaction on three binary nodes. -/
def xor3 (π : Policy (Fin 3) (Fin 2)) : ℝ := if π 0 + π 1 + π 2 = 1 then 1 else 0

/-- `xor3` respects no coupling graph, not even the complete one: the pairwise form is strictly
weaker than "every clique of `G` may carry an interaction". -/
theorem xor3_not_respectsPairs_top : ¬ RespectsPairs (fun _ _ => True) xor3 := by
  rintro ⟨f, -, hU⟩
  have h000 := hU ![0, 0, 0]
  have h001 := hU ![0, 0, 1]
  have h010 := hU ![0, 1, 0]
  have h011 := hU ![0, 1, 1]
  have h100 := hU ![1, 0, 0]
  have h101 := hU ![1, 0, 1]
  have h110 := hU ![1, 1, 0]
  have h111 := hU ![1, 1, 1]
  simp +decide only [xor3, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, if_true, if_false]
    at h000 h001 h010 h011 h100 h101 h110 h111
  linarith

end Cleanroom.Udt.UdtEndorsePolicy.AuditR2

#print axioms Cleanroom.Udt.UdtEndorsePolicy.AuditR2.xor3_not_respectsPairs_top
