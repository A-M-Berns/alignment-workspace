import Cleanroom.Udt.UdtCondenseDd.WitnessLatent

/-!
# Audit r3 (adversarial) probe: `Xor` as a positive instance — the latent is a proper coarsening

Checks on the repair-round-2 positive instance `WitnessLatent.Xor` that its `nondegenerate` does not
state directly:

1. `polE_not_sub_E`: `E` is **not** a function of `Π̈` (so the pair latent is strictly coarser than
   the second given variable; together with the package's clause (4), strictly coarser than both).
2. `polE_not_sub_DIB`: `D_{I,B}` is not a function of `Π̈` (the package's clause (4) in `IsSubvariable`
   form).
3. `dI_not_sub_polE`: `Π̈` is not a function of the internal dynamic alone.
4. `E_not_sub_DIB`: `E` is not a function of `D_{I,B}` (the environment has its own randomness `j`),
   so DD's Markov clause is not the degenerate "E is determined by the dynamics".
5. `polS_ne_polE`: the structure's *chosen policy* field `Π*` (`polS`) is a constant policy that
   disagrees with the realized external policy `Π̈` — `AbstractDS` imposes no link between the two,
   and nothing in T9 reads `polS`. Recorded so the N+ grade is read as being about `Π̈`.

Not imported by the library.
-/

namespace Cleanroom.Udt.UdtCondenseDd.AuditR3

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust

theorem polE_not_sub_E : ¬ IsSubvariable Xor.absDS.polE Xor.absDS.E := by
  rw [Xor.polE_fun]
  decide +kernel

theorem polE_not_sub_DIB : ¬ IsSubvariable Xor.absDS.polE Xor.absDS.DIB := by
  rw [Xor.polE_fun]
  decide +kernel

theorem dI_not_sub_polE : ¬ IsSubvariable Xor.absDS.dI Xor.absDS.polE := by
  rw [Xor.polE_fun]
  decide +kernel

theorem E_not_sub_DIB : ¬ IsSubvariable Xor.absDS.DIB Xor.absDS.E := by
  decide +kernel

/-- `Π*` (the `polS` field) at world `(0, 0, 0)` and observation `1` returns action `0`, while
`Π̈` (the realized external policy, the identity at `k = 0`) returns `1`. -/
theorem polS_ne_polE :
    (Xor.absDS.polS (0, 0, 0) (0, 1)).2 ≠ Xor.absDS.polE (0, 0, 0) 1 := by
  rw [Xor.polE_eq]
  decide +kernel

end Cleanroom.Udt.UdtCondenseDd.AuditR3

#print axioms Cleanroom.Udt.UdtCondenseDd.AuditR3.polE_not_sub_E
#print axioms Cleanroom.Udt.UdtCondenseDd.AuditR3.E_not_sub_DIB
#print axioms Cleanroom.Udt.UdtCondenseDd.AuditR3.polS_ne_polE
