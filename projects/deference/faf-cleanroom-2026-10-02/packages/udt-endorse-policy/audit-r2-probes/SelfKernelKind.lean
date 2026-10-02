import Cleanroom.Udt.UdtEndorsePolicy.NodeValue

/-!
Audit r2 (fidelity) probe for `udt-endorse-policy`: the ledger grades
`edtAssembly_selfKernel_of_optimal` as Kind **P**. It is `udt-policy-calc`'s
`isLocalOptimum_of_isOptimal` (Kind T there) composed with the `Iff.rfl`
`edtAssembly_selfKernel_iff`, i.e. a Kind T/L fact. Not imported by the library.
-/

namespace Cleanroom.Udt.UdtEndorsePolicy

open Cleanroom.Udt.UdtPolicyCalc

/-- The same statement, proved by the two existing one-liners. -/
theorem probe_selfKernel_of_optimal_is_composition {S A : Type} [DecidableEq S]
    (U : Policy S A → ℝ) {π : Policy S A} (h : IsOptimal U π) :
    EdtAssembly U (selfKernel π) π :=
  (edtAssembly_selfKernel_iff U π).2 (isLocalOptimum_of_isOptimal h)

end Cleanroom.Udt.UdtEndorsePolicy
