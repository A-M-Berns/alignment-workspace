import Cleanroom.Udt.UdtCondenseDd.WitnessLatent

/-!
# Audit r3 (fidelity) probe: the T9 refutation is robust to the note's own gloss of its latent model

[[topics/decision-determination]] line 99 glosses its sentence as: "if we view the agent-environment
interaction as a latent variable model where `D_{I,B}` is latent and `(E, Ö)` is observed, then `Π̈`
captures all of `D_{I,B}`'s contribution to `E`". The package's reading of record makes `D_{I,B}` a
*given* variable (RVM `(D_{I,B}, E)`, pair latent `Π̈`) and states robustness only for readings
where `Π̈` is a latent `Y_A` with `E`'s index in `A`. Under the note's gloss the observed
coordinates are `E` and `Ö` (and `E = (Ä, Ö)`), so `Π̈` could sit as a latent above `Ö` alone or
`Ä` alone; Corollary 4.6 then forces `Π̈ ⊑ Ö` or `Π̈ ⊑ Ä`. This probe records that both fail on
`Three` (as `Π̈ ⊑ E` does, `Three.not_isSubvariable`), so the refutation covers every latent
placement of `Π̈` above any observed coordinate. Not imported by the library.
-/

namespace Cleanroom.Udt.UdtCondenseDd.AuditR3

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust

/-- On `Three`, `Π̈` is not a function of the external observation `Ö = j` alone. -/
theorem three_polE_not_sub_oE : ¬ IsSubvariable Three.absDS.oE Three.absDS.polE := by
  rw [Three.polE_fun]
  decide +kernel

/-- On `Three`, `Π̈` is not a function of the external action `Ä` alone. -/
theorem three_polE_not_sub_aE : ¬ IsSubvariable Three.absDS.aE Three.absDS.polE := by
  rw [Three.polE_fun]
  decide +kernel

/-- On `Three`, `Π̈` is not a function of the environment dynamic `D_E` alone. -/
theorem three_polE_not_sub_dE : ¬ IsSubvariable Three.absDS.dE Three.absDS.polE := by
  rw [Three.polE_fun]
  decide +kernel

end Cleanroom.Udt.UdtCondenseDd.AuditR3
