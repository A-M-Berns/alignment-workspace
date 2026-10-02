import Cleanroom.Udt.UdtCommTrust.WitnessDet

/-!
# Audit r2 (adversarial) probe: nothing in `Construct.lean` requires the side-channel value to be
neutral

Not imported by the library. `ConcreteDS.Neutral` is defined and instantiated once (`W2m.neutral`)
and never appears in a hypothesis. So `polSC c₀`, `withPolSC c₀`, (i) `polSC_sub_DIB`, (ii)
`polD_eq_polSC_of_oC`, (iii) `polD_eq_polSC_of_modProb_zero` and `withPolSC_hlink` all accept a
*forcing* side-channel value, for which `Π*_c` is "the effective policy under forcing", not the
paper's "what would run if unmodified". On `W2m` the value `1` forces action `0`
(`p _ 1 = some 0`); the structure `withPolSC 1` typechecks and satisfies T7's hypothesis.
-/

namespace Cleanroom.Udt.UdtCommTrust.AuditR2

open Cleanroom.Udt.UdtPolicyCalc

/-- `1` is not a neutral side-channel value on `W2m`: it forces action `0` at the only instance. -/
theorem W2m_one_not_neutral : ¬ W2m.S.Neutral 1 := by
  intro h
  have := h 0
  simp [W2m.S] at this

/-- Nevertheless the construction with `c₀ = 1` is a `ConcreteDS` whose "chosen policy" is a
subvariable of `D_{I,B}` — (i) does not see neutrality. -/
theorem withPolSC_forcing_polS_sub :
    IsSubvariable (W2m.S.withPolSC 1).DIB (W2m.S.withPolSC 1).polS :=
  W2m.S.withPolSC_polS_sub 1

/-- Nor does (ii)'s exact form: at the worlds whose side channel is the forcing value `1`, the
effective policy equals the "chosen" one by `neutralize_spec` alone. -/
theorem polD_eq_polSC_forcing {ω : W2m.Ω} (hc : W2m.S.oC ω = 1) :
    W2m.S.polD ω (W2m.S.O ω) = W2m.S.polSC 1 ω (W2m.S.O ω) :=
  W2m.S.polD_eq_polSC_of_oC W2m.semChanSplit hc

end Cleanroom.Udt.UdtCommTrust.AuditR2
