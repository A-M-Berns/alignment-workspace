import Cleanroom.Udt.UdtCommTrust.Concrete

/-!
# `Cleanroom.Udt.UdtCtExamples.Infra`: reading `Π†` off a witness

Work package `udt-ct-examples`, infrastructure. `udt-comm-trust`'s `polE_eq_of` is the witnesses'
route past the `Classical.choose` in `Π̈`; the T4/T7 witnesses of this package need the same for
the effective policy `Π†`, whose value at an input `o` is the action taken at the world with
boundary `(o, D_B(ω))`. `polD_eq_of` gives it under three decidable hypotheses (agreement at the
realized input, dependence only through `D_B`, and every input realized alongside every value
of `D_B`).
-/

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

variable {Ω OI OE AI AE DI DE DB OH OC : Type} [Fintype Ω]

/-- **A computable description of `Π†`**: if `f` agrees with `A` at each world's own observation,
depends on the world only through `D_B`, and every observation is realized alongside every value
of `D_B`, then `Π† = f`. Mirror of `AbstractDS.polE_eq_of`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polD_eq_of (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)
    (f : Ω → Policy (OI × OE) (AI × AE)) (hf : ∀ ω, f ω (S.O ω) = S.A ω)
    (hD : ∀ ω ω', S.dB ω = S.dB ω' → f ω = f ω')
    (hs : ∀ ω o, ∃ ω', S.dB ω' = S.dB ω ∧ S.O ω' = o) (ω : Ω) : S.polD ω = f ω := by
  funext o
  obtain ⟨ω', h1, h2⟩ := hs ω o
  have : S.polD ω o = S.polD ω' (S.O ω') := by
    unfold AbstractDS.polD
    rw [← h2, h1]
  rw [this, S.polD_apply_O, ← hf ω', h2, hD ω ω' h1.symm]

end Cleanroom.Udt.UdtCtExamples
