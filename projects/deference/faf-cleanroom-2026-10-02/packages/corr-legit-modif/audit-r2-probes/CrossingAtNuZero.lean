import Cleanroom.Corrigibility.CorrLegitModif.LearnAlpha

/-!
# Audit probe (corr-legit-modif, round 2, adversarial): `alphaHat_crossing` at `ν = 0`

`alphaHat_crossing` assumes `ν < 1` but not `0 < ν` (the repair dropped `0 < ν` as unused). At
`ν = 0` — no prior weight on the dull sensor — the estimate is `α₁` from the start, so the
crossing happens at `n = 0` whenever the sharp sensor crosses: "after finitely many self-assessed
false presses" is "after none". The hypothesis package therefore admits a degenerate corner; the
docstring's "intended range `0 < ν`" and the witness (`ν = 9/10`, least index `4`) keep the headline
out of it. Recorded, not blocking.
-/

namespace AuditProbe

open Cleanroom.Corrigibility.CorrLegitModif

theorem crosses_zero_at_nu_zero {ε β c h α₀ α₁ : ℝ} (hε : ε < 1)
    (hsharp : β * ε * h < α₁ * (1 - ε) * c) :
    Crosses ε β c h 0 α₀ α₁ 0 := by
  rw [crosses_iff_core hε]
  simp only [pow_zero, zero_mul, sub_zero, one_mul, mul_one, zero_add]
  linarith

end AuditProbe
