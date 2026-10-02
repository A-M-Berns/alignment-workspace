import Cleanroom.Corrigibility.CorrLegitModif.Capability

/-!
# Audit probe (corr-legit-modif, round 2, adversarial): `fails_beyond_level` at `ε = 0`

`fails_beyond_level` assumes `0 ≤ ε` and `0 ≤ β_H`. At `ε = 0` (or `β_H = 0`) the binding cell's
`W`-mass is `0` for every agent rate, so compliance fails for every `β_A` and the "level" the
theorem exhibits is vacuous (`b = 0`, and in fact every `b` works). The hypothesis package admits
this corner; `capability_instance` (`ε = 1/10`, `β_H = 9/10`, a crossing between `(3/10, 7/10)` and
`(1/10, 9/10)`) is outside it. Recorded, not blocking.
-/

namespace AuditProbe

open Cleanroom.Corrigibility.CorrLegitModif

theorem fails_everywhere_at_eps_zero {αH βH αA c h : ℝ} (hαH : 0 < αH) (hαA : αA < 1)
    (hc : 0 < c) (βA : ℝ) : ¬ Complies c h (bindW 0 βH βA) (bindR 0 αH αA) := by
  unfold Complies bindW bindR
  push Not
  nlinarith [mul_pos hc (mul_pos hαH (sub_pos.2 hαA))]

end AuditProbe
