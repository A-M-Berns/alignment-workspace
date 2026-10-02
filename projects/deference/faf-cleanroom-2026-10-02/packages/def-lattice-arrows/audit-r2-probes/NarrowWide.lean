import Cleanroom.Deference.DefLatticeArrows.WideBand

/-!
# Audit r2 (adversarial) probe: how much of `BandReflectionWithin c` is still the wide band?

`Partition.lean` states the predicate-level partition arrows from `BandReflectionWithin P DP E c`
(bands of half-width `ε ≤ c·δ`) and certifies, via `bandWt_ne_rampAbove_of_narrow`, that no
band of the predicate is the ramp at any threshold `v < 1 − 2cδ`. The probe asks the
complementary question: for which thresholds does the *narrow* predicate still contain the
soft Total-Trust face directly, with no `BandQuotesAvailable`, no grid and no partition?

Answer (proved below): for every `v` with `1 + δ ≤ v + 2cδ`, i.e. `v ≥ 1 − (2c − 1)δ` — the
band of the largest permitted half-width `ε = cδ` centred at `v + cδ` is the ramp there. So
the region where the partition is what proves the face is `v < 1 − (2c − 1)δ`, and the
package's `v < 1 − 2cδ` is `δ` short of sharp (in the safe direction). Below the ramp the
mirror statement holds for `v ≤ (2c − 1)δ`. Not imported by the library.
-/

namespace Cleanroom.Deference.DefLatticeArrows.AuditR2

open LogicalInduction Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows

variable {P : History} {DP : DeductiveProcess}

/-- The narrow predicate still gives the above face directly wherever `1 + δ ≤ v + 2cδ`. -/
theorem softTotalTrustAbove_of_bandReflectionWithin_wide {E : Expert DP} {c : ℚ}
    (hB : BandReflectionWithin P DP E c) {v δ : ℚ} (hδ : 0 < δ) (hc : 0 < c)
    (hwide : (1 : ℚ) + δ ≤ v + 2 * (c * δ)) :
    SoftTotalTrustAbove P DP E v δ := by
  intro X W XW hX q
  have hε : (0 : ℚ) < c * δ := mul_pos hc hδ
  have hface := (hB (v + c * δ) (c * δ) δ hε le_rfl hδ).1 X W XW hX
    (WeightQuote.toWideBand hδ hwide q)
  have hs : (v + c * δ - c * δ : ℚ) = v := by ring
  simp only [hs] at hface
  exact hface

/-- The mirror: the below face directly wherever `v − 2cδ + δ ≤ 0`. -/
theorem softTotalTrustBelow_of_bandReflectionWithin_wide {E : Expert DP} {c : ℚ}
    (hB : BandReflectionWithin P DP E c) {v δ : ℚ} (hδ : 0 < δ) (hc : 0 < c)
    (hwide : v - 2 * (c * δ) + δ ≤ 0) :
    SoftTotalTrustBelow P DP E v δ := by
  intro X W XW hX q
  have hε : (0 : ℚ) < c * δ := mul_pos hc hδ
  have hface := (hB (v - c * δ) (c * δ) δ hε le_rfl hδ).2 X W XW hX
    (WeightQuote.toWideBandBelow hδ hwide q)
  have hs : (v - c * δ + c * δ : ℚ) = v := by ring
  simp only [hs] at hface
  exact hface

/-- Sanity: at `c = 1` the free region above is exactly `v ≥ 1 − δ`, so at `δ = 1/10` the
faces at thresholds `v ≥ 9/10` need no partition even from the narrowest useful predicate. -/
example {E : Expert DP} (hB : BandReflectionWithin P DP E 1) :
    SoftTotalTrustAbove P DP E (9 / 10) (1 / 10) :=
  softTotalTrustAbove_of_bandReflectionWithin_wide hB (by norm_num) (by norm_num) (by norm_num)

end Cleanroom.Deference.DefLatticeArrows.AuditR2
