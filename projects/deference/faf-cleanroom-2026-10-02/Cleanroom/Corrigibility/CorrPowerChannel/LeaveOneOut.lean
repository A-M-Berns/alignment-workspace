import Cleanroom.Corrigibility.CorrPowerChannel.Hazard

/-!
# `corr-power-channel` — T11(a): the leave-one-out form of "which component carries"

For each detector `k`, `without_k M` is the model with detector `k` removed (`b_k = a_k = 0`), and
`Δ_k(λ) = margin_M(λ) − margin_{without k}(λ)` is the net contribution of detector `k` to the
margin. d1 S7's display

`Δ_k = (1 − q_k^{−k}) w_k b_k h_k − a_k [ w_∅ (1 − q_∅^{−k}) c₀ − ∑_{f≠k} w_f (1 − q_f^{−k}) h_f ]`

(with `q^{−k}` the press probabilities of the model without `k`, `w_θ = (1 − λ) p_θ`, `w_f = p_f`
otherwise, `w_∅ = p₀`) is proved as an exact identity for each of the four detectors
(`deltaθ_eq`, `deltaN_eq`, `deltaπ_eq`, `deltar_eq`), and the four signs at the worked
parameters, whole-line, `λ = 1`, are the exact rationals `Δ_θ = −894103/25000000`,
`Δ_N = 113107/25000000`, `Δ_π = 501809/25000000`, `Δ_r = −43643/25000000` (`delta_signs`):
`θ −`, `N +`, `π +`, `r −`.

Sources: d1-final.md S7 (l. 58), P9 (l. 94); corr-wf14b-040.
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel

noncomputable section

namespace HazardModel

variable (M : HazardModel)

/-- The model with the `θ`-detector removed. Source: d1-final.md S7 (l. 58, "`q^{−k}`"). Kind: D.
Fidelity: exact -/
def withoutθ : HazardModel := { M with bθ := 0, aθ := 0 }

/-- The model with the `N`-detector removed. Source: d1-final.md S7. Kind: D. Fidelity: exact -/
def withoutN : HazardModel := { M with bN := 0, aN := 0 }

/-- The model with the `π`-detector removed. Source: d1-final.md S7. Kind: D. Fidelity: exact -/
def withoutπ : HazardModel := { M with bπ := 0, aπ := 0 }

/-- The model with the `r`-detector removed. Source: d1-final.md S7. Kind: D. Fidelity: exact -/
def withoutr : HazardModel := { M with br := 0, ar := 0 }

/-- `Δ_θ(λ)`: the net contribution of the `θ`-detector to the margin.
Source: d1-final.md S7 (l. 58). Kind: D. Fidelity: exact -/
def deltaθ (l : ℝ) : ℝ := M.margin l - M.withoutθ.margin l

/-- `Δ_N(λ)`. Source: d1-final.md S7. Kind: D. Fidelity: exact -/
def deltaN (l : ℝ) : ℝ := M.margin l - M.withoutN.margin l

/-- `Δ_π(λ)`. Source: d1-final.md S7. Kind: D. Fidelity: exact -/
def deltaπ (l : ℝ) : ℝ := M.margin l - M.withoutπ.margin l

/-- `Δ_r(λ)`. Source: d1-final.md S7. Kind: D. Fidelity: exact -/
def deltar (l : ℝ) : ℝ := M.margin l - M.withoutr.margin l

/-- **S7's display for `k = θ`** (exact identity): `Δ_θ(λ) = (1 − q_θ^{−θ}) (1 − λ) p_θ b_θ h_θ −
a_θ [ p₀ (1 − α^{−θ}) c₀ − ∑_{f≠θ} p_f (1 − q_f^{−θ}) h_f ]`.
Source: d1-final.md S7 (l. 58), P9 (l. 94)
Kind: P
Fidelity: exact (at every `λ`; the source states `λ = 1`)
Hyps: (a) none -/
theorem deltaθ_eq (l : ℝ) :
    M.deltaθ l = (1 - M.withoutθ.qθ) * ((1 - l) * M.pθ) * M.bθ * M.hθ -
      M.aθ * (M.p₀ * (1 - M.withoutθ.α) * M.c₀ -
        (M.pN * (1 - M.withoutθ.qN) * M.hN + M.pπ * (1 - M.withoutθ.qπ) * M.hπ +
          M.pr * (1 - M.withoutθ.qr) * M.hr)) := by
  simp only [deltaθ, withoutθ, margin, H, F, p₀, α, qθ, qN, qπ, qr]
  ring

/-- **S7's display for `k = N`.**
Source: d1-final.md S7 (l. 58), P9 (l. 94)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem deltaN_eq (l : ℝ) :
    M.deltaN l = (1 - M.withoutN.qN) * M.pN * M.bN * M.hN -
      M.aN * (M.p₀ * (1 - M.withoutN.α) * M.c₀ -
        (((1 - l) * M.pθ) * (1 - M.withoutN.qθ) * M.hθ + M.pπ * (1 - M.withoutN.qπ) * M.hπ +
          M.pr * (1 - M.withoutN.qr) * M.hr)) := by
  simp only [deltaN, withoutN, margin, H, F, p₀, α, qθ, qN, qπ, qr]
  ring

/-- **S7's display for `k = π`.**
Source: d1-final.md S7 (l. 58), P9 (l. 94)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem deltaπ_eq (l : ℝ) :
    M.deltaπ l = (1 - M.withoutπ.qπ) * M.pπ * M.bπ * M.hπ -
      M.aπ * (M.p₀ * (1 - M.withoutπ.α) * M.c₀ -
        (((1 - l) * M.pθ) * (1 - M.withoutπ.qθ) * M.hθ + M.pN * (1 - M.withoutπ.qN) * M.hN +
          M.pr * (1 - M.withoutπ.qr) * M.hr)) := by
  simp only [deltaπ, withoutπ, margin, H, F, p₀, α, qθ, qN, qπ, qr]
  ring

/-- **S7's display for `k = r`.**
Source: d1-final.md S7 (l. 58), P9 (l. 94)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem deltar_eq (l : ℝ) :
    M.deltar l = (1 - M.withoutr.qr) * M.pr * M.br * M.hr -
      M.ar * (M.p₀ * (1 - M.withoutr.α) * M.c₀ -
        (((1 - l) * M.pθ) * (1 - M.withoutr.qθ) * M.hθ + M.pN * (1 - M.withoutr.qN) * M.hN +
          M.pπ * (1 - M.withoutr.qπ) * M.hπ)) := by
  simp only [deltar, withoutr, margin, H, F, p₀, α, qθ, qN, qπ, qr]
  ring

end HazardModel

/-- **The four signs at the worked parameters (N+ for the model)**, whole-line, `λ = 1`:
`Δ_θ = −894103/25000000 < 0`, `Δ_N = 113107/25000000 > 0`, `Δ_π = 501809/25000000 > 0`,
`Δ_r = −43643/25000000 < 0` — the humans' `r`-detector is a net cost at these parameters (the
adversary's A25, sharpened), as the source says. Exact rationals (rule 4).
Source: d1-final.md S7 (l. 58, "`Δ_θ = −0.0358`, `Δ_N = +0.0045`, `Δ_π = +0.0201`,
`Δ_r = −0.0018`"), P9 (l. 94)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem delta_signs :
    (wholeLine (1 / 20)).deltaθ 1 = -(894103 / 25000000) ∧
      (wholeLine (1 / 20)).deltaN 1 = 113107 / 25000000 ∧
      (wholeLine (1 / 20)).deltaπ 1 = 501809 / 25000000 ∧
      (wholeLine (1 / 20)).deltar 1 = -(43643 / 25000000) := by
  simp only [HazardModel.deltaθ, HazardModel.deltaN, HazardModel.deltaπ, HazardModel.deltar,
    HazardModel.withoutθ, HazardModel.withoutN, HazardModel.withoutπ, HazardModel.withoutr,
    wholeLine, worked, HazardModel.margin, HazardModel.H, HazardModel.F, HazardModel.p₀,
    HazardModel.α, HazardModel.qθ, HazardModel.qN, HazardModel.qπ, HazardModel.qr]
  norm_num

end

end Cleanroom.Corrigibility.CorrPowerChannel
