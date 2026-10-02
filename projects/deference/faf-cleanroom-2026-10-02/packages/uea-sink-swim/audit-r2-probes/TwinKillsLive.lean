import Cleanroom.Uea.UeaSinkSwim.Twin

/-!
# Probe (audit r2, fidelity): `Twin.twin_kills_good` on the two regimes of `(b, c, δ)`

`twin_kills_good` says: for every `(b, c, δ)` there is `ρ ∈ [0, 1)` with `s = 1` such that the trap is a twin fixed
point and the good point is not. It does not say the good point *was* a fixed point before the twin, and its proof
takes `ρ = 0` when `c > 2b(1-δ)`. This probe separates the two regimes:

* `twin_kills_live`: when the good point is alive without the twin (`c ≤ b(1-δ)`, i.e. a plain fixed point of
  `sos ⟨b, c, δ, 1⟩` by `good_isPlainFP_iff`), the twin with `ρ := 1 - c/(2b(1-δ)) ≥ 1/2` kills it — the content
  the name promises, with the twin's share bounded away from `0`.
* `good_dead_without_twin`: when `c > b(1-δ)` the good point is not a plain fixed point of `sos ⟨b, c, δ, 1⟩` at all,
  so there `twin_kills_good` asserts nothing about the twin (it is satisfiable with `ρ = 0`).

Not imported by the library. Elaborated with `scripts/lean-check`.
-/

namespace Cleanroom.Uea.UeaSinkSwim.Twin

open Cleanroom.Uea.UeaColeShadow Cleanroom.Uea.UeaColeShadow.SinkOrSwim

/-- The sink-or-swim parameters of `P` with `s := 1`. -/
noncomputable def atOne (P : Params) : Params :=
  ⟨P.b, P.c, P.δ, 1, P.hc, P.hcb, P.hb, P.hδ, P.hδ1, zero_le_one, le_rfl⟩

/-- **Live regime**: if the good point is a plain fixed point of `sos` at `s = 1` (`c ≤ b(1-δ)`), then the twin with
`ρ = 1 - c/(2b(1-δ)) ∈ [1/2, 1)` makes the trap a twin fixed point and the good point not one. -/
theorem twin_kills_live (P : Params) (hlive : P.c ≤ P.b * (1 - P.δ)) :
    (sos (atOne P)).IsPlainFP TheoremA.good ∧
    ∃ (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1), 1 / 2 ≤ ρ ∧
      IsTwinFP ⟨atOne P, ρ, hρ0, hρ1⟩ trap ∧ ¬ IsTwinFP ⟨atOne P, ρ, hρ0, hρ1⟩ TheoremA.good := by
  have hb := TheoremA.b_pos P
  have hc := P.hc; have hδ := P.hδ; have hδ1 := P.hδ1
  have h1δ : 0 < 1 - P.δ := by linarith
  have hden : 0 < 2 * P.b * (1 - P.δ) := by positivity
  refine ⟨?_, ?_⟩
  · rw [TheoremA.good_isPlainFP_iff]
    show P.c ≤ P.b * (1 - P.δ * 1)
    simpa using hlive
  · have hfrac_le : P.c / (2 * P.b * (1 - P.δ)) ≤ 1 / 2 := by
      rw [div_le_iff₀ hden]; nlinarith
    have hfrac_pos : 0 < P.c / (2 * P.b * (1 - P.δ)) := by positivity
    refine ⟨1 - P.c / (2 * P.b * (1 - P.δ)), by linarith, by linarith, by linarith, ?_, ?_⟩
    · exact (trap_twinFP_iff _).2.2 (by show P.b * (1 - 1) ≤ P.c; simp; exact hc.le)
    · rw [(good_twinFP_iff _).2]
      show ¬ P.c ≤ P.b * ((1 - P.δ) * (1 - (1 - P.c / (2 * P.b * (1 - P.δ)))) + P.δ * (1 - 1))
      have hkey : P.b * ((1 - P.δ) * (1 - (1 - P.c / (2 * P.b * (1 - P.δ)))) + P.δ * (1 - 1)) = P.c / 2 := by
        field_simp
        ring
      rw [hkey]
      linarith

/-- **Dead regime**: if `c > b(1-δ)` the good point is not a plain fixed point of `sos` at `s = 1` even without a twin
(`ρ = 0`), so on these parameters `twin_kills_good` has nothing to kill. -/
theorem good_dead_without_twin (P : Params) (hdead : P.b * (1 - P.δ) < P.c) :
    ¬ (sos (atOne P)).IsPlainFP TheoremA.good := by
  rw [TheoremA.good_isPlainFP_iff]
  show ¬ P.c ≤ P.b * (1 - P.δ * 1)
  simp
  exact hdead

end Cleanroom.Uea.UeaSinkSwim.Twin
