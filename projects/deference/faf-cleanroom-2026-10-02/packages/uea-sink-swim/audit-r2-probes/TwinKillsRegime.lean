import Cleanroom.Uea.UeaSinkSwim.Twin

/-!
# Audit r2 (adversarial) probe for `uea-sink-swim`: where `Twin.twin_kills_good` needs a twin

`Twin.twin_kills_good (P)` is universal over `(b, c, δ)` and exhibits `ρ ∈ [0,1)` (with `s = 1`) such that the
trap is a twin fixed point and the good point is not. Its proof picks `ρ = 0` (no twin at all) whenever
`c > 2b(1-δ)`. This probe shows that in the whole regime `b(1-δ) < c` the good point is already dead at
`s = 1` with `ρ = 0` — `δ` alone kills it — so the theorem's name ("the twin kills the good point") describes
only the complementary regime `c ≤ b(1-δ)`, where the good point *is* a twin fixed point at `ρ = 0`
(`good_twinFP_noTwin_iff`) and a positive `ρ` is needed to remove it. The N+ witness `Twin.witness`
(`b = 1, c = 1/2, δ = 1/10`) sits in that genuine regime. Not imported by the library.
-/

namespace Cleanroom.Uea.UeaSinkSwim.AuditR2Adversarial

open Cleanroom.Uea.UeaColeShadow
open Cleanroom.Uea.UeaColeShadow.SinkOrSwim
open Twin

/-- The twin parameters at `s = 1` with twin share `ρ = 0`: no twin. -/
noncomputable def noTwin (P : Params) : TwinP :=
  ⟨⟨P.b, P.c, P.δ, 1, P.hc, P.hcb, P.hb, P.hδ, P.hδ1, zero_le_one, le_rfl⟩, 0, le_rfl, zero_lt_one⟩

/-- At `s = 1`, `ρ = 0`, the good point is a twin fixed point iff `c ≤ b(1-δ)`. -/
theorem good_twinFP_noTwin_iff (P : Params) :
    IsTwinFP (noTwin P) TheoremA.good ↔ P.c ≤ P.b * (1 - P.δ) := by
  rw [(good_twinFP_iff (noTwin P)).2]
  have h : (noTwin P).P.b * ((1 - (noTwin P).P.δ) * (1 - (noTwin P).ρ) + (noTwin P).P.δ * (1 - (noTwin P).P.s)) =
      P.b * (1 - P.δ) := by
    show P.b * ((1 - P.δ) * (1 - 0) + P.δ * (1 - 1)) = P.b * (1 - P.δ)
    ring
  rw [h]
  exact Iff.rfl

/-- At `s = 1`, `ρ = 0`, the trap is always a twin fixed point. -/
theorem trap_twinFP_noTwin (P : Params) : IsTwinFP (noTwin P) trap :=
  (trap_twinFP_iff (noTwin P)).2.2 (by show P.b * (1 - 1) ≤ P.c; linarith [P.hc])

/-- **In the regime `b(1-δ) < c` no twin is needed**: with `ρ = 0` the trap is a twin fixed point, the good point is
not, the honest self's posterior is `1 - δ`, and `(1-δ) < c/b` — every conjunct of `twin_kills_good`'s conclusion that
mentions the twin holds with the twin absent. -/
theorem twin_kills_good_without_twin (P : Params) (h : P.b * (1 - P.δ) < P.c) :
    IsTwinFP (noTwin P) trap ∧ ¬ IsTwinFP (noTwin P) TheoremA.good ∧
    (sos3 (noTwin P) 0 le_rfl zero_le_one).wS trap 0 island = (1 - P.δ) * (1 - 0) ∧
    (1 - P.δ) * (1 - 0) < P.c / P.b := by
  have hb := TheoremA.b_pos P
  refine ⟨trap_twinFP_noTwin P, ?_, wS3_island (noTwin P) 0 le_rfl zero_le_one trap, ?_⟩
  · rw [good_twinFP_noTwin_iff]; exact not_le.2 h
  · rw [sub_zero, mul_one, lt_div_iff₀ hb]; linarith

/-- **In the regime `c ≤ b(1-δ)` the twin is what kills**: the good point is a twin fixed point at `ρ = 0`, and the
`ρ` of `twin_kills_good` removes it. (The witness `b = 1, c = 1/2, δ = 1/10` is here: `1/2 ≤ 9/10`.) -/
theorem twin_needed (P : Params) (h : P.c ≤ P.b * (1 - P.δ)) :
    IsTwinFP (noTwin P) TheoremA.good ∧
    ∃ (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1),
      let Q : TwinP := ⟨⟨P.b, P.c, P.δ, 1, P.hc, P.hcb, P.hb, P.hδ, P.hδ1, zero_le_one, le_rfl⟩, ρ, hρ0, hρ1⟩
      ¬ IsTwinFP Q TheoremA.good := by
  refine ⟨(good_twinFP_noTwin_iff P).2 h, ?_⟩
  obtain ⟨ρ, hρ0, hρ1, hQ⟩ := twin_kills_good P
  exact ⟨ρ, hρ0, hρ1, hQ.2.1⟩

theorem witness_in_genuine_regime : (1 : ℝ) / 2 ≤ 1 * (1 - 1 / 10) := by norm_num

end Cleanroom.Uea.UeaSinkSwim.AuditR2Adversarial
