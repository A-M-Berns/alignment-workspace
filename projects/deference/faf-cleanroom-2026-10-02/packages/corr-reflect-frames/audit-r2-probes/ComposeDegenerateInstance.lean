import Cleanroom.Corrigibility.CorrReflectFrames.Compose

/-!
Audit r2 (adversarial) probe — the degenerate inhabitants of `legitimizingVal_compose`'s
hypothesis package (T7, load-bearing).

At `L₁₂ = ∅` the restricted deferrer is `0`, so step one (`Reflects (restrict π ∅) F₂`) and step
two (over the empty candidate set) hold for *every* pair of frames and every `φ`, `L₂₃`, and the
conclusion is the vacuous `legitimizingVal_empty`. This records that the theorem says nothing at
a `π`-null `L₁₂`, as expected (the definition is vacuous on null events), and that the positive
witness `compose_positive_witness` (proper `L₁₂ = {X₁ = 1}`) is the one that exercises it.
Nothing here is imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames.AuditR2

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames

variable {W : Type} [Fintype W] [DecidableEq W]

theorem restrict_empty (π : W → ℝ) : restrict π ∅ = fun _ => 0 := by
  funext w; simp [restrict, ind]

theorem cands_restrict_empty (π : W → ℝ) (F : Frame W) : F.cands (restrict π ∅) = ∅ := by
  ext ρ
  simp only [Frame.mem_cands, restrict_empty, notMem_empty, iff_false, not_exists, not_and]
  intro w h; exact absurd h (lt_irrefl 0)

/-- Both hypotheses of `legitimizingVal_compose` hold at `L₁₂ = ∅` for every `F₂ F₃ φ L₂₃`. -/
theorem compose_hyps_at_empty (π : W → ℝ) (F₂ F₃ : Frame W) (φ L₂₃ : Finset W) :
    Reflects (restrict π ∅) F₂ ∧
      ∀ ρ ∈ F₂.cands (restrict π ∅), LegitimizingVal ρ F₃ φ L₂₃ := by
  constructor
  · intro ρ hρ
    rw [cands_restrict_empty] at hρ
    exact absurd hρ (notMem_empty ρ)
  · intro ρ hρ
    rw [cands_restrict_empty] at hρ
    exact absurd hρ (notMem_empty ρ)

/-- … and the conclusion there is the vacuous empty-event legitimacy. -/
theorem compose_concl_at_empty (π : W → ℝ) (F₃ : Frame W) (φ L₂₃ : Finset W) :
    LegitimizingVal π F₃ φ (∅ ∩ L₂₃) := by
  rw [empty_inter]; exact legitimizingVal_empty φ

end Cleanroom.Corrigibility.CorrReflectFrames.AuditR2
