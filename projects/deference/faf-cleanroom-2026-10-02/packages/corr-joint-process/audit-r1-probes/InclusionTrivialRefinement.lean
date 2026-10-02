import Cleanroom.Corrigibility.CorrJointProcess.Cellwise

/-!
# `corr-joint-process` · audit r1 (adversarial) probe: T3 at the degenerate refinement

Not imported by the library.

`Cellwise.inclusion_cellwise` holds for every overseer partition `f` refining the agent's cells.
The degenerate end is `f = Prod.snd` (the overseers see exactly the agent's cell and nothing
more): then the derived sensor presses on a cell iff the cell's own expectation of `X` is negative
— i.e. exactly where the agent would stop on its own — and cellwise (i) is automatic because the
press coincides with the agent's decision. This probe instantiates the theorem there and records
the cell sum in that case: `Z_i = min(m_i, 0)` where `m_i` is the cell's expectation of `X`. It
confirms the theorem's content is the *definition* of the derived sensor (Pattern B), which is
what Prop. 1′ claims ("information inclusion makes cellwise (i) automatic"), not a hidden squeeze.
-/

namespace Cleanroom.Corrigibility.CorrJointProcess.AuditR1Adversarial

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

variable {Θ Y : Type} [Fintype Θ] [Fintype Y] [DecidableEq Y]
variable (P : Distr (Θ × Y)) (wrong : Θ → Bool) (c h : ℝ)

/-- T3 at the trivial refinement: overseers who see only the agent's cell. -/
theorem inclusion_cellwise_trivial (i : Y) :
    (inclusionRound P wrong c h Prod.snd).cellwiseBelowThreshold i :=
  inclusion_cellwise P wrong c h Prod.snd id (fun _ => rfl) i

/-- At the trivial refinement the cell sum is `min(m_i, 0)`: the press is the agent's own stop
decision on the cell. -/
theorem inclusion_cellPressSum_trivial (i : Y) :
    (inclusionRound P wrong c h Prod.snd).cellPressSum i =
      if ruleSum P wrong c h Prod.snd i < 0 then ruleSum P wrong c h Prod.snd i else 0 := by
  rw [inclusion_cellPressSum P wrong c h Prod.snd id (fun _ => rfl) i]
  simp only [id]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · intro hi; exact absurd (mem_univ i) hi

end Cleanroom.Corrigibility.CorrJointProcess.AuditR1Adversarial
