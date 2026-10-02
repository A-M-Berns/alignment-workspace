import Cleanroom.Corrigibility.CorrTrajectory.ObsToy

/-!
# Audit r3 (adversarial), probe 2: `ObsToy.Updating.view` "updates on the revealed `W₀`" — but not by Bayes

The ledger and docstrings describe `Updating.view` as "an agent that updates on the revealed `W₀`". Its
round-0 law is the independent product `Bern(1/4) ⊗ Bern(1/4)`, whose Bayes conditional on `W₀ = 1`
gives `W₁ ~ Bern(1/4)` — not the `3/10` the round-1 law assigns (`bayes_update_quarter`). So the
round-1 law is *a law that depends on the revealed `W₀`*, not the Bayes update of the agent's own prior;
and the witness is not reflective at `(0, ·)`: `E_{P₀}[Ψ₁] = 21/80 ≠ 20/80 = E_{P₀}[R₁]`
(`not_uncondMart`). Neither affects the N+ grade — the certificate theorems' package is `Δ_t ≤ 0` and
observable losses, which hold — but "updates on" should read "whose round-1 law depends on"; a genuine
Bayes update of this prior would put `Ψ₁ = 1/4` on both atoms, i.e. the very degeneracy the section was
added to remove. (A correlated round-0 prior could give an honest-Bayes variant; not required.)
Non-blocking: presentation.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory.ObsToy.Updating

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect
open LossToy

/-- Conditioning the round-0 law on `W₀ = 1` gives `W₁` credence `1/4`; the round-1 law says `3/10`. -/
theorem bayes_update_quarter :
    (view.agentLaw 0 (true, true)).mass (true, true) /
        ((view.agentLaw 0 (true, true)).mass (true, true) + (view.agentLaw 0 (true, true)).mass (true, false)) =
      1 / 4 ∧
    (view.agentLaw 1 (true, true)).mass (true, true) = 3 / 10 := by
  constructor
  · rw [view_agentLaw_zero]; simp [bern2] <;> norm_num
  · rw [view_agentLaw_one_true (ω := (true, true)) rfl]; simp [bern2] <;> norm_num

/-- The updating witness is not reflective at round `0`: `E_{P₀}[Ψ₁] = 21/80 ≠ 1/4 = E_{P₀}[R₁]`. -/
theorem not_uncondMart (ω : Bool × Bool) : ¬ view.uncondMart 1 0 ω := by
  unfold AgentView.uncondMart
  rw [view_Psi_one, view_R_one_one, view_loss_one, view_agentLaw_zero, expect_bern2, expect_bern2]
  norm_num

end Cleanroom.Corrigibility.CorrTrajectory.ObsToy.Updating
