import Cleanroom.Uea.UeaSelfGame.Witness8801

/-!
# Audit round 3 (adversarial) probe: `exists_isFlooredFPext`'s witness, made explicit

The ledger's row for `exists_isFPext`/`exists_isFlooredFPext` names `Witness8801.witness` as the N+
witness of both, but `Witness8801` ships a *plain* extension fixed point with the trust bound everywhere
and no floored-fixed-point statement. The missing step is general: a plain extension fixed point with
the extension trust bound at every situation is a floored extension fixed point (the residual is
nonnegative everywhere, and every supported action attains `maxF`). So the `√8801` fixed point is a
floored one too, on an instance with no pure fixed point of either kind — the floored existence theorem
has a non-degenerate witness. Not imported by the library.
-/

namespace Cleanroom.Uea.UeaSelfGame.AuditR3

open Game

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]

/-- A plain extension fixed point with the extension trust bound everywhere is a floored one. -/
theorem isFlooredFPext_of_isFPext_tb (G : Game S A) {σ : S → A → ℝ} (h : G.IsFPext σ)
    (htb : ∀ s, G.TBext σ s) : G.IsFlooredFPext σ := by
  refine ⟨h.1, fun s => ?_⟩
  obtain ⟨b, hb⟩ := htb s
  have hmax : G.thr ≤ G.maxF σ s := le_trans hb (G.Fext_le_maxF σ s b)
  have hattain : ∀ a, 0 < σ s a → G.Fext σ s a = G.maxF σ s := by
    intro a ha
    apply le_antisymm (G.Fext_le_maxF σ s a)
    obtain ⟨c, hc⟩ := G.exists_Fext_eq_maxF σ s
    rw [← hc]
    exact h.2 s a ha c
  refine ⟨fun hlt => ?_, fun _ a ha => hattain a ha, fun _ a ha => Or.inl (hattain a ha)⟩
  exfalso
  unfold Game.resid at hlt
  linarith

/-- The `√8801` fixed point is a floored extension fixed point of the §6 instance. -/
theorem witness8801_isFlooredFPext : Section6.game.IsFlooredFPext Witness8801.σ :=
  isFlooredFPext_of_isFPext_tb _ Witness8801.witness.1 Witness8801.witness.2.2.1

end Cleanroom.Uea.UeaSelfGame.AuditR3
