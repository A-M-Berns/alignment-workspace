import Cleanroom.Lit.LitWeathersonFrames.Composite

/-!
Audit round 1, adversarial lens — probe for finding F-T4's scope.

The abstract's second clause is "Value can hold without Total Trust (when the option set is
**finite** …)". The package refutes it through `value_imp_totalTrust : ValueBdd → TotalTrustC`
(all menus) and `valueFinInt_imp_totalTrustInt` (finite menus, integrable options); the literal
reading — Value for *finite menus of bounded options* implies Total Trust — is the weaker
predicate `ValueFinBdd` of `Composite.lean`, and the same two-option proof gives it. This probe
states that reading, so F-T4 covers the abstract's clause exactly as worded. Not imported by the
library.
-/

namespace Cleanroom.Lit.LitWeathersonFrames.AuditR1Adv

open Cleanroom.Lit.LitWeathersonFrames

variable {W : Type}

/-- Value on finite menus of uniformly bounded options already implies product-form Total Trust
(the two-option menu is finite). -/
theorem valueFinBdd_imp_totalTrustC {π : W → ℝ} (hπ : IsDist π) {F : CFrame W}
    (hV : ValueFinBdd π F) : TotalTrustC π F := by
  intro X hX t
  have hbdd : BddFam (twoMenu X t) := by
    obtain ⟨M, hM⟩ := hX
    refine ⟨max M |t|, fun b w => ?_⟩
    cases b
    · simp [twoMenu]
    · simp only [twoMenu, ↓reduceIte]; exact le_trans (hM w) (le_max_left _ _)
  have := hV Bool (twoMenu X t) hbdd (twoStrat F X t) (twoStrat_recommended F X t) false
  rw [totalTrust_sum_eq_twoStrat hπ F (hX.integrableW hπ) t]
  have hc : Eℕ π (twoMenu X t false) = t := Eℕ_const hπ t
  rw [hc] at this
  linarith

end Cleanroom.Lit.LitWeathersonFrames.AuditR1Adv
