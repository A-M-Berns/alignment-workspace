import Cleanroom.Lit.LitWeathersonFrames.Composite

/-!
Audit r1 (fidelity) probe for `lit-weatherson-frames`. Not imported by the library.

Claim: the T4 argument already gives Value ⟹ Total Trust from the *weakest* Value predicate
of the package, `ValueFinBdd` (finite menus, uniformly bounded options) — the predicate the
abstract's "when the option set is finite" names — so the finding F-T4 can be stated at that
grade. The package states `ValueBdd → TotalTrustC` and `ValueFinInt → TotalTrustInt`; this is
the missing (strongest) corner, proved by the same two-option menu.
-/

namespace Cleanroom.Lit.LitWeathersonFrames

theorem probe_valueFinBdd_imp_totalTrustC {W : Type} {π : W → ℝ} (hπ : IsDist π) {F : CFrame W}
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

end Cleanroom.Lit.LitWeathersonFrames
