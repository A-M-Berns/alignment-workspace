import Cleanroom.Uea.UeaSelfGame.T3Family
import Cleanroom.Uea.UeaSelfGame.Attainment

/-!
# Audit round 3 (adversarial) probe: the "exact, unattained supremum" sentence as one statement

The ledger, `Attainment.lean` and `T3Family.lean` say that `T3Family.sup_limit` together with
`Attainment.theoremC_strict` makes `δ/(1−δ)` the exact, unattained supremum of the gap on `δ ≤ 1/2`.
This probe composes the two: for every `δ ∈ (0, 1/2]` and `ε > 0` there is a pure fixed point with the
trust bound everywhere whose gap lies in `[δ/(1−δ) − ε, δ/(1−δ))`. The strict upper bound needs a
situation to apply `theoremC_strict` at; when `sup_limit`'s witness has `n = 0` (which it never does, but
the existential does not say so) the gap is `0 < δ/(1−δ)` anyway. Not imported by the library.
-/

namespace Cleanroom.Uea.UeaSelfGame.AuditR3

theorem sup_limit_strict (δ : ℝ) (h0 : 0 < δ) (hhalf : δ ≤ 1 / 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (G : Game (Fin n) (Fin 2)) (π : Fin n → Fin 2), G.δ = δ ∧ G.IsPureFP π ∧
      (∀ s, G.TB (G.muSelf π) s) ∧ δ / (1 - δ) - ε ≤ G.Ustar - G.U π ∧
      G.Ustar - G.U π < δ / (1 - δ) := by
  obtain ⟨n, G, π, hδ, hfp, htb, hgap⟩ := T3Family.sup_limit δ h0 hhalf ε hε
  refine ⟨n, G, π, hδ, hfp, htb, hgap, ?_⟩
  have hpos : 0 < δ / (1 - δ) := div_pos h0 (by linarith)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- no situations: every policy is `π*`, the gap is `0`
    subst hn
    have : π = G.piStar := funext fun i => Fin.elim0 i
    rw [this]
    unfold Game.Ustar
    linarith
  · have hGδ : 0 < G.δ := by rw [hδ]; exact h0
    have := G.theoremC_strict hGδ π hfp ⟨0, hn⟩ (htb ⟨0, hn⟩)
    rw [hδ] at this
    linarith

end Cleanroom.Uea.UeaSelfGame.AuditR3
