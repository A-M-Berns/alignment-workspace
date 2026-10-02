import Cleanroom.Info.InfoVoiLatents.VoiHarmMass

/-!
# Audit r3 (fidelity) probe — S2's harm-mass bound holds on the *whole* binary menu

`VoiHarmMass.voi_le_mul_harmMass_binary` (repair round 2) proves S2's "`VOI ≤ M·m_t(A)`" for the
binary execute-or-null menu `![a, v₀]` **with `a` prior-optimal**, through the regret-mass bound
(there D5's harm mass `μ{a < v₀}` is the regret mass of `a`). The ledger's Fidelity for it reads
"weaker: the binary menu `{a, ∅}` with `a` prior-optimal". The other case — the null action
prior-optimal — is not reachable by that route (the regret set of `v₀` is `{a > v₀}`, not
`{a < v₀}`), but the sentence still holds there, by a different argument:

`voi ≤ E_μ[max(a, v₀)] − E_μ[v₀] = E_μ[(a − v₀)⁺] = E_μ[a − v₀] + E_μ[(a − v₀)⁻] ≤ 0 + M·μ{a < v₀}`,

the first inequality because the perfect-information value dominates every decision rule, the
last because `E_μ[a] ≤ E_μ[v₀]` (the null action is prior-optimal) and `(a − v₀)⁻ ≤ M·𝟙[a < v₀]`.
So "where S2's sentence is true" is the binary menu, whichever of its two actions is
prior-optimal — the package's scoping can be widened by one clause.
-/

namespace Cleanroom.Info.InfoVoiLatents.AuditR3

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Info.InfoVoiLatents Cleanroom.Info.InfoVoiLatents.Voi

noncomputable section

variable {W S : Type} [Fintype W] [Fintype S]

open scoped Classical in
/-- D5's harm mass of the binary menu is the mass of `{a < v₀}`, for any nonnegative `μ`
(no prior-optimality needed). -/
theorem harmMass_binary_eq (μ : W → ℝ) (hμ : ∀ w, 0 ≤ μ w) (a v₀ : W → ℝ) :
    harmMass μ v₀ ![a, v₀] = ∑ w ∈ univ.filter (fun w => a w < v₀ w), μ w := by
  unfold harmMass
  rw [sup'_fin_two]
  have h1 : (univ.filter fun w => (![a, v₀] : Fin 2 → W → ℝ) 1 w < v₀ w) = ∅ := by
    ext w
    simp
  have h0 : (univ.filter fun w => (![a, v₀] : Fin 2 → W → ℝ) 0 w < v₀ w)
      = univ.filter fun w => a w < v₀ w := by
    ext w
    simp
  rw [h1, h0, Finset.sum_empty]
  exact max_eq_left (Finset.sum_nonneg fun w _ => hμ w)

/-- The Bayes value of the binary menu is at most the perfect-information value
`E_μ[max(a, v₀)]` (every decision rule is dominated pointwise). -/
theorem bayesValue_binary_le [DecidableEq S] {μ : W → ℝ} (hμ : ∀ w, 0 ≤ μ w) (k : Experiment W S)
    (a v₀ : W → ℝ) :
    bayesValue μ k ![a, v₀] ≤ ∑ w, μ w * max (a w) (v₀ w) := by
  unfold bayesValue
  rw [Finset.sup'_le_iff]
  intro δ _
  refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ (hμ w)
  have hb : ∀ b : Fin 2, (![a, v₀] : Fin 2 → W → ℝ) b w ≤ max (a w) (v₀ w) := by
    intro b
    fin_cases b <;> simp [le_max_left, le_max_right]
  calc ∑ s, k.k w s * (![a, v₀] : Fin 2 → W → ℝ) (δ s) w
      ≤ ∑ s, k.k w s * max (a w) (v₀ w) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hb (δ s)) ((k.k_mem w).1 s)
    _ = max (a w) (v₀ w) := by rw [← Finset.sum_mul, (k.k_mem w).2, one_mul]

open scoped Classical in
/-- **S2's harm-mass bound on the binary menu with the null action prior-optimal**:
`voi ≤ M · harmMass` when `E_μ[v₀] = priorValue` and `|a − v₀| ≤ M`. Together with
`VoiHarmMass.voi_le_mul_harmMass_binary` (the `a`-prior-optimal case) this covers the whole binary
menu. -/
theorem voi_le_mul_harmMass_binary_null [DecidableEq S] {μ : W → ℝ} (hμ : μ ∈ stdSimplex ℝ W)
    (k : Experiment W S) (a v₀ : W → ℝ) {M : ℝ} (hM : ∀ w, |a w - v₀ w| ≤ M)
    (hstar : E μ v₀ = priorValue μ ![a, v₀]) :
    voi μ k ![a, v₀] ≤ M * harmMass μ v₀ ![a, v₀] := by
  rw [harmMass_binary_eq μ hμ.1 a v₀]
  -- `a` is not better than the prior-optimal null action
  have hEa : E μ a ≤ E μ v₀ := by
    rw [hstar]
    have := Finset.le_sup' (fun b : Fin 2 => E μ ((![a, v₀] : Fin 2 → W → ℝ) b)) (mem_univ 0)
    simpa [priorValue] using this
  -- `E[max(a, v₀)] ≤ E[a] + M·μ{a < v₀}`
  have hsum : ∑ w, μ w * max (a w) (v₀ w)
      ≤ E μ a + M * ∑ w ∈ univ.filter (fun w => a w < v₀ w), μ w := by
    rw [Finset.mul_sum, Finset.sum_filter]
    unfold E
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w _ => ?_
    have h := abs_le.1 (hM w)
    split_ifs with h'
    · rw [max_eq_right h'.le]
      have : 0 ≤ μ w * (a w - v₀ w + M) := mul_nonneg (hμ.1 w) (by linarith [h.1])
      nlinarith [this]
    · push Not at h'
      rw [max_eq_left h']
      simp
  unfold voi
  rw [← hstar]
  have hbv := bayesValue_binary_le hμ.1 k a v₀
  linarith [hbv, hsum, hEa]

end

end Cleanroom.Info.InfoVoiLatents.AuditR3
