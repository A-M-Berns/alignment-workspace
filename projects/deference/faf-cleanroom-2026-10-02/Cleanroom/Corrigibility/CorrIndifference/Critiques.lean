import Cleanroom.Corrigibility.CorrIndifference.Estimators
import Cleanroom.Found.CorrThreeStep.TwoState

/-!
# Stretch items with short proofs: S13 (the convexity theorem), S9 (Good's theorem for
refinements on D-5; the two-state mixture identity)

Source: [[corr-refs-inventory]] 021 (the convexity remark); [[corr-wf13-inventory]] 046
(armstrong.md I6.2), 047 (armstrong.md I13.2).
-/

namespace Cleanroom.Corrigibility.CorrIndifference.Critiques

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep Estimators

set_option linter.unusedSectionVars false

/-! ## S13. The convexity theorem -/

/-- **`p ↦ max_a (p · v_a + (1 − p) · w_a)` is convex** (the maximum of affine functions), stated
directly: for `t ∈ [0, 1]`, `f(t p₁ + (1 − t) p₂) ≤ t f(p₁) + (1 − t) f(p₂)`.
Source: [[corr-refs-inventory]] 021 (the convexity remark)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem sup_affine_convex {A : Type*} [Fintype A] [Nonempty A] (v w : A → ℝ) (p₁ p₂ t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    univ.sup' univ_nonempty (fun a => (t * p₁ + (1 - t) * p₂) * v a + (1 - (t * p₁ + (1 - t) * p₂)) * w a) ≤
      t * univ.sup' univ_nonempty (fun a => p₁ * v a + (1 - p₁) * w a) +
        (1 - t) * univ.sup' univ_nonempty (fun a => p₂ * v a + (1 - p₂) * w a) := by
  rw [sup'_le_iff]
  intro a _
  have h1 : p₁ * v a + (1 - p₁) * w a ≤ univ.sup' univ_nonempty (fun a => p₁ * v a + (1 - p₁) * w a) :=
    le_sup' (fun a => p₁ * v a + (1 - p₁) * w a) (mem_univ a)
  have h2 : p₂ * v a + (1 - p₂) * w a ≤ univ.sup' univ_nonempty (fun a => p₂ * v a + (1 - p₂) * w a) :=
    le_sup' (fun a => p₂ * v a + (1 - p₂) * w a) (mem_univ a)
  nlinarith [mul_le_mul_of_nonneg_left h1 ht0, mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr ht1)]

/-! ## S9. Good's theorem for refinements on D-5 -/

variable {W C C' : Type*} [Fintype W] [DecidableEq W] [DecidableEq C] [DecidableEq C']

/-- `condExp` is monotone in the integrand. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma condExp_mono (P : Distr W) (π : W → C) {X Y : W → ℝ} (h : ∀ w, X w ≤ Y w) (w : W) :
    condExp P π X w ≤ condExp P π Y w := by
  unfold condExp
  apply div_le_div_of_nonneg_right _ (classMass_nonneg P π w)
  exact sum_le_sum fun w' _ => mul_le_mul_of_nonneg_left (h w') (P.nonneg w')

/-- **Good's theorem for refinements ("supports"):** for a finite decision problem with payoffs
`u_a` and `π'` refining `π`, `max_a E_P[u_a | π] ≤ E_P[max_a E_P[u_a | π'] | π]` at every state — the
finer estimator's decision value is at least the coarser one's, by the tower and monotonicity.
Source: [[corr-wf13-inventory]] 046 / armstrong.md I6.2 (Jensen on the martingale)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem good_refinement {A : Type*} [Fintype A] [Nonempty A] (P : Distr W) {π : W → C} {π' : W → C'}
    (h : Refines π' π) (u : A → W → ℝ) (w : W) :
    univ.sup' univ_nonempty (fun a => condExp P π (u a) w) ≤
      condExp P π (fun w' => univ.sup' univ_nonempty (fun a => condExp P π' (u a) w')) w := by
  rw [sup'_le_iff]
  intro a _
  rw [← congrFun (condExp_condExp P h (u a)) w]
  exact condExp_mono P π (fun w' => le_sup' (fun a => condExp P π' (u a) w') (mem_univ a)) w

/-! ## S9 (047). The two-state mixture identity -/

/-- **`P(Pr) P(W | Pr) + P(¬Pr) P(W | ¬Pr) = ε`, the two-state formulas inlined** — the identity
`armstrong.md` I13.2 records as "reflection is silent on the base rate", stated with the
posterior weights in product form,
`((1 − ε) α + ε β) · (ε β / ((1 − ε) α + ε β)) + ((1 − ε)(1 − α) + ε (1 − β)) · (ε (1 − β) / (…)) = ε`
under both masses positive. The four reals are `twoState ε α β`'s press mass, its press-and-wrong
mass, its silence mass and its silence-and-wrong mass *typed in by hand*; the statement does not
mention `twoState`, `pressMass` or `obsExpect` (audit r1, NB-9), so the correspondence is by
inspection, not by Lean.
Source: [[corr-wf13-inventory]] 047 / armstrong.md I13.2
Kind: L
Fidelity: variant: the two-state formulas inlined, not stated over `twoState`
Hyps: (a) positivity of both event masses -/
theorem mixture_identity (ε α β : ℝ) (hp : 0 < (1 - ε) * α + ε * β)
    (hs : 0 < (1 - ε) * (1 - α) + ε * (1 - β)) :
    ((1 - ε) * α + ε * β) * (ε * β / ((1 - ε) * α + ε * β)) +
      ((1 - ε) * (1 - α) + ε * (1 - β)) * (ε * (1 - β) / ((1 - ε) * (1 - α) + ε * (1 - β))) = ε := by
  rw [mul_div_cancel₀ _ (ne_of_gt hp), mul_div_cancel₀ _ (ne_of_gt hs)]; ring

/-- **The certain-update case:** if the press is certain on `W` and impossible on `R` (`α = 0`,
`β = 1`), the press posterior is `1` and the silence posterior `0`, and the identity reads
`ε · 1 + (1 − ε) · 0 = ε`.
Source: [[corr-wf13-inventory]] 047 / armstrong.md I13.2 (the certain-update case)
Kind: L
Fidelity: exact -/
theorem mixture_identity_certain (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    ε * (ε * 1 / ((1 - ε) * 0 + ε * 1)) + (1 - ε) * (ε * (1 - 1) / ((1 - ε) * (1 - 0) + ε * (1 - 1))) = ε := by
  have hε : ε ≠ 0 := ne_of_gt h0
  rw [show (1 - ε) * 0 + ε * 1 = ε by ring, show (1 - ε) * (1 - 0) + ε * (1 - 1) = 1 - ε by ring,
    show ε * (1 - 1) = 0 by ring, mul_one, div_self hε, zero_div]
  ring

end Cleanroom.Corrigibility.CorrIndifference.Critiques
