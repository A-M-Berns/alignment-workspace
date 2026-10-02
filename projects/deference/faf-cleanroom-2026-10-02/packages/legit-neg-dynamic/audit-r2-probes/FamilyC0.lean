import Cleanroom.Corrigibility.LegitNegDynamic.Partial

/-!
Audit r2 (adversarial) probe for `legit-neg-dynamic`: the extension's "the verdicts first part at
`σ̂ = 7/9`" is stated at the cell `C₁` ("says `i₁`"). This probe checks the *other* cell
`C₀` ("says `i₂`") of the same family: there the updateful P2 verdict and the updateless
(`λ* = 2/5`) verdict agree for every `σ ∈ [1/2, 1]` — both `{x}` below `σ = 1`, both a tie at
`σ = 1` — so the family-wide first parting is indeed at `7/9`, at `C₁`, and the headline does not
hide an earlier parting at the cell it does not mention. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing

/-- `C₀`: the cell where the signal says `i₂`. -/
def C0 : Finset (Fin 3 × Bool) := sigCell false

variable (σ : ℚ) (hσ0 : 1/2 ≤ σ) (hσ1 : σ ≤ 1)

lemma C0_pos : 0 < ∑ t ∈ C0, (d2Aσ σ hσ0 hσ1).prior t := by
  unfold C0; rw [sigCell_mass σ hσ0 hσ1]; norm_num

/-- At `C₀`: `n x = (5 − 2σ)/10`, `n y = (9 + 21σ)/100`, `d x = 1`, `d y = (1 + 9σ)/10`. -/
lemma C0_values :
    ((d2Aσ σ hσ0 hσ1).restrict C0 (C0_pos σ hσ0 hσ1)).P1 (S1 (d2Aσ σ hσ0 hσ1).u) 0 = (5 - 2 * σ) / 10 ∧
    ((d2Aσ σ hσ0 hσ1).restrict C0 (C0_pos σ hσ0 hσ1)).P1 (S1 (d2Aσ σ hσ0 hσ1).u) 1 = (9 + 21 * σ) / 100 ∧
    ((d2Aσ σ hσ0 hσ1).restrict C0 (C0_pos σ hσ0 hσ1)).PL 0 = 1 ∧
    ((d2Aσ σ hσ0 hσ1).restrict C0 (C0_pos σ hσ0 hσ1)).PL 1 = (1 + 9 * σ) / 10 := by
  have hmass : ∑ t ∈ C0, (d2Aσ σ hσ0 hσ1).prior t = 1/2 := by
    unfold C0; exact sigCell_mass σ hσ0 hσ1 false
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [Problem.P1, Problem.PL, Problem.mass, restrict_prior, restrict_leg, restrict_u,
      Problem.cellprior, hmass]
     simp [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool, C0, sigCell, d2Aσ, d2A, sig, S1]
     try ring)

/-- The updateful P2 verdict at `C₀`: `{x}` for `σ < 1`, a tie at `σ = 1`. -/
theorem C0_updateful :
    (σ < 1 → argmaxOpt (((d2Aσ σ hσ0 hσ1).restrict C0 (C0_pos σ hσ0 hσ1)).P2 (S1 (d2Aσ σ hσ0 hσ1).u)) = {0}) ∧
    (σ = 1 → argmaxOpt (((d2Aσ σ hσ0 hσ1).restrict C0 (C0_pos σ hσ0 hσ1)).P2 (S1 (d2Aσ σ hσ0 hσ1).u)) = univ) := by
  obtain ⟨n0, n1, d0, d1⟩ := C0_values σ hσ0 hσ1
  have hd1pos : (0 : ℚ) < (1 + 9 * σ) / 10 := by linarith
  have h0 : ((d2Aσ σ hσ0 hσ1).restrict C0 (C0_pos σ hσ0 hσ1)).P2 (S1 (d2Aσ σ hσ0 hσ1).u) 0
      = some ((5 - 2 * σ) / 10) := by
    rw [Problem.P2_of_ne _ _ _ (by rw [d0]; exact one_ne_zero), d0, n0, div_one]
  have h1 : ((d2Aσ σ hσ0 hσ1).restrict C0 (C0_pos σ hσ0 hσ1)).P2 (S1 (d2Aσ σ hσ0 hσ1).u) 1
      = some ((9 + 21 * σ) / (10 + 90 * σ)) := by
    rw [Problem.P2_of_ne _ _ _ (by rw [d1]; exact hd1pos.ne'), d1, n1]
    congr 1
    have h10 : (1 : ℚ) + 9 * σ ≠ 0 := by linarith
    have h100 : (10 : ℚ) + 90 * σ = 10 * (1 + 9 * σ) := by ring
    rw [h100]
    field_simp
    ring
  have hsome := argmaxOpt_eq_argmax_of_forall_some
    (f := ((d2Aσ σ hσ0 hσ1).restrict C0 (C0_pos σ hσ0 hσ1)).P2 (S1 (d2Aσ σ hσ0 hσ1).u))
    (g := ![(5 - 2 * σ) / 10, (9 + 21 * σ) / (10 + 90 * σ)])
    (by rw [Fin.forall_fin_two]; exact ⟨by simpa using h0, by simpa using h1⟩)
  have hden : (0 : ℚ) < 10 + 90 * σ := by linarith
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · rw [hsome, argmax_fin2_eq_zero_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [div_lt_div_iff₀ hden (by norm_num)]
    nlinarith [mul_pos (by linarith : (0:ℚ) < 9 * σ - 2) (by linarith : (0:ℚ) < 1 - σ)]
  · rw [hsome, argmax_fin2_eq_univ_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    subst hs; norm_num

/-- The updateless verdict at `C₀` (cellwise P3 with `W ≡ λ*`, `λ*` the `sup'` of record): `{x}`
for `σ < 1`, a tie at `σ = 1` — the same as the updateful one, for every `σ`. -/
theorem C0_updateless :
    (σ < 1 → argmax (((d2Aσ σ hσ0 hσ1).restrict C0 (C0_pos σ hσ0 hσ1)).P3
      (fun _ _ _ => lamStarT1 (d2Aσ σ hσ0 hσ1) sigCellOf (S1 (d2Aσ σ hσ0 hσ1).u)
        (family_Lambda_nonempty σ hσ0 hσ1)) 1 (S1 (d2Aσ σ hσ0 hσ1).u)) = {0}) ∧
    (σ = 1 → argmax (((d2Aσ σ hσ0 hσ1).restrict C0 (C0_pos σ hσ0 hσ1)).P3
      (fun _ _ _ => lamStarT1 (d2Aσ σ hσ0 hσ1) sigCellOf (S1 (d2Aσ σ hσ0 hσ1).u)
        (family_Lambda_nonempty σ hσ0 hσ1)) 1 (S1 (d2Aσ σ hσ0 hσ1).u)) = univ) := by
  obtain ⟨n0, n1, d0, d1⟩ := C0_values σ hσ0 hσ1
  have hstar := family_lamStar σ hσ0 hσ1 (family_Lambda_nonempty σ hσ0 hσ1)
  rw [hstar, argmax_P3_const_eq_shifted]
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · rw [argmax_fin2_eq_zero_iff, n0, n1, d0, d1]; linarith
  · rw [argmax_fin2_eq_univ_iff, n0, n1, d0, d1]; subst hs; norm_num

end Cleanroom.Corrigibility.LegitNegDynamic
