import Cleanroom.Corrigibility.LegitNegDynamic.Dinkelbach

/-!
Audit r2 (adversarial) probe for `legit-neg-dynamic`: the load-bearing identity
`updateless_P2_iff_cellwise_P3` run end to end on **instance B**, where the updateless P2-optimum is
the *voiding* action `y` (on instance A it is `x`, where P2 and cdot agree — the library's only
end-to-end instance). Here `λ* = 901/1010` is the `sup'` of record over `Λ`, "`y` everywhere" is an
updateless optimum through the identity, and "`x` everywhere" is not. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing

lemma d2B_values :
    d2B.PL 0 = 1 ∧ d2B.PL 1 = 101/200 ∧ d2B.P1 (S1 d2B.u) 0 = 13/20 ∧ d2B.P1 (S1 d2B.u) 1 = 901/2000 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [d2B, Problem.PL, Problem.mass, Fin.sum_univ_three]; norm_num
  · simp [d2B, Problem.PL, Problem.mass, Fin.sum_univ_three]; norm_num
  · simp [d2B, Problem.P1, S1, Fin.sum_univ_three]; norm_num
  · simp [d2B, Problem.P1, S1, Fin.sum_univ_three]; norm_num

lemma d2B_Lambda_nonempty : (Lambda d2B d2cell).Nonempty :=
  Lambda_nonempty_of_PL_pos d2B d2cell (a := 0) (by rw [d2B_values.1]; norm_num)

/-- `λ* = 901/1010` on instance B, the `sup'` of record over `Λ`, attained by "`y` everywhere". -/
theorem d2B_lamStarT1 : lamStarT1 d2B d2cell (S1 d2B.u) d2B_Lambda_nonempty = 901/1010 := by
  have hleg : ∀ a, d2B.leg 2 a = true := by intro a; simp [d2B]
  have hu : ∀ a, d2B.u 2 a = d2B.u 2 0 := by intro a; simp [d2B]
  obtain ⟨hPL0, hPL1, hP10, hP11⟩ := d2B_values
  have hbound : ∀ π ∈ Lambda d2B d2cell,
      ratio (policyProblem d2B d2cell) (policyVec d2cell (S1 d2B.u)) π ≤ 901/1010 := by
    intro π hπ
    have hpos : 0 < policyPL d2B π.1 := (mem_Lambda _ _).1 hπ
    obtain ⟨hv, hp⟩ := d2_policy_values d2B hleg hu π
    unfold ratio
    rw [policyProblem_P1, policyProblem_PL, div_le_iff₀ hpos, hv, hp]
    generalize π.1 0 = a
    fin_cases a <;> simp [d2B, Problem.P1, Problem.PL, Problem.mass, S1, Fin.sum_univ_three] <;> norm_num
  have hy : ratio (policyProblem d2B d2cell) (policyVec d2cell (S1 d2B.u))
      ⟨fun _ => 1, cellPolicy_const _ _⟩ = 901/1010 := by
    unfold ratio
    rw [policyProblem_P1, policyProblem_PL, policyValue_const, policyPL_const, hP11, hPL1]; norm_num
  have hymem : (⟨fun _ => 1, cellPolicy_const _ _⟩ : CellPol (A := Fin 2) d2cell) ∈ Lambda d2B d2cell := by
    rw [mem_Lambda, policyPL_const, hPL1]; norm_num
  unfold lamStarT1 lamStar
  apply le_antisymm
  · exact Finset.sup'_le _ _ hbound
  · rw [← hy]; exact Finset.le_sup' _ hymem

/-- "`y` everywhere" is an updateless P2-optimum on instance B, through the identity. -/
theorem d2B_updateless_y :
    (⟨fun _ => 1, cellPolicy_const _ _⟩ : CellPol (A := Fin 2) d2cell)
      ∈ argmaxOpt (fun π : CellPol (A := Fin 2) d2cell => policyP2 d2B (S1 d2B.u) π.1) := by
  rw [updateless_P2_iff_cellwise_P3 d2B_partition (S1 d2B.u) d2B_Lambda_nonempty, d2B_lamStarT1]
  refine ⟨?_, ?_⟩
  · show 0 < policyPL d2B (fun _ => 1)
    rw [policyPL_const, d2B_values.2.1]; norm_num
  · intro s
    rw [mem_argmax]
    intro b
    rw [P3_const_one_eq, P3_const_one_eq]
    simp only [Problem.P1, Problem.PL, Problem.mass, restrict_prior, restrict_leg, Problem.cellprior]
    fin_cases s <;> fin_cases b <;>
      simp [d2cell, d2B, S1, Fin.sum_univ_three] <;> norm_num

/-- "`x` everywhere" is *not* an updateless P2-optimum on instance B (it fails the cellwise clause at
`i₁`), so the identity separates the two constant policies as the fixture's `t1` values do. -/
theorem d2B_not_updateless_x :
    (⟨fun _ => 0, cellPolicy_const _ _⟩ : CellPol (A := Fin 2) d2cell)
      ∉ argmaxOpt (fun π : CellPol (A := Fin 2) d2cell => policyP2 d2B (S1 d2B.u) π.1) := by
  rw [updateless_P2_iff_cellwise_P3 d2B_partition (S1 d2B.u) d2B_Lambda_nonempty, d2B_lamStarT1]
  rintro ⟨-, h⟩
  have := mem_argmax.1 (h 0) 1
  rw [P3_const_one_eq, P3_const_one_eq] at this
  simp only [Problem.P1, Problem.PL, Problem.mass, restrict_prior, restrict_leg, Problem.cellprior] at this
  simp [d2cell, d2B, S1, Fin.sum_univ_three] at this
  norm_num at this

end Cleanroom.Corrigibility.LegitNegDynamic
