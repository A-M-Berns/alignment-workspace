import Cleanroom.Lit.LitShutdownPrefs.PostConsistency

/-!
# Audit round 2 (fidelity) probe: the POSL ∧ ILPACS two-cycle is not specific to sum-total

`PostConsistency.posl_ilpacs_two_cycle` assumes the agent ranks single-length-`1` lotteries by
expected **sum-total**. This probe shows the same two ILPACS moves force a two-cycle for a
within-length **expected-utility** ranking whose utility is far from sum-total:
`u [10] = 100`, `u [9] = 1`, `u [0] = 0`. The package's weights `(1/10, 9/10)` no longer work
(`E_u X₁ = 200/11 > 18/19 = E_u Y₁`), but `α = 1/1000` on `[10]` does: the length-1 conditional
of `X' = α[10] + (1−α)D` is `(2/1001)[10] + (999/1001)[0]` with `E_u = 200/1001 < 18/19 = E_u Y₁`.
The general mechanism (hand argument in the audit): with three same-length trajectories
`t₁ ≻ t₂ ≻ t₃` ranked by any EU utility, `α → 0` on `t₁` and `β → 1` on `t₂` always give the
cycle, so the inconsistency holds for every agent satisfying Thornley 2025 §12's own
within-length VNM assumption with a strict 3-chain at some length. Not imported by the library.
-/

namespace AuditR2

open Cleanroom.Lit.LitShutdownPrefs Cleanroom.Lit.LitShutdownPrefs.Lottery
  Cleanroom.Lit.LitShutdownPrefs.Strict Cleanroom.Lit.LitShutdownPrefs.PostConsistency

/-- A within-length utility far from sum-total: `[10] ↦ 100`, `[9] ↦ 1`, everything else `0`. -/
noncomputable def u : Traj → ℝ := fun t => if t = [10] then 100 else if t = [9] then 1 else 0

theorem u_ten : u [10] = 100 := by simp [u]

theorem u_nine : u [9] = 1 := by norm_num [u]

theorem u_zero : u [0] = 0 := by norm_num [u]

/-- `X' = (1/1000)[10] + (999/1000) D`. -/
noncomputable def X' : Lottery Traj :=
  comb ![1/1000, 999/1000] (fun i => by fin_cases i <;> norm_num) (by norm_num [Fin.sum_univ_two])
    ![dirac [10], D]

/-- The length-1 conditional of `X'`: `(2/1001)[10] + (999/1001)[0]`. -/
noncomputable def X₁' : Lottery Traj := mix (2/1001) (by norm_num) (dirac [10]) (dirac [0])

theorem X₁'_lengths : X₁'.lengths = {1} := by
  unfold X₁'; rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]

/-- `X' = (1001/2000) X₁' + (999/2000) [1,1]`. -/
theorem X'_decomp :
    X'.p = ∑ i, (![1001/2000, 999/2000] : Fin 2 → ℝ) i •
      ((![X₁', dirac [1, 1]] : Fin 2 → Lottery Traj) i).p := by
  ext t
  simp only [X', X₁', D, comb_p, mix_p, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

/-- The package's weights fail for `u`: `E_u X₁ = 200/11 > 18/19 = E_u Y₁`, so the package's second
ILPACS instance is unavailable — the two-cycle needs the weights adapted to `u`. -/
theorem package_weights_fail : Y₁.expect u < X₁.expect u := by
  unfold Y₁ X₁
  simp only [expect_mix, expect_dirac, u_ten, u_nine, u_zero]
  norm_num

/-- **The two-cycle for an EU within-length ranking that is not sum-total.** -/
theorem two_cycle_vnm (lt : Lottery Traj → Lottery Traj → Prop)
    (hP : POSL lt) (hI : ILPACS lt) (hirr : ∀ Z, ¬ lt Z Z)
    (hEU : ∀ A B : Lottery Traj, A.lengths = {1} → B.lengths = {1} →
      B.expect u < A.expect u → lt A B) :
    lt X' Y ∧ lt Y X' := by
  have hlack : ∀ A B : Lottery Traj, A.lengths ≠ B.lengths → lacks lt A B := fun A B hne =>
    ⟨fun h => hne (hP _ _ h), fun h => hne (hP _ _ h).symm⟩
  have h10 : (dirac ([10] : Traj)).lengths = {1} := by simp [lengths_dirac, len]
  have h9 : (dirac ([9] : Traj)).lengths = {1} := by simp [lengths_dirac, len]
  have h11 : (dirac ([1, 1] : Traj)).lengths = {2} := by simp [lengths_dirac, len]
  have h10_9 : (dirac ([9] : Traj)).expect u < (dirac ([10] : Traj)).expect u := by
    simp only [expect_dirac, u_ten, u_nine]; norm_num
  have hY1X1 : X₁'.expect u < Y₁.expect u := by
    unfold Y₁ X₁'
    simp only [expect_mix, expect_dirac, u_ten, u_nine, u_zero]
    norm_num
  have hXY : lt X' Y := by
    refine hI 2 ![1/1000, 999/1000] ![9/10, 1/10] ![dirac [10], D] ![dirac [9], D] X' Y rfl rfl
      (fun i => by fin_cases i <;> norm_num) (fun i => by fin_cases i <;> norm_num)
      (fun i j hij => ?_) (fun i => ?_) ⟨0, ?_⟩
    · fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hlack (dirac [10]) D (by rw [h10, D_lengths]; decide)
      · exact hlack D (dirac [10]) (by rw [h10, D_lengths]; decide)
      · exact absurd rfl hij
    · fin_cases i
      · exact Or.inl (hEU _ _ h10 h9 h10_9)
      · exact Or.inr (Strict.indiff_self _ (hirr _))
    · exact hEU _ _ h10 h9 h10_9
  have hYX : lt Y X' := by
    refine hI 2 ![19/20, 1/20] ![1001/2000, 999/2000] ![Y₁, dirac [1, 1]] ![X₁', dirac [1, 1]] Y X'
      Y_decomp X'_decomp
      (fun i => by fin_cases i <;> norm_num) (fun i => by fin_cases i <;> norm_num)
      (fun i j hij => ?_) (fun i => ?_) ⟨0, ?_⟩
    · fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hlack Y₁ (dirac [1, 1]) (by rw [Y₁_lengths, h11]; decide)
      · exact hlack (dirac [1, 1]) Y₁ (by rw [Y₁_lengths, h11]; decide)
      · exact absurd rfl hij
    · fin_cases i
      · exact Or.inl (hEU _ _ Y₁_lengths X₁'_lengths hY1X1)
      · exact Or.inr (Strict.indiff_self _ (hirr _))
    · exact hEU _ _ Y₁_lengths X₁'_lengths hY1X1
  exact ⟨hXY, hYX⟩

/-- With asymmetry: inconsistent. -/
theorem inconsistent_vnm (lt : Lottery Traj → Lottery Traj → Prop)
    (hP : POSL lt) (hI : ILPACS lt) (hasymm : ∀ A B, lt A B → ¬ lt B A)
    (hEU : ∀ A B : Lottery Traj, A.lengths = {1} → B.lengths = {1} →
      B.expect u < A.expect u → lt A B) : False :=
  have h := two_cycle_vnm lt hP hI (fun Z h => hasymm Z Z h h) hEU
  hasymm _ _ h.1 h.2

end AuditR2
