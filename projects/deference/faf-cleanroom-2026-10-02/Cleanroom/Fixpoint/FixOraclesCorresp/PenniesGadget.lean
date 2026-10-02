import Cleanroom.Fixpoint.FixOraclesCorresp.NashReflective
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.PenniesGadget`: Lemma A.1, the variant Matching Pennies

Target 14 (fixpoint-lit-2-008). An **ambient** two-action game `twoActionGame u` with three
distinguished players `row col mat` (pairwise distinct) whose payoffs for `row` and `col` at every pure
profile `a` are FTC's tables as functions of `(a row, a col, a mat)`:

* Row gets `1` exactly on Up-Left and Down-Right (`a row = a col`), whatever Matrix plays;
* Column gets `1` exactly on Down-Left-Front (`a row = 1, a col = 0, a mat = 0`) and
  Up-Right-Back (`a row = 0, a col = 1, a mat = 1`);

every other player's payoff is arbitrary. Conclusion (`pennies_gadget`): at every mixed Nash
equilibrium, `P(Row = Down) = P(Matrix = Back)`, i.e. `(σ row).val 1 = (σ mat).val 1`.

The one real step is the marginalization "Column's expected payoff against independent mixing is
`p(1−q)` vs `(1−p)q`": `sum_prod_agreeInd` computes `∑ τ, (∏ j, ρ j (τ j)) * [τ = v on T]` as
`∏ j ∈ T, ρ j (v j)` for any family of probability vectors `ρ`, and both tables are sums of two such
indicators. With `gain u row x = 2 x col − 1` and `gain u col x = x mat − x row`, Theorem 4.1
(`isMixedNashEq_iff_reflective`) turns the paper's three cases into two: `x mat > x row` forces
`x col = 1`, hence `x row = 1 > x mat`; `x mat < x row` forces `x col = 0`, hence `x row = 0 < x mat`.
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set StrategicGame Finset

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The indicator of "`τ` agrees with `v` on `T`".
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def agreeInd (T : Finset N) (v τ : N → Fin 2) : ℝ := if ∀ j ∈ T, τ j = v j then 1 else 0

/-- **Marginalization**: for probability vectors `ρ j`, the `ρ`-expectation of the indicator of
"`τ = v` on `T`" is `∏ j ∈ T, ρ j (v j)` (the coordinates off `T` integrate to `1`).
Source: FTC 2015 Lemma A.1 (proof, "Column must be indifferent … `p(1 − q) = (1 − p)q`"); Theorem 5.1
(proof, "independent samples")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem sum_prod_agreeInd (ρ : N → Fin 2 → ℝ) (hρ : ∀ j, ∑ s, ρ j s = 1) (T : Finset N)
    (v : N → Fin 2) :
    ∑ τ : N → Fin 2, (∏ j, ρ j (τ j)) * agreeInd T v τ = ∏ j ∈ T, ρ j (v j) := by
  have h1 : ∀ τ : N → Fin 2, (∏ j, ρ j (τ j)) * agreeInd T v τ =
      ∏ j, (ρ j (τ j) * if j ∈ T then (if τ j = v j then 1 else 0) else 1) := by
    intro τ
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_boole]
    unfold agreeInd
    by_cases hp : ∀ j ∈ T, τ j = v j <;> simp [hp]
  have h2 : ∏ j ∈ T, ρ j (v j) = ∏ j, if j ∈ T then ρ j (v j) else 1 := by
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun j t => ρ j t * if j ∈ T then (if t = v j then (1 : ℝ) else 0) else 1),
    h2]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j ∈ T
  · simp [hj, Finset.sum_ite_eq']
  · simp [hj, hρ j]

/-- `rawEP` of a payoff that is a finite sum of agreement indicators.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem rawEP_of_agreeInd_sum (u : (N → Fin 2) → N → ℝ) (ρ : N → Fin 2 → ℝ)
    (hρ : ∀ j, ∑ s, ρ j s = 1) (j : N) {K : Type*} [Fintype K] (T : K → Finset N)
    (v : K → N → Fin 2) (hu : ∀ τ, u τ j = ∑ k, agreeInd (T k) (v k) τ) :
    rawEP u ρ j = ∑ k, ∏ i ∈ T k, ρ i (v k i) := by
  unfold rawEP
  simp_rw [hu, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => sum_prod_agreeInd ρ (hρ) (T k) (v k)

omit [Fintype N] in
/-- The deviation weight vectors are probability vectors.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_update_wt (x : N → ℝ) (i : N) (s : Fin 2) (j : N) :
    ∑ t, Function.update (fun j => wt (x j)) i (pureWt s) j t = 1 := by
  by_cases h : j = i
  · subst h
    simp only [Function.update_self]
    exact sum_pureWt s
  · simp only [Function.update_of_ne h]
    exact sum_wt _

/-- Row's table: `[a row = a col] = [a row = 0 ∧ a col = 0] + [a row = 1 ∧ a col = 1]`, as agreement
indicators on `{row, col}`.
Source: FTC 2015 Lemma A.1 (the two payoff matrices, first coordinates)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem row_table_eq (row col : N) (a : N → Fin 2) :
    (if a row = a col then (1 : ℝ) else 0) =
      ∑ k : Fin 2, agreeInd {row, col} (fun _ => k) a := by
  simp only [agreeInd, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Fin.sum_univ_two]
  generalize a row = r
  generalize a col = c
  fin_cases r <;> fin_cases c <;> simp

/-- Column's table: `[a mat = 0 ∧ a row = 1 ∧ a col = 0] + [a mat = 1 ∧ a row = 0 ∧ a col = 1]`, as
agreement indicators on `{row, col, mat}` with `v 0 = (1, 0, 0)` and `v 1 = (0, 1, 1)` on
`(row, col, mat)`.
Source: FTC 2015 Lemma A.1 (the two payoff matrices, second coordinates)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem col_table_eq {row col mat : N} (hrc : row ≠ col) (hrm : row ≠ mat) (a : N → Fin 2) :
    (if a mat = 0 then (if a row = 1 ∧ a col = 0 then (1 : ℝ) else 0)
      else (if a row = 0 ∧ a col = 1 then 1 else 0)) =
      ∑ k : Fin 2, agreeInd {row, col, mat}
        (fun j => if j = row then (if k = 0 then 1 else 0) else k) a := by
  simp only [agreeInd, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Fin.sum_univ_two, if_true, hrc.symm, hrm.symm, if_false]
  generalize a row = r
  generalize a col = c
  generalize a mat = m
  fin_cases r <;> fin_cases c <;> fin_cases m <;> simp

/-- Row's gain in the ambient game: `2 x col − 1`.
Source: FTC 2015 Lemma A.1 (proof)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem gain_row (u : (N → Fin 2) → N → ℝ) {row col : N} (hrc : row ≠ col)
    (hrow : ∀ a, u a row = if a row = a col then 1 else 0) (x : N → ℝ) :
    gain u row x = 2 * x col - 1 := by
  unfold gain
  have key : ∀ s : Fin 2,
      rawEP u (Function.update (fun j => wt (x j)) row (pureWt s)) row =
        ∑ k : Fin 2, pureWt s k * wt (x col) k := by
    intro s
    rw [rawEP_of_agreeInd_sum u _ (sum_update_wt x row s) row (fun _ => {row, col})
      (fun k _ => k) (fun τ => by rw [hrow]; exact row_table_eq row col τ)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.prod_pair hrc, Function.update_self, Function.update_of_ne hrc.symm]
  rw [key, key]
  simp [pureWt, wt]
  ring

/-- Column's gain in the ambient game: `x mat − x row`.
Source: FTC 2015 Lemma A.1 (proof: "`p(1 − q)` vs `(1 − p)q`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem gain_col (u : (N → Fin 2) → N → ℝ) {row col mat : N} (hrc : row ≠ col) (hrm : row ≠ mat)
    (hcm : col ≠ mat)
    (hcol : ∀ a, u a col = if a mat = 0 then (if a row = 1 ∧ a col = 0 then 1 else 0)
      else (if a row = 0 ∧ a col = 1 then 1 else 0)) (x : N → ℝ) :
    gain u col x = x mat - x row := by
  unfold gain
  have key : ∀ s : Fin 2,
      rawEP u (Function.update (fun j => wt (x j)) col (pureWt s)) col =
        ∑ k : Fin 2, wt (x row) (if k = 0 then 1 else 0) * (pureWt s k * wt (x mat) k) := by
    intro s
    rw [rawEP_of_agreeInd_sum u _ (sum_update_wt x col s) col (fun _ => {row, col, mat})
      (fun k j => if j = row then (if k = 0 then 1 else 0) else k)
      (fun τ => by rw [hcol]; exact col_table_eq hrc hrm τ)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.prod_insert (show row ∉ ({col, mat} : Finset N) by simp [hrc, hrm]),
      Finset.prod_pair hcm]
    simp [Function.update_of_ne, hrc, hrc.symm, hrm.symm, hcm.symm]
  rw [key, key]
  simp [pureWt, wt]
  ring

/-- **Target 14, Lemma A.1**: in any two-action game with three distinguished players `row`, `col`,
`mat` whose `row`/`col` payoffs are FTC's variant Matching Pennies tables (Matrix's action selects the
table), every mixed Nash equilibrium has `P(Row = Down) = P(Matrix = Back)`.
Source: FTC 2015 Lemma A.1 (Appendix A); [[fixpoint-lit-2-inventory]] 008
Kind: P
Fidelity: exact (ambient `n`-player game; the other players' payoffs are arbitrary)
Hyps: (a) none — `hrow`/`hcol` are the lemma's hypotheses (the tables) -/
theorem pennies_gadget (u : (N → Fin 2) → N → ℝ) {row col mat : N} (hrc : row ≠ col)
    (hrm : row ≠ mat) (hcm : col ≠ mat)
    (hrow : ∀ a, u a row = if a row = a col then 1 else 0)
    (hcol : ∀ a, u a col = if a mat = 0 then (if a row = 1 ∧ a col = 0 then 1 else 0)
      else (if a row = 0 ∧ a col = 1 then 1 else 0))
    {σ : MixedProfile (twoActionGame u)} (h : IsMixedNashEq (twoActionGame u) σ) :
    (σ row).val 1 = (σ mat).val 1 := by
  have hR := (isMixedNashEq_iff_reflective u σ).1 h
  have hcube := toCube_mem_cube σ
  have hr := hR row
  have hc := hR col
  simp only [evOf, gain_row u hrc hrow, gain_col u hrc hrm hcm hcol] at hr hc
  have hxm := hcube mat (mem_univ _)
  have hxr := hcube row (mem_univ _)
  change (toCube σ row) = toCube σ mat
  rcases lt_trichotomy (toCube σ mat) (toCube σ row) with hlt | heq | hgt
  · have h1 := hc.2 (by linarith)
    have h2 := hr.2 (by rw [h1]; norm_num)
    linarith [hxm.1]
  · exact heq.symm
  · have h1 := hc.1 (by linarith)
    have h2 := hr.1 (by rw [h1]; norm_num)
    linarith [hxm.2]

end Cleanroom.Fixpoint.FixOraclesCorresp
