import Cleanroom.Corrigibility.LegitNegPricing.Scoring

/-!
# Extension: B11 under partial information — the cell-wise covariance form

Package `legit-neg-pricing`, the mandate's required extension (plan §0.4 rule 6). Source: the
mandate's conjecture, "for a partition `cellOf` *without* `L_a`-purity,
`P1 (S2cell) a − P1 (S1 u) a = ∑_{C} π(C ∧ L_a) π(C ∧ ¬L_a)/π(C) · (𝔼[u_a | C ∧ ¬L_a] − 𝔼[u_a | C ∧ L_a])`",
the cell-wise form of A3's `−Cov/(π(L) π(¬L))` (`legit-neg-static`'s `condExp_gap_eq_neg_cov_div`).

**Derived** (not refuted). The junk-free form is `cellCov C = (π(C ∧ L_a) · ∑_{C ∧ ¬L_a} π u − π(C ∧ ¬L_a) · ∑_{C ∧ L_a} π u) / π(C)`
(`P1_S2cell_sub_P1_S1`); under positivity of both parts of a cell it is the conjectured product
of masses times the difference of conditional means (`cellCov_eq_cov`); it vanishes iff the cell
is `L_a`-pure or has equal conditional means (`cellCov_eq_zero_iff`). So the degree of collapse
is exactly the `L_a`-impure cells' covariance mass. Built on `Scoring.lean`'s `P1_S2cell_eq`,
which already holds without purity.
-/

namespace Cleanroom.Corrigibility.LegitNegPricing

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

variable {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]

/-- The distinct cells of a partition, as the image of `cellOf`.
Source: mandate extension
Kind: D
Fidelity: exact -/
def cells (cellOf : S → Finset S) : Finset (Finset S) := univ.image cellOf

/-- A sum over the states is the sum over the distinct cells of the within-cell sums.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_cells (cellOf : S → Finset S) (hmem : ∀ s, s ∈ cellOf s)
    (hcell : ∀ s t, t ∈ cellOf s → cellOf t = cellOf s) (f : S → ℚ) :
    ∑ t, f t = ∑ C ∈ cells cellOf, ∑ t ∈ C, f t := by
  have hU : (univ : Finset S) = (cells cellOf).biUnion id := by
    ext t
    simp only [mem_univ, true_iff, mem_biUnion, cells, mem_image, id, true_and]
    exact ⟨cellOf t, ⟨t, rfl⟩, hmem t⟩
  have hdisj : ((cells cellOf : Finset (Finset S)) : Set (Finset S)).PairwiseDisjoint id := by
    intro C hC C' hC' hne
    simp only [cells, coe_image, coe_univ, Set.image_univ, Set.mem_range] at hC hC'
    obtain ⟨s, rfl⟩ := hC
    obtain ⟨s', rfl⟩ := hC'
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro t ht ht'
    exact hne (by rw [← hcell s t ht, ← hcell s' t ht'])
  conv_lhs => rw [hU]
  rw [Finset.sum_biUnion hdisj]
  rfl

section Cell

variable (P : Problem S A) (a : A) (C : Finset S)

/-- `π(C ∧ L_a)`.
Source: mandate extension
Kind: D
Fidelity: exact -/
def cellMassL : ℚ := ∑ s ∈ C, P.prior s * ind (P.leg s a)

/-- `π(C ∧ ¬L_a)`.
Source: mandate extension
Kind: D
Fidelity: exact -/
def cellMassN : ℚ := ∑ s ∈ C, P.prior s * ind (!P.leg s a)

/-- `∑_{C ∧ L_a} π u_a`.
Source: mandate extension
Kind: D
Fidelity: exact -/
def cellSumL : ℚ := ∑ s ∈ C, P.prior s * ind (P.leg s a) * P.u s a

/-- `∑_{C ∧ ¬L_a} π u_a`.
Source: mandate extension
Kind: D
Fidelity: exact -/
def cellSumN : ℚ := ∑ s ∈ C, P.prior s * ind (!P.leg s a) * P.u s a

/-- The cell's covariance term, junk-free:
`(π(C ∧ L_a) · ∑_{C ∧ ¬L_a} π u − π(C ∧ ¬L_a) · ∑_{C ∧ L_a} π u) / π(C)`.
Source: mandate extension
Kind: D
Fidelity: exact -/
def cellCov : ℚ :=
  (cellMassL P a C * cellSumN P a C - cellMassN P a C * cellSumL P a C) / ∑ s ∈ C, P.prior s

/-- `cellMass_add`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellMass_add : cellMassL P a C + cellMassN P a C = ∑ s ∈ C, P.prior s := by
  unfold cellMassL cellMassN
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ind_not]; ring

/-- `cellSum_add`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellSum_add : cellSumL P a C + cellSumN P a C = ∑ s ∈ C, P.prior s * P.u s a := by
  unfold cellSumL cellSumN
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ind_not]; ring

/-- **Under positivity of both parts**, the cell term is the conjectured
`π(C ∧ L_a) π(C ∧ ¬L_a)/π(C) · (𝔼[u_a | C ∧ ¬L_a] − 𝔼[u_a | C ∧ L_a])`.
Source: mandate extension (the conjectured form)
Kind: L
Fidelity: exact
Hyps: (a) both parts of the cell have positive mass (so the conditional means are not junk) -/
theorem cellCov_eq_cov (hL : cellMassL P a C ≠ 0) (hN : cellMassN P a C ≠ 0) :
    cellCov P a C
      = cellMassL P a C * cellMassN P a C / (∑ s ∈ C, P.prior s)
        * (cellSumN P a C / cellMassN P a C - cellSumL P a C / cellMassL P a C) := by
  unfold cellCov
  field_simp

/-- `cellSumL` vanishes when `π(C ∧ L_a) = 0` (each term has a zero factor), likewise the `¬L` part.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellSumL_eq_zero_of_mass (h : cellMassL P a C = 0) : cellSumL P a C = 0 := by
  unfold cellMassL at h
  unfold cellSumL
  refine Finset.sum_eq_zero fun s hs => ?_
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun t _ => mul_nonneg (P.prior_nonneg t) (ind_nonneg _))).1 h s hs
  rw [this, zero_mul]

/-- `cellSumN_eq_zero_of_mass`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellSumN_eq_zero_of_mass (h : cellMassN P a C = 0) : cellSumN P a C = 0 := by
  unfold cellMassN at h
  unfold cellSumN
  refine Finset.sum_eq_zero fun s hs => ?_
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun t _ => mul_nonneg (P.prior_nonneg t) (ind_nonneg _))).1 h s hs
  rw [this, zero_mul]

/-- **The cell term vanishes iff the cell is `L_a`-pure or has equal conditional means.**
Source: mandate extension ("vanishing iff every cell is `L_a`-pure or has equal conditional means")
Kind: P
Fidelity: exact
Hyps: (a) positive cell mass -/
theorem cellCov_eq_zero_iff (hpos : 0 < ∑ s ∈ C, P.prior s) :
    cellCov P a C = 0
      ↔ cellMassL P a C = 0 ∨ cellMassN P a C = 0
        ∨ cellSumN P a C / cellMassN P a C = cellSumL P a C / cellMassL P a C := by
  have key : cellCov P a C = 0
      ↔ cellMassL P a C * cellSumN P a C = cellMassN P a C * cellSumL P a C := by
    unfold cellCov
    rw [div_eq_zero_iff, sub_eq_zero]
    exact or_iff_left hpos.ne'
  rw [key]
  constructor
  · intro h
    by_cases hL : cellMassL P a C = 0
    · exact Or.inl hL
    by_cases hN : cellMassN P a C = 0
    · exact Or.inr (Or.inl hN)
    refine Or.inr (Or.inr ?_)
    rw [div_eq_div_iff hN hL]
    linear_combination h
  · rintro (hL | hN | hE)
    · rw [hL, cellSumL_eq_zero_of_mass P a C hL]; ring
    · rw [hN, cellSumN_eq_zero_of_mass P a C hN]; ring
    · by_cases hL : cellMassL P a C = 0
      · rw [hL, cellSumL_eq_zero_of_mass P a C hL]; ring
      by_cases hN : cellMassN P a C = 0
      · rw [hN, cellSumN_eq_zero_of_mass P a C hN]; ring
      rw [div_eq_div_iff hN hL] at hE
      linear_combination hE

end Cell

/-- **The extension, derived**: for any partition into cells of positive mass (no purity),
`P1 (S2cell) a − P1 (S1 u) a = ∑_{C ∈ cells} cellCov C` — the degree of collapse is exactly the
`L_a`-impure cells' covariance mass (`cellCov_eq_cov`, `cellCov_eq_zero_iff`); under purity every
term vanishes and `Scoring.lean`'s `P1_S2cell_eq_P1_S1_of_pure` returns.
Source: mandate extension; [[corr-legit-neg-inventory]] item 023 (B11), 009 (A3's covariance form)
Kind: P
Fidelity: exact (the junk-free form; the conjectured product form under positivity is `cellCov_eq_cov`)
Hyps: (a) the partition axioms and positive cell mass -/
theorem P1_S2cell_sub_P1_S1 (P : Problem S A) (cellOf : S → Finset S) (a : A)
    (hmem : ∀ s, s ∈ cellOf s) (hcell : ∀ s t, t ∈ cellOf s → cellOf t = cellOf s)
    (hpos : ∀ s, 0 < ∑ t ∈ cellOf s, P.prior t) :
    P.P1 (P.S2cell cellOf) a - P.P1 (S1 P.u) a = ∑ C ∈ cells cellOf, cellCov P a C := by
  rw [P1_S2cell_eq P cellOf a hmem hcell]
  unfold Problem.P1
  rw [← Finset.sum_sub_distrib, sum_cells cellOf hmem hcell]
  refine Finset.sum_congr rfl fun C hC => ?_
  simp only [cells, mem_image, mem_univ, true_and] at hC
  obtain ⟨s, rfl⟩ := hC
  have hcond : ∀ t ∈ cellOf s,
      condLeg P cellOf a t = cellMassL P a (cellOf s) / ∑ r ∈ cellOf s, P.prior r := by
    intro t ht; unfold condLeg cellMassL; rw [hcell s t ht]
  have hm0 : (∑ r ∈ cellOf s, P.prior r) ≠ 0 := (hpos s).ne'
  calc ∑ t ∈ cellOf s, (P.prior t * P.u t a * condLeg P cellOf a t
          - P.prior t * ind (P.leg t a) * S1 P.u t a a)
      = ∑ t ∈ cellOf s, (P.prior t * P.u t a * (cellMassL P a (cellOf s) / ∑ r ∈ cellOf s, P.prior r)
          - P.prior t * ind (P.leg t a) * P.u t a) :=
        Finset.sum_congr rfl fun t ht => by rw [hcond t ht, S1_apply]
    _ = (∑ t ∈ cellOf s, P.prior t * P.u t a) * (cellMassL P a (cellOf s) / ∑ r ∈ cellOf s, P.prior r)
          - cellSumL P a (cellOf s) := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul]; rfl
    _ = cellCov P a (cellOf s) := by
        unfold cellCov
        rw [← cellSum_add P a (cellOf s), eq_div_iff hm0, sub_mul, mul_assoc,
          div_mul_cancel₀ _ hm0, ← cellMass_add P a (cellOf s)]
        ring

/-! ### The two-cell instance -/

/-- **The extension's N+ witness**: four equiprobable states, cells `{0, 1}` and `{2, 3}`; `a₁`
legitimate on `{0, 2}` and void on `{1, 3}` (both cells impure); `u(·, a₁) = (1, 0, 1/2, 1/2)`.
Then `P1 (S2cell) a₁ = 1/4`, `P1 (S1 u) a₁ = 3/8`, the difference `−1/8` is the first cell's
covariance term (`−1/8`) plus the second's (`0`: equal conditional means), as the theorem says.
Source: mandate extension ("the two-cell instance")
Kind: N+
Fidelity: exact -/
theorem impure_two_cell_witness :
    let P : Problem (Fin 4) (Fin 2) :=
      { prior := fun _ => 1/4
        prior_nonneg := fun _ => by norm_num
        prior_sum := by simp
        leg := fun s a => if a = 1 then ![true, false, true, false] s else true
        u := fun s a => ![![1, 1], ![1, 0], ![1, 1/2], ![1, 1/2]] s a }
    let cellOf : Fin 4 → Finset (Fin 4) := fun s => if s.val < 2 then {0, 1} else {2, 3}
    (∀ s, s ∈ cellOf s) ∧ (∀ s t, t ∈ cellOf s → cellOf t = cellOf s)
    ∧ (∀ s, 0 < ∑ t ∈ cellOf s, P.prior t)
    ∧ ¬ (∀ s t, t ∈ cellOf s → P.leg t 1 = P.leg s 1)
    ∧ P.P1 (P.S2cell cellOf) 1 = 1/4 ∧ P.P1 (S1 P.u) 1 = 3/8
    ∧ cellCov P 1 {0, 1} = -1/8 ∧ cellCov P 1 {2, 3} = 0
    ∧ P.P1 (P.S2cell cellOf) 1 - P.P1 (S1 P.u) 1 = cellCov P 1 {0, 1} + cellCov P 1 {2, 3} := by
  intro P cellOf
  have hmem : ∀ s, s ∈ cellOf s := by decide
  have hcell : ∀ s t, t ∈ cellOf s → cellOf t = cellOf s := by decide
  have hpos : ∀ s, 0 < ∑ t ∈ cellOf s, P.prior t := by
    intro s; fin_cases s <;> simp [cellOf, P] <;> norm_num
  have himpure : ¬ (∀ s t, t ∈ cellOf s → P.leg t 1 = P.leg s 1) := by decide
  have hS2 : P.P1 (P.S2cell cellOf) 1 = 1/4 := by
    simp [P, cellOf, Problem.P1, Problem.S2cell, Problem.Hc, Problem.cellprior, Fin.sum_univ_four]
      <;> norm_num
  have hS1 : P.P1 (S1 P.u) 1 = 3/8 := by
    simp [P, Problem.P1, Fin.sum_univ_four] <;> norm_num
  have hc1 : cellCov P 1 {0, 1} = -1/8 := by
    simp [cellCov, cellMassL, cellMassN, cellSumL, cellSumN, P] <;> norm_num
  have hc2 : cellCov P 1 {2, 3} = 0 := by
    simp [cellCov, cellMassL, cellMassN, cellSumL, cellSumN, P] <;> norm_num
  refine ⟨hmem, hcell, hpos, himpure, hS2, hS1, hc1, hc2, ?_⟩
  rw [hS2, hS1, hc1, hc2]; norm_num

end Cleanroom.Corrigibility.LegitNegPricing
