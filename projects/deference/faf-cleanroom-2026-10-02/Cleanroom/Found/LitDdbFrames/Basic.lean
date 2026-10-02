import Cleanroom.Found.LitDdbFrames.Defs

/-!
# Basic API for the definitions of record

Package `lit-ddb-frames`. Supporting lemmas (kind L, no ledger rows) about expectation, mass,
support, cells, candidates and the informed expert, used by every theorem file.
-/

namespace Cleanroom.Found.LitDdbFrames

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Simplex membership -/

/-- Membership in the standard simplex, unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_stdSimplex_iff {ρ : W → ℝ} :
    ρ ∈ stdSimplex ℝ W ↔ (∀ w, 0 ≤ ρ w) ∧ ∑ w, ρ w = 1 := Iff.rfl

/-- Rows of a frame are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.P_nonneg (F : Frame W) (w v : W) : 0 ≤ F.P w v := (F.P_mem w).1 v

/-- Rows of a frame sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.P_sum (F : Frame W) (w : W) : ∑ v, F.P w v = 1 := (F.P_mem w).2

/-! ## Expectation -/

/-- Expectation is additive in the distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_add_left (ρ σ X : W → ℝ) : E (ρ + σ) X = E ρ X + E σ X := by
  simp [E, add_mul, sum_add_distrib]

/-- Expectation is homogeneous in the distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_smul_left (c : ℝ) (ρ X : W → ℝ) : E (c • ρ) X = c * E ρ X := by
  simp [E, mul_sum, mul_assoc]

/-- Expectation of a finite convex (or any linear) combination of distributions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_sum_left {ι : Type*} (s : Finset ι) (c : ι → ℝ) (z : ι → W → ℝ) (X : W → ℝ) :
    E (∑ i ∈ s, c i • z i) X = ∑ i ∈ s, c i * E (z i) X := by
  simp only [E, sum_apply, Pi.smul_apply, smul_eq_mul, sum_mul, mul_sum, mul_assoc]
  rw [sum_comm]

/-- Expectation is additive in the variable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_add_right (ρ X Y : W → ℝ) : E ρ (X + Y) = E ρ X + E ρ Y := by
  simp [E, mul_add, sum_add_distrib]

/-- Expectation of a difference of variables.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_sub_right (ρ X Y : W → ℝ) : E ρ (X - Y) = E ρ X - E ρ Y := by
  simp [E, mul_sub, sum_sub_distrib]

/-- Expectation of the negative of a variable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_neg_right (ρ X : W → ℝ) : E ρ (-X) = -E ρ X := by
  simp [E, sum_neg_distrib]

/-- Expectation of a scaled variable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_smul_right (ρ X : W → ℝ) (c : ℝ) : E ρ (c • X) = c * E ρ X := by
  simp [E, mul_sum, mul_left_comm]

/-- Expectation of a constant under a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_const {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) (s : ℝ) : E ρ (fun _ => s) = s := by
  simp [E, ← sum_mul, hρ.2]

/-- Expectation of an indicator is the mass of the proposition.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_ind (ρ : W → ℝ) (q : Finset W) : E ρ (ind q) = mass ρ q := by
  simp [E, ind, mass, mul_ite, sum_ite_mem, univ_inter]

/-- Expectation is monotone in the variable for nonnegative distributions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_le_E {ρ X Y : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w) (h : ∀ w, X w ≤ Y w) : E ρ X ≤ E ρ Y :=
  sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (h w) (hρ w)

/-- Expectation of a variable vanishing off a proposition is the sum over that proposition.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_eq_sum_of_support {ρ X : W → ℝ} {q : Finset W} (h : ∀ w, w ∉ q → X w = 0) :
    E ρ X = ∑ w ∈ q, ρ w * X w := by
  unfold E
  rw [← sum_subset (subset_univ q)]
  intro w _ hw
  simp [h w hw]

/-- Expectation under a distribution vanishing off a proposition is the sum over that proposition.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_eq_sum_of_support_left {ρ X : W → ℝ} {q : Finset W} (h : ∀ w, w ∉ q → ρ w = 0) :
    E ρ X = ∑ w ∈ q, ρ w * X w := by
  unfold E
  rw [← sum_subset (subset_univ q)]
  intro w _ hw
  simp [h w hw]

/-! ## Mass -/

/-- Mass is nonnegative for nonnegative distributions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_nonneg {ρ : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w) (q : Finset W) : 0 ≤ mass ρ q :=
  sum_nonneg fun w _ => hρ w

/-- Mass is monotone in the proposition for nonnegative distributions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_mono {ρ : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w) {q p : Finset W} (h : q ⊆ p) :
    mass ρ q ≤ mass ρ p :=
  sum_le_sum_of_subset_of_nonneg h fun w _ _ => hρ w

/-- The mass of everything is one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_univ {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) : mass ρ univ = 1 := hρ.2

/-- Mass is at most one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_le_one {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) (q : Finset W) : mass ρ q ≤ 1 :=
  (mass_mono hρ.1 (subset_univ q)).trans_eq (mass_univ hρ)

/-- A point of a proposition of zero mass has zero probability.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem eq_zero_of_mass_eq_zero {ρ : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w) {q : Finset W}
    (h : mass ρ q = 0) {w : W} (hw : w ∈ q) : ρ w = 0 :=
  (sum_eq_zero_iff_of_nonneg fun v _ => hρ v).1 h w hw

/-- Mass is positive iff some point of the proposition has positive probability.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_pos_iff {ρ : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w) {q : Finset W} :
    0 < mass ρ q ↔ ∃ w ∈ q, 0 < ρ w := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have : mass ρ q = 0 := sum_eq_zero fun w hw => le_antisymm (hne w hw) (hρ w)
    linarith
  · rintro ⟨w, hw, hpos⟩
    exact lt_of_lt_of_le hpos (single_le_sum (fun v _ => hρ v) hw)

/-- A point of positive probability makes the mass of any proposition containing it positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_pos_of_mem {ρ : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w) {q : Finset W} {w : W} (hw : w ∈ q)
    (hpos : 0 < ρ w) : 0 < mass ρ q :=
  (mass_pos_iff hρ).2 ⟨w, hw, hpos⟩

/-- Mass of a proposition as an expectation of its indicator.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_eq_E_ind (ρ : W → ℝ) (q : Finset W) : mass ρ q = E ρ (ind q) := (E_ind ρ q).symm

/-- Mass of a finite linear combination of distributions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_sum_left {ι : Type*} (s : Finset ι) (c : ι → ℝ) (z : ι → W → ℝ) (q : Finset W) :
    mass (∑ i ∈ s, c i • z i) q = ∑ i ∈ s, c i * mass (z i) q := by
  rw [mass_eq_E_ind, E_sum_left]
  simp [mass_eq_E_ind]

/-- Splitting a mass along a second proposition.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_inter_add_mass_sdiff (ρ : W → ℝ) (q p : Finset W) :
    mass ρ (q ∩ p) + mass ρ (q \ p) = mass ρ q :=
  sum_inter_add_sum_sdiff q p ρ

/-- Mass of an intersection is at most the mass of either side.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_inter_le_right {ρ : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w) (q p : Finset W) :
    mass ρ (q ∩ p) ≤ mass ρ p :=
  mass_mono hρ inter_subset_right

/-! ## Support -/

/-- Membership in the support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem mem_supp {ρ : W → ℝ} {w : W} : w ∈ supp ρ ↔ 0 < ρ w := by
  simp [supp]

/-- A nonnegative distribution vanishes off its support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem eq_zero_of_not_mem_supp {ρ : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w) {w : W} (h : w ∉ supp ρ) :
    ρ w = 0 := by
  rw [mem_supp, not_lt] at h
  exact le_antisymm h (hρ w)

/-- A distribution has full mass on its support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_supp {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) : mass ρ (supp ρ) = 1 := by
  rw [← mass_univ hρ]
  unfold mass
  apply sum_subset (subset_univ _)
  intro w _ hw
  exact eq_zero_of_not_mem_supp hρ.1 hw

/-- The support of a distribution is nonempty.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem supp_nonempty {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) : (supp ρ).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have := mass_supp hρ
  simp [h, mass] at this

/-- Full mass on a proposition means the distribution vanishes off it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem eq_zero_of_mass_eq_one {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) {q : Finset W}
    (h : mass ρ q = 1) {w : W} (hw : w ∉ q) : ρ w = 0 := by
  have h1 := mass_inter_add_mass_sdiff ρ univ q
  rw [univ_inter, mass_univ hρ, h] at h1
  have h2 : mass ρ (univ \ q) = 0 := by linarith
  exact eq_zero_of_mass_eq_zero hρ.1 h2 (by simp [hw])

/-- Full mass on a proposition puts every support point inside it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_of_mass_eq_one {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) {q : Finset W}
    (h : mass ρ q = 1) {w : W} (hw : 0 < ρ w) : w ∈ q := by
  by_contra hnot
  have := eq_zero_of_mass_eq_one hρ h hnot
  linarith

/-! ## Cells -/

/-- Membership in a cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem Frame.mem_cell {F : Frame W} {ρ : W → ℝ} {w : W} : w ∈ F.cell ρ ↔ F.P w = ρ := by
  simp [Frame.cell]

/-- Every world is in the cell of its own row.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.mem_cell_self (F : Frame W) (w : W) : w ∈ F.cell (F.P w) := by simp

/-- Cells of distinct distributions are disjoint.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.cell_disjoint (F : Frame W) {ρ σ : W → ℝ} (h : ρ ≠ σ) :
    Disjoint (F.cell ρ) (F.cell σ) := by
  rw [disjoint_left]
  intro w hw hw'
  rw [Frame.mem_cell] at hw hw'
  exact h (hw.symm.trans hw')

/-- The indicator of a cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ind_cell_apply (F : Frame W) (ρ : W → ℝ) (w : W) :
    ind (F.cell ρ) w = if F.P w = ρ then 1 else 0 := by
  simp [ind]

/-! ## Candidates -/

/-- Membership in the candidate set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.mem_cands {F : Frame W} {ρ σ : W → ℝ} :
    σ ∈ F.cands ρ ↔ ∃ w, 0 < ρ w ∧ F.P w = σ := by
  simp [Frame.cands]

/-- The row at a support point is a candidate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.P_mem_cands (F : Frame W) {ρ : W → ℝ} {w : W} (h : 0 < ρ w) : F.P w ∈ F.cands ρ :=
  Frame.mem_cands.2 ⟨w, h, rfl⟩

/-- A candidate is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.mem_stdSimplex_of_mem_cands (F : Frame W) {ρ σ : W → ℝ} (h : σ ∈ F.cands ρ) :
    σ ∈ stdSimplex ℝ W := by
  obtain ⟨w, _, rfl⟩ := Frame.mem_cands.1 h
  exact F.P_mem w

/-- Candidacy is positivity of the cell mass: `σ ∈ C_ρ ↔ ρ(P = σ) > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.mem_cands_iff_mass_cell_pos (F : Frame W) {ρ : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w)
    {σ : W → ℝ} : σ ∈ F.cands ρ ↔ 0 < mass ρ (F.cell σ) := by
  rw [mass_pos_iff hρ, Frame.mem_cands]
  simp only [Frame.mem_cell]
  constructor
  · rintro ⟨w, h, rfl⟩; exact ⟨w, rfl, h⟩
  · rintro ⟨w, h, hpos⟩; exact ⟨w, hpos, h⟩

/-- The candidate set of a distribution is nonempty.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.cands_nonempty (F : Frame W) {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) :
    (F.cands ρ).Nonempty :=
  (supp_nonempty hρ).image _

/-- Membership in `C_ρ⁻`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.mem_candsMinus {F : Frame W} {ρ σ : W → ℝ} :
    σ ∈ F.candsMinus ρ ↔ σ ≠ ρ ∧ σ ∈ F.cands ρ := by
  simp [Frame.candsMinus]

/-! ## The informed expert -/

/-- The informed expert vanishes off the cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.informed_eq_zero_of_ne (F : Frame W) {ρ : W → ℝ} {w : W} (h : F.P w ≠ ρ) :
    F.informed ρ w = 0 := by
  simp [Frame.informed, h]

/-- The informed expert is nonnegative when `ρ` is.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.informed_nonneg (F : Frame W) {ρ : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w) (w : W) :
    0 ≤ F.informed ρ w := by
  unfold Frame.informed
  split_ifs
  · exact div_nonneg (hρ w) (mass_nonneg hρ _)
  · exact le_rfl

/-- On the cell, `P̂_ρ w · ρ(P = ρ) = ρ w` once the self-cell has positive mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.informed_mul_selfMass (F : Frame W) {ρ : W → ℝ} (h : 0 < F.selfMass ρ) {w : W}
    (hw : F.P w = ρ) : F.informed ρ w * F.selfMass ρ = ρ w := by
  simp [Frame.informed, hw, div_mul_cancel₀ _ h.ne']

/-- The informed expert has zero mass on any cell of a different distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.mass_informed_cell_of_ne (F : Frame W) {ρ σ : W → ℝ} (h : ρ ≠ σ) :
    mass (F.informed ρ) (F.cell σ) = 0 := by
  apply sum_eq_zero
  intro w hw
  rw [Frame.mem_cell] at hw
  exact F.informed_eq_zero_of_ne (hw.symm ▸ h.symm)

/-- The informed expert's mass on the self-cell times the self-mass is the self-mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.mass_informed_cell_mul (F : Frame W) {ρ : W → ℝ} (h : 0 < F.selfMass ρ) :
    mass (F.informed ρ) (F.cell ρ) * F.selfMass ρ = F.selfMass ρ := by
  unfold mass
  rw [sum_mul]
  conv_rhs => rw [Frame.selfMass, mass]
  apply sum_congr rfl
  intro w hw
  exact F.informed_mul_selfMass h (Frame.mem_cell.1 hw)

/-- The informed expert is a distribution once the self-cell has positive mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.informed_mem_stdSimplex (F : Frame W) {ρ : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w)
    (h : 0 < F.selfMass ρ) : F.informed ρ ∈ stdSimplex ℝ W := by
  refine ⟨F.informed_nonneg hρ, ?_⟩
  have h1 := F.mass_informed_cell_mul h
  have h2 : mass (F.informed ρ) (F.cell ρ) = mass (F.informed ρ) univ := by
    unfold mass
    apply sum_subset (subset_univ _)
    intro w _ hw
    exact F.informed_eq_zero_of_ne (fun e => hw (Frame.mem_cell.2 e))
  have h3 : mass (F.informed ρ) univ = 1 := by
    rw [← h2]
    exact (mul_left_inj' h.ne').1 (by rw [h1, one_mul])
  exact h3

/-- Mass of the informed expert on any proposition is at most one (also at a null self-cell,
where it is the zero vector).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.mass_informed_le_one (F : Frame W) {ρ : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w)
    (q : Finset W) : mass (F.informed ρ) q ≤ 1 := by
  rcases lt_or_ge 0 (F.selfMass ρ) with h | h
  · exact mass_le_one (F.informed_mem_stdSimplex hρ h) q
  · have : F.selfMass ρ = 0 := le_antisymm h (mass_nonneg hρ _)
    have hz : ∀ w, F.informed ρ w = 0 := fun w => by simp [Frame.informed, this]
    simp [mass, hz]

/-- The expectation of the informed expert, cleared of its denominator: on a positive self-cell,
`E_{P̂_ρ}(X) · ρ(P = ρ) = ∑ w ∈ [P = ρ], ρ w · X w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.E_informed_mul_selfMass (F : Frame W) {ρ : W → ℝ} (h : 0 < F.selfMass ρ)
    (X : W → ℝ) : E (F.informed ρ) X * F.selfMass ρ = ∑ w ∈ F.cell ρ, ρ w * X w := by
  have hsupp : ∀ w, w ∉ F.cell ρ → F.informed ρ w = 0 := fun w hw =>
    F.informed_eq_zero_of_ne (fun e => hw (Frame.mem_cell.2 e))
  rw [E_eq_sum_of_support_left hsupp, sum_mul]
  apply sum_congr rfl
  intro w hw
  rw [mul_right_comm, F.informed_mul_selfMass h (Frame.mem_cell.1 hw)]

/-! ## Strategies -/

/-- The value of a strategy as an expectation of its diagonal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem stratValue_eq_E (π : W → ℝ) (S : W → (W → ℝ)) : stratValue π S = E π (fun w => S w w) :=
  rfl

/-- A recommended strategy is a strategy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.Recommended.isStrategy {F : Frame W} {𝒪 : DecisionProblem W} {S : W → (W → ℝ)}
    (h : F.Recommended 𝒪 S) : F.IsStrategy 𝒪 S := h.1

/-- Every option of a recommended strategy is in the menu.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.Recommended.mem {F : Frame W} {𝒪 : DecisionProblem W} {S : W → (W → ℝ)}
    (h : F.Recommended 𝒪 S) (w : W) : S w ∈ 𝒪 := h.1.1 w

/-- The cell constraint of a recommended strategy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.Recommended.cell {F : Frame W} {𝒪 : DecisionProblem W} {S : W → (W → ℝ)}
    (h : F.Recommended 𝒪 S) {w v : W} (e : F.P w = F.P v) : S w = S v := h.1.2 w v e

/-- The optimality clause of a recommended strategy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.Recommended.le {F : Frame W} {𝒪 : DecisionProblem W} {S : W → (W → ℝ)}
    (h : F.Recommended 𝒪 S) (w : W) {o : W → ℝ} (ho : o ∈ 𝒪) : E (F.P w) o ≤ E (F.P w) (S w) :=
  h.2 w o ho

end

end Cleanroom.Found.LitDdbFrames
