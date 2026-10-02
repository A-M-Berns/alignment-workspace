import Cleanroom.Found.LitDdbFrames

/-!
# lit-ddb-facts — cell-partition helpers

Package `lit-ddb-facts` (faf-cleanroom run, 2026-09-29). Supporting lemmas (kind L, no ledger
rows) about the partition of a deferrer's support into the cells of its candidates, immodest
distributions, and sums that agree on the support. Everything is stated over the definitions of
record of `lit-ddb-frames` (`Cleanroom.Found.LitDdbFrames`), which are not redefined here.
-/

namespace Cleanroom.Lit.LitDdbFacts

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Sums over the candidates' cells -/

/-- A `π`-weighted sum over all worlds is the sum over the cells of `π`'s candidates: worlds
outside every candidate's cell are `π`-null.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_mul_eq_sum_cands (F : Frame W) {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) (X : W → ℝ) :
    ∑ w, π w * X w = ∑ ρ ∈ F.cands π, ∑ w ∈ F.cell ρ, π w * X w := by
  have h1 : ∀ ρ, ∑ w ∈ F.cell ρ, π w * X w = ∑ w, if F.P w = ρ then π w * X w else 0 := by
    intro ρ
    rw [Frame.cell, sum_filter]
  simp_rw [h1]
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · have : π w = 0 := by
      by_contra hne
      exact h (F.P_mem_cands (lt_of_le_of_ne (hπ w) (Ne.symm hne)))
    simp [this]

/-- The cell masses of the candidates of a distribution sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_cands_mass_cell (F : Frame W) {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) :
    ∑ σ ∈ F.cands ρ, mass ρ (F.cell σ) = 1 := by
  have := sum_mul_eq_sum_cands F hρ.1 (fun _ => 1)
  simp only [mul_one] at this
  rw [← hρ.2, this]
  rfl

/-- Two `π`-weighted sums agree when the index sets agree on the support of `π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_eq_of_supp_iff {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {A B : Finset W}
    (h : ∀ u, 0 < π u → (u ∈ A ↔ u ∈ B)) (f : W → ℝ) :
    ∑ w ∈ A, π w * f w = ∑ w ∈ B, π w * f w := by
  rw [← sum_filter_add_sum_filter_not A (fun u => 0 < π u),
    ← sum_filter_add_sum_filter_not B (fun u => 0 < π u)]
  have hz : ∀ (C : Finset W), ∑ u ∈ C.filter (fun u => ¬ 0 < π u), π u * f u = 0 := fun C =>
    sum_eq_zero fun u hu => by
      rw [le_antisymm (not_lt.1 (mem_filter.1 hu).2) (hπ u), zero_mul]
  rw [hz, hz, add_zero, add_zero]
  congr 1
  ext u
  simp only [mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(h u h2).1 h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(h u h2).2 h1, h2⟩

/-- Two masses agree when the propositions agree on the support of `π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_eq_of_supp_iff {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {A B : Finset W}
    (h : ∀ u, 0 < π u → (u ∈ A ↔ u ∈ B)) : mass π A = mass π B := by
  have := sum_eq_of_supp_iff hπ h (fun _ => 1)
  simpa [mass] using this

/-! ## Immodest distributions -/

/-- A distribution with full self-cell mass vanishes off its cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem eq_zero_of_selfMass_eq_one (F : Frame W) {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W)
    (h : F.selfMass ρ = 1) {w : W} (hw : F.P w ≠ ρ) : ρ w = 0 :=
  eq_zero_of_mass_eq_one hρ h (fun e => hw (Frame.mem_cell.1 e))

/-- An immodest distribution is its own only candidate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cands_eq_singleton_of_selfMass_eq_one (F : Frame W) {ρ : W → ℝ}
    (hρ : ρ ∈ stdSimplex ℝ W) (h : F.selfMass ρ = 1) : F.cands ρ = {ρ} := by
  ext σ
  rw [Frame.mem_cands, mem_singleton]
  constructor
  · rintro ⟨w, hw, rfl⟩
    by_contra hne
    have := eq_zero_of_selfMass_eq_one F hρ h hne
    linarith
  · rintro rfl
    have hpos : 0 < mass σ (F.cell σ) := by
      unfold Frame.selfMass at h
      rw [h]
      exact one_pos
    obtain ⟨w, hw, hpos⟩ := (mass_pos_iff hρ.1).1 hpos
    exact ⟨w, hpos, Frame.mem_cell.1 hw⟩

/-- `ρ ∈ C_ρ ↔ 0 < ρ(P = ρ)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_cands_self_iff (F : Frame W) {ρ : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w) :
    ρ ∈ F.cands ρ ↔ 0 < F.selfMass ρ :=
  F.mem_cands_iff_mass_cell_pos hρ

/-- Candidates of an immodest frame are immodest.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem immodest_cands {F : Frame W} (hF : F.Immodest) (π : W → ℝ) :
    ∀ ρ ∈ F.cands π, F.selfMass ρ = 1 := by
  intro ρ hρ
  obtain ⟨w, _, rfl⟩ := Frame.mem_cands.1 hρ
  exact hF w

/-- The informed expert is the zero vector exactly at a null self-cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem informed_eq_zero_iff (F : Frame W) {ρ : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w) :
    F.informed ρ = 0 ↔ F.selfMass ρ = 0 := by
  constructor
  · intro h
    by_contra hne
    have hpos : 0 < F.selfMass ρ := lt_of_le_of_ne (mass_nonneg hρ _) (Ne.symm hne)
    have h1 := F.mass_informed_cell_mul hpos
    rw [h] at h1
    have h0 : mass (0 : W → ℝ) (F.cell ρ) = 0 := by simp [mass]
    rw [h0, zero_mul] at h1
    exact hne h1.symm
  · intro h
    funext w
    simp [Frame.informed, h]

/-- `P̂_ρ = ρ` exactly when `ρ` is immodest.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem informed_eq_self_iff (F : Frame W) {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) :
    F.informed ρ = ρ ↔ F.selfMass ρ = 1 := by
  constructor
  · intro h
    rcases (mass_nonneg hρ.1 (F.cell ρ)).lt_or_eq with hpos | hzero
    · have h1 := F.mass_informed_cell_mul hpos
      rw [h] at h1
      have hs : 0 < F.selfMass ρ := hpos
      have h2 : F.selfMass ρ * F.selfMass ρ = F.selfMass ρ * 1 := by rw [mul_one]; exact h1
      exact mul_left_cancel₀ hs.ne' h2
    · exfalso
      have hz : F.informed ρ = 0 := (informed_eq_zero_iff F hρ.1).2 hzero.symm
      rw [hz] at h
      have := hρ.2
      rw [← h] at this
      simp at this
  · intro h
    funext w
    unfold Frame.informed
    split_ifs with hw
    · rw [h, div_one]
    · exact (eq_zero_of_selfMass_eq_one F hρ h hw).symm

end

end Cleanroom.Lit.LitDdbFacts
