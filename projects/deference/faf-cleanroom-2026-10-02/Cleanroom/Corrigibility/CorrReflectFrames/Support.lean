import Cleanroom.Corrigibility.CorrReflectFrames.Collapse

/-!
# corr-reflect-frames — T4: zero → positive is forbidden

Radical I2.2, MM Proposition I2.1 and ddb's support lemma (L-A) on frames: a reflected (or
value-reflected, or totally trusted) successor gives no `π`-null event positive probability.
At the anticipation level the same fact is `udt-supercondition`'s
`SameOntologyModel.boundedDensity` (Diaconis–Zabell necessity), cited in the report.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W] {π : W → ℝ} {F : Frame W}

/-- **Zero → positive is forbidden under Reflection**: a candidate gives every `π`-null event
probability zero (`π w = 0` on the event and `π w · 𝟙_cell w = π(cell) · ρ w` with `π(cell) > 0`).
Source: [[radical]] I2.2 l. 92, I3.3(d)
Kind: P
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem reflects_null_of_null (hπ : ∀ w, 0 ≤ π w) (h : Reflects π F) {ρ : W → ℝ}
    (hρ : ρ ∈ F.cands π) {A : Finset W} (hA : mass π A = 0) : mass ρ A = 0 := by
  have hpos : 0 < mass π (F.cell ρ) := (F.mem_cands_iff_mass_cell_pos hπ).1 hρ
  show ∑ w ∈ A, ρ w = 0
  apply sum_eq_zero
  intro w hw
  have hw0 : π w = 0 := eq_zero_of_mass_eq_zero hπ hA hw
  have := h ρ hρ w
  rw [hw0, zero_mul] at this
  rcases mul_eq_zero.1 this.symm with h0 | h0
  · exact absurd h0 hpos.ne'
  · exact h0

/-- **Zero → positive is forbidden under value-form reflection** (no introspection needed): at
`φ := A` and `c := ρ(A)`, the cell `{P_{t₂}(A) = c}` contains `ρ`'s own cell, so if `c > 0` the
calibration identity forces the cell to be `π`-null, contradicting candidacy.
Source: [[radical]] I2.2 l. 92 (`P_{t₁}(A | P_{t₂}(A) = c) = 0 ≠ c` for `c > 0`)
Kind: P
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem valueReflects_null_of_null (hπ : ∀ w, 0 ≤ π w) (h : ValueReflects π F) {ρ : W → ℝ}
    (hρ : ρ ∈ F.cands π) {A : Finset W} (hA : mass π A = 0) : mass ρ A = 0 := by
  have hρs := F.mem_stdSimplex_of_mem_cands hρ
  by_contra hne
  have hc : 0 < mass ρ A := lt_of_le_of_ne (mass_nonneg hρs.1 A) (Ne.symm hne)
  have hv := h A (mass ρ A)
  have hsub : F.cell ρ ⊆ valCell F A (mass ρ A) := by
    intro w hw
    rw [mem_valCell, Frame.mem_cell.1 hw]
  have h1 : mass π (A ∩ valCell F A (mass ρ A)) ≤ mass π A :=
    mass_mono hπ inter_subset_left
  have h2 : 0 < mass π (valCell F A (mass ρ A)) :=
    lt_of_lt_of_le ((F.mem_cands_iff_mass_cell_pos hπ).1 hρ) (mass_mono hπ hsub)
  have h3 : 0 < mass ρ A * mass π (valCell F A (mass ρ A)) := mul_pos hc h2
  have h4 : 0 ≤ mass π (A ∩ valCell F A (mass ρ A)) := mass_nonneg hπ _
  linarith

/-- **MM Proposition I2.1 (zero → positive is forbidden by Total Trust).** If `π(N) = 0` then
every world where the expert gives `N` positive probability is `π`-null: at `X := 𝟙_N` and
`s := P_w(N) > 0` the above-threshold sum is `−s · π([P(N) ≥ s]) ≥ 0`.
Source: [[mm]] Proposition I2.1 l. 117; [[ddb]] L-A l. 45 (same mechanism)
Kind: P
Fidelity: exact (finite; MM's union over `t > 0` is the single threshold `t = P_w(N)`)
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem totalTrust_null_of_null (hπ : ∀ w, 0 ≤ π w) (h : TotalTrust π F) {N : Finset W}
    (hN : mass π N = 0) {w : W} (hw : 0 < mass (F.P w) N) : π w = 0 := by
  have h1 := h.event_sum (ind N) (mass (F.P w) N)
  have hmem : w ∈ F.estEvent (ind N) (mass (F.P w) N) := by
    rw [Frame.mem_estEvent, E_ind]
  have hterm : ∀ v ∈ F.estEvent (ind N) (mass (F.P w) N),
      π v * (ind N v - mass (F.P w) N) = -(mass (F.P w) N * π v) := by
    intro v _
    by_cases hv : v ∈ N
    · rw [eq_zero_of_mass_eq_zero hπ hN hv]; ring
    · simp [ind, hv]; ring
  rw [sum_congr rfl hterm, sum_neg_distrib, ← mul_sum] at h1
  have h2 : π w ≤ ∑ v ∈ F.estEvent (ind N) (mass (F.P w) N), π v :=
    single_le_sum (fun v _ => hπ v) hmem
  have h3 : 0 ≤ ∑ v ∈ F.estEvent (ind N) (mass (F.P w) N), π v :=
    sum_nonneg (fun v _ => hπ v)
  have h4 : mass (F.P w) N * ∑ v ∈ F.estEvent (ind N) (mass (F.P w) N), π v ≤ 0 := by linarith
  have h5 : ∑ v ∈ F.estEvent (ind N) (mass (F.P w) N), π v = 0 := by
    rcases (mul_nonpos_iff.1 h4) with ⟨_, hle⟩ | ⟨hle, _⟩
    · exact le_antisymm hle h3
    · linarith
  exact le_antisymm (h5 ▸ h2) (hπ w)

/-- **ddb's support lemma (L-A).** Under Total Trust every `π`-positive world's expert gives
`π`'s support probability one (`N := W ∖ W_π` in `totalTrust_null_of_null`).
Source: [[ddb]] L-A l. 45
Kind: P
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem totalTrust_mass_supp (hπ : π ∈ stdSimplex ℝ W) (h : TotalTrust π F) {w : W}
    (hw : 0 < π w) : mass (F.P w) (supp π) = 1 := by
  have hN : mass π (univ \ supp π) = 0 := by
    show ∑ v ∈ univ \ supp π, π v = 0
    apply sum_eq_zero
    intro v hv
    exact eq_zero_of_not_mem_supp hπ.1 (mem_sdiff.1 hv).2
  have hzero : mass (F.P w) (univ \ supp π) = 0 := by
    by_contra hne
    have hpos : 0 < mass (F.P w) (univ \ supp π) :=
      lt_of_le_of_ne (mass_nonneg (F.P_nonneg w) _) (Ne.symm hne)
    have := totalTrust_null_of_null hπ.1 h hN hpos
    linarith
  have hsplit := mass_inter_add_mass_sdiff (F.P w) univ (supp π)
  rw [univ_inter, mass_univ (F.P_mem w), hzero] at hsplit
  linarith

end

end Cleanroom.Corrigibility.CorrReflectFrames
