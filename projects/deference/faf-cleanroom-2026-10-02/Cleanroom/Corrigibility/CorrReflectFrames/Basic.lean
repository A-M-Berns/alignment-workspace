import Cleanroom.Corrigibility.CorrReflectFrames.Defs

/-!
# corr-reflect-frames — support toolkit

Sums over row-closed events grouped by cells, sums that agree on the support, the consequences
of introspection at candidates (a candidate row vanishes off its own cell), and the one
consequence of `Reflects` every collapse step uses: on a cell, `∑_{P = ρ} π w · X w =
π(P = ρ) · E_ρ(X)`. No headline here.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Sums and indicators -/

/-- A sum over an event as a full sum against the indicator.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_eq_sum_mul_ind (g : W → ℝ) (A : Finset W) :
    ∑ w ∈ A, g w = ∑ w, g w * ind A w := by
  simp only [ind, mul_ite, mul_one, mul_zero]
  rw [sum_ite_mem, univ_inter]

/-- Weighted sums over two events that agree on the support of the weight are equal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_congr_supp {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {A B : Finset W}
    (h : ∀ w, 0 < π w → (w ∈ A ↔ w ∈ B)) (g : W → ℝ) :
    ∑ w ∈ A, π w * g w = ∑ w ∈ B, π w * g w := by
  have hsub : ∀ C : Finset W, ∑ w ∈ C ∩ supp π, π w * g w = ∑ w ∈ C, π w * g w := by
    intro C
    apply sum_subset inter_subset_left
    intro w hw hw'
    have : w ∉ supp π := fun hs => hw' (mem_inter.2 ⟨hw, hs⟩)
    rw [eq_zero_of_not_mem_supp hπ this, zero_mul]
  have hAB : A ∩ supp π = B ∩ supp π := by
    ext w
    simp only [mem_inter, mem_supp]
    exact ⟨fun ⟨ha, hs⟩ => ⟨(h w hs).1 ha, hs⟩, fun ⟨hb, hs⟩ => ⟨(h w hs).2 hb, hs⟩⟩
  rw [← hsub A, ← hsub B, hAB]

/-- Masses of two events that agree on the support are equal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_congr_supp {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {A B : Finset W}
    (h : ∀ w, 0 < π w → (w ∈ A ↔ w ∈ B)) : mass π A = mass π B := by
  have := sum_congr_supp hπ h (fun _ => 1)
  simpa [mass] using this

/-- Grouping a sum over a row-closed event by the cells it contains.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_rowClosed (F : Frame W) {A : Finset W}
    (hA : ∀ w v, F.P w = F.P v → w ∈ A → v ∈ A) (g : W → ℝ) :
    ∑ w ∈ A, g w = ∑ ρ ∈ A.image F.P, ∑ w ∈ F.cell ρ, g w := by
  rw [← sum_fiberwise_of_maps_to (fun w hw => mem_image_of_mem F.P hw) g]
  apply sum_congr rfl
  intro ρ hρ
  obtain ⟨v, hv, rfl⟩ := mem_image.1 hρ
  apply sum_congr _ (fun _ _ => rfl)
  ext w
  simp only [mem_filter, Frame.mem_cell]
  exact ⟨fun h => h.2, fun h => ⟨hA v w h.symm hv, h⟩⟩

/-- A world of positive probability is on a positive-mass cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_cell_pos_of_pos {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) (F : Frame W) {w : W}
    (hw : 0 < π w) : 0 < mass π (F.cell (F.P w)) :=
  mass_pos_of_mem hπ (F.mem_cell_self w) hw

/-- A non-candidate row has a null cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_cell_eq_zero_of_not_mem_cands {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) (F : Frame W)
    {ρ : W → ℝ} (h : ρ ∉ F.cands π) : mass π (F.cell ρ) = 0 := by
  have := (F.mem_cands_iff_mass_cell_pos hπ).not.1 h
  exact le_antisymm (not_lt.1 this) (mass_nonneg hπ _)

/-! ## Consequences of introspection at candidates -/

/-- Under introspection a candidate row vanishes off its own cell.
Source: none: infrastructure (radical S1 INT, used in Theorem I4.1 (ii), (iii), (v))
Kind: L
Fidelity: n/a -/
theorem CandsIntrospective.zero_of_ne {π : W → ℝ} {F : Frame W} (hINT : CandsIntrospective π F)
    {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) {v : W} (hv : F.P v ≠ ρ) : ρ v = 0 :=
  eq_zero_of_mass_eq_one (F.mem_stdSimplex_of_mem_cands hρ) (hINT ρ hρ) (by simpa using hv)

/-- Under introspection a candidate's expectation depends only on values on its own cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CandsIntrospective.E_congr {π : W → ℝ} {F : Frame W} (hINT : CandsIntrospective π F)
    {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) {Y Z : W → ℝ} (h : ∀ v, F.P v = ρ → Y v = Z v) :
    E ρ Y = E ρ Z := by
  unfold E
  apply sum_congr rfl
  intro v _
  by_cases hv : F.P v = ρ
  · rw [h v hv]
  · rw [hINT.zero_of_ne hρ hv]; ring

/-- Under introspection a candidate's expectation of a variable constant on its cell is that
constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CandsIntrospective.E_of_const_on_cell {π : W → ℝ} {F : Frame W}
    (hINT : CandsIntrospective π F) {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) {Y : W → ℝ} {a : ℝ}
    (h : ∀ v, F.P v = ρ → Y v = a) : E ρ Y = a := by
  rw [hINT.E_congr hρ (Z := fun _ => a) (fun v hv => h v hv)]
  exact E_const (F.mem_stdSimplex_of_mem_cands hρ) a

/-! ## The one consequence of Reflection every collapse step uses -/

/-- Under Reflection, on any cell `∑_{P = ρ} π w · X w = π(P = ρ) · E_ρ(X)` (for a non-candidate
both sides vanish).
Source: none: infrastructure (radical Theorem I4.1 (i): "condition on the state")
Kind: L
Fidelity: n/a -/
theorem reflects_cell_sum {π : W → ℝ} {F : Frame W} (hπ : ∀ w, 0 ≤ π w) (h : Reflects π F)
    (ρ X : W → ℝ) : ∑ w ∈ F.cell ρ, π w * X w = mass π (F.cell ρ) * E ρ X := by
  by_cases hρ : ρ ∈ F.cands π
  · rw [sum_eq_sum_mul_ind]
    unfold E
    rw [mul_sum]
    apply sum_congr rfl
    intro w _
    have := h ρ hρ w
    calc π w * X w * ind (F.cell ρ) w = (π w * ind (F.cell ρ) w) * X w := by ring
      _ = mass π (F.cell ρ) * ρ w * X w := by rw [this]
      _ = mass π (F.cell ρ) * (ρ w * X w) := by ring
  · have hm := mass_cell_eq_zero_of_not_mem_cands hπ F hρ
    rw [hm, zero_mul]
    apply sum_eq_zero
    intro w hw
    rw [eq_zero_of_mass_eq_zero hπ hm hw, zero_mul]

/-- Frames with the same rows are equal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem frame_ext {F G : Frame W} (h : ∀ w, F.P w = G.P w) : F = G := by
  cases F; cases G
  simp only [Frame.mk.injEq]
  funext w; exact h w

end

end Cleanroom.Corrigibility.CorrReflectFrames
